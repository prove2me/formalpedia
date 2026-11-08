-- Prove2me | solution 1 for DemandResponse.FirstBest.eqA3_lagrangian_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T07:43:59.312205+00:00
-- url     : https://prove2.me/submissions/d9ceb516-2a8c-467f-805c-6e372f09af4c

import Mathlib
import Definitions.Def_DemandResponse_FirstBest_Model

open MeasureTheory DemandResponse.FirstBest

namespace DRFBeqA3

variable {N d : ℕ}

lemma measurable_X (P : Params N d) (t : Time P) : Measurable (X P t) := by
  intro s hs
  exact (le_iSup (fun t : Time P => MeasurableSpace.comap (X P t)
    (inferInstance : MeasurableSpace ℝ)) t) _ ⟨s, hs, rfl⟩

lemma continuous_Xr (P : Params N d) (ω : Path P) : Continuous fun s => Xr P s ω := by
  unfold Xr X
  exact (ContinuousMap.continuous _).comp continuous_projIcc

lemma measurable_Xr (P : Params N d) (s : ℝ) : Measurable (Xr P s) :=
  measurable_X P _

lemma measurable_intX (P : Params N d) (c : ℝ) :
    Measurable fun ω : Path P => ∫ s in (0 : ℝ)..P.T, c * Xr P s ω := by
  have hj : Measurable (Function.uncurry fun (s : ℝ) (ω : Path P) => c * Xr P s ω) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => continuous_const.mul (continuous_Xr P ω))
      (fun s => (measurable_Xr P s).const_mul c)
  have hj' : StronglyMeasurable (fun q : Path P × ℝ => c * Xr P q.2 q.1) :=
    (hj.comp measurable_swap).stronglyMeasurable
  have := hj'.integral_prod_right' (ν := volume.restrict (Set.Ioc 0 P.T))
  simp_rw [intervalIntegral.integral_of_le P.hT.le]
  exact this.measurable

/-- measurability of a control in time, for fixed ω -/
lemma measurable_αr (P : Params N d) (ν : Control P) (ω : Path P) :
    Measurable fun s => ν.αr s ω := by
  have h := (ν.α_prog (tT P)).measurable
  let g : ℝ → Set.Iic (tT P) × Path P := fun s =>
    (⟨Set.projIcc 0 P.T P.hT.le s,
      Set.mem_Iic.mpr (Subtype.coe_le_coe.mp (Set.projIcc 0 P.T P.hT.le s).2.2)⟩, ω)
  have hg : @Measurable ℝ _ _ (MeasurableSpace.prod Subtype.instMeasurableSpace
      (filt P (tT P))) g := by
    apply Measurable.prod
    · apply Measurable.subtype_mk
      exact continuous_projIcc.measurable
    · exact measurable_const
  exact h.comp hg

lemma measurable_βr (P : Params N d) (ν : Control P) (ω : Path P) :
    Measurable fun s => ν.βr s ω := by
  have h := (ν.β_prog (tT P)).measurable
  let g : ℝ → Set.Iic (tT P) × Path P := fun s =>
    (⟨Set.projIcc 0 P.T P.hT.le s,
      Set.mem_Iic.mpr (Subtype.coe_le_coe.mp (Set.projIcc 0 P.T P.hT.le s).2.2)⟩, ω)
  have hg : @Measurable ℝ _ _ (MeasurableSpace.prod Subtype.instMeasurableSpace
      (filt P (tT P))) g := by
    apply Measurable.prod
    · apply Measurable.subtype_mk
      exact continuous_projIcc.measurable
    · exact measurable_const
  exact h.comp hg

lemma cost_nonneg_le (P : Params N d) (a : Fin N → ℝ) (b : Fin d → ℝ) (ha : a ∈ effortA P)
    (hb : b ∈ effortB P) :
    0 ≤ cost P a b ∧ cost P a b ≤ (1 / 2) * ∑ i, (P.μ i * P.Amax) ^ 2 / P.μ i +
      (1 / 2) * ∑ j, P.σ j ^ 2 / P.lam j * (P.ε⁻¹ - 1) := by
  unfold cost c1 c2
  have hε := P.hε
  have h1 : ∀ i, 0 ≤ a i ^ 2 / P.μ i := fun i => div_nonneg (sq_nonneg _) (P.hμ i).le
  have h2 : ∀ i, a i ^ 2 / P.μ i ≤ (P.μ i * P.Amax) ^ 2 / P.μ i := by
    intro i
    apply div_le_div_of_nonneg_right _ (P.hμ i).le
    exact pow_le_pow_left₀ (ha i).1 (ha i).2 2
  have hbpos : ∀ j, 0 < b j := fun j => lt_of_lt_of_le hε (hb j).1
  have h3 : ∀ j, 0 ≤ P.σ j ^ 2 / P.lam j * ((b j)⁻¹ - 1) := by
    intro j
    apply mul_nonneg (div_nonneg (sq_nonneg _) (P.hlam j).le)
    rw [sub_nonneg]
    exact one_le_inv₀ (hbpos j) |>.mpr (hb j).2
  have h4 : ∀ j, P.σ j ^ 2 / P.lam j * ((b j)⁻¹ - 1) ≤ P.σ j ^ 2 / P.lam j * (P.ε⁻¹ - 1) := by
    intro j
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (sq_nonneg _) (P.hlam j).le)
    have := inv_anti₀ hε (hb j).1
    linarith
  have s1 := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => h1 i)
  have s2 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h2 i)
  have s3 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => h3 j)
  have s4 := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h4 j)
  constructor <;> nlinarith

lemma measurable_cost (P : Params N d) :
    Measurable fun x : (Fin N → ℝ) × (Fin d → ℝ) => cost P x.1 x.2 := by
  unfold cost c1 c2
  fun_prop

lemma cost_intervalIntegrable (P : Params N d) (ν : Control P) (ω : Path P) :
    IntervalIntegrable (fun s => cost P (ν.αr s ω) (ν.βr s ω)) volume 0 P.T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le P.hT.le]
  have hα := measurable_αr P ν ω
  have hβ := measurable_βr P ν ω
  have hm : Measurable fun s => cost P (ν.αr s ω) (ν.βr s ω) := by
    have hα' : ∀ i, Measurable fun s => ν.αr s ω i := fun i => (measurable_pi_apply i).comp hα
    have hβ' : ∀ j, Measurable fun s => ν.βr s ω j := fun j => (measurable_pi_apply j).comp hβ
    unfold cost c1 c2
    fun_prop
  refine Measure.integrableOn_of_bounded (M := (1 / 2) * ∑ i, (P.μ i * P.Amax) ^ 2 / P.μ i +
      (1 / 2) * ∑ j, P.σ j ^ 2 / P.lam j * (P.ε⁻¹ - 1)) measure_Ioc_lt_top.ne
    hm.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  have := cost_nonneg_le P (ν.αr s ω) (ν.βr s ω) (ν.α_mem (Set.projIcc 0 P.T P.hT.le s) ω)
    (ν.β_mem (Set.projIcc 0 P.T P.hT.le s) ω)
  rw [Real.norm_eq_abs, abs_of_nonneg this.1]
  exact this.2

end DRFBeqA3

open DRFBeqA3 in
theorem solution {N d : ℕ} (P : Params N d) (ξ : Path P → ℝ)
    (ν : Control P) (Q : Measure (Path P)) (hξ : IsContract P ξ) (hQ : Admissible P ν Q)
    (hPC : (P.R₀ : EReal) ≤ JA P ξ ν Q) (w : ℝ) (hw : w < 0)
    (hCw : -(((∫⁻ ω, ENNReal.ofReal (Real.exp (-rho P *
      ((∫ s in (0 : ℝ)..P.T, (delta P * Xr P s ω - cost P (ν.αr s ω) (ν.βr s ω))) -
        P.h / 2 * qvInt P ν P.T ω))) ∂Q) : ENNReal) : EReal) ≤ (w : EReal)) :
    JP P ξ ν Q ≤ ((P.R₀ * (w / P.R₀) ^ (1 + P.p / P.r) : ℝ) : EReal) := by
  have hr := P.hr
  have hp := P.hp
  have hR := P.hR₀
  -- the three path functionals
  set K : Path P → ℝ := fun ω =>
    ∫ s in (0 : ℝ)..P.T, (P.κ * Xr P s ω - cost P (ν.αr s ω) (ν.βr s ω)) with hK
  set G : Path P → ℝ := fun ω => ∫ s in (0 : ℝ)..P.T, P.θ * Xr P s ω with hG
  set q : Path P → ℝ := fun ω => qvInt P ν P.T ω with hq
  have hD : ∀ ω, (∫ s in (0 : ℝ)..P.T, (delta P * Xr P s ω - cost P (ν.αr s ω) (ν.βr s ω)))
      = K ω - G ω := by
    intro ω
    have i1 : IntervalIntegrable (fun s => P.κ * Xr P s ω - cost P (ν.αr s ω) (ν.βr s ω))
        volume 0 P.T :=
      ((continuous_const.mul (continuous_Xr P ω)).intervalIntegrable _ _).sub
        (cost_intervalIntegrable P ν ω)
    have i2 : IntervalIntegrable (fun s => P.θ * Xr P s ω) volume 0 P.T :=
      (continuous_const.mul (continuous_Xr P ω)).intervalIntegrable _ _
    simp only [hK, hG]
    rw [← intervalIntegral.integral_sub i1 i2]
    congr 1
    ext s
    unfold delta
    ring
  -- measurability of the producer's integrand
  have hξm : Measurable ξ := hξ.1.mono ((filt P).le _) le_rfl
  have hGm : Measurable G := measurable_intX P P.θ
  have hqm : Measurable q := by
    have h1 : Measurable fun ω => X P (tT P) ω - P.X₀ + driftInt P ν P.T ω :=
      (hQ.mart_drift.1 (tT P)).measurable.mono ((filt P).le _) le_rfl
    have h2 : Measurable fun ω =>
        (X P (tT P) ω - P.X₀ + driftInt P ν P.T ω) ^ 2 - qvInt P ν P.T ω :=
      (hQ.mart_qv.1 (tT P)).measurable.mono ((filt P).le _) le_rfl
    have : q = fun ω => (X P (tT P) ω - P.X₀ + driftInt P ν P.T ω) ^ 2 -
        ((X P (tT P) ω - P.X₀ + driftInt P ν P.T ω) ^ 2 - qvInt P ν P.T ω) := by
      ext ω; simp only [hq]; ring
    rw [this]
    exact (h1.pow_const 2).sub h2
  -- constants
  set ρ := rho P with hρ
  set wa : ℝ := P.p / (P.r + P.p) with hwa
  set wb : ℝ := P.r / (P.r + P.p) with hwb
  set q₀ : ℝ := w / P.R₀ with hq₀
  have hq₀pos : 0 < q₀ := div_pos_of_neg_of_neg hw hR
  have hwa0 : 0 ≤ wa := by positivity
  have hwb0 : 0 ≤ wb := by positivity
  have hwab : wa + wb = 1 := by rw [hwa, hwb]; field_simp; ring
  set ca : ℝ := wa * q₀ with hca
  set cb : ℝ := wb * q₀ ^ (-(P.p / P.r)) with hcb
  have hca0 : 0 ≤ ca := by positivity
  have hcb0 : 0 ≤ cb := by positivity
  set a : Path P → ℝ := fun ω => Real.exp (-P.r * (ξ ω + K ω)) with ha
  set b : Path P → ℝ := fun ω => Real.exp (-P.p * (-ξ ω - G ω - P.h / 2 * q ω)) with hb
  -- pointwise weighted AM-GM (the pointwise maximisation in (A.3)-(A.4))
  have hpt : ∀ ω, Real.exp (-ρ * ((K ω - G ω) - P.h / 2 * q ω)) ≤ ca * a ω + cb * b ω := by
    intro ω
    have hx : q₀ * a ω = Real.exp (Real.log q₀ + -P.r * (ξ ω + K ω)) := by
      rw [Real.exp_add, Real.exp_log hq₀pos]
    have hy : q₀ ^ (-(P.p / P.r)) * b ω =
        Real.exp (Real.log q₀ * (-(P.p / P.r)) + -P.p * (-ξ ω - G ω - P.h / 2 * q ω)) := by
      rw [Real.exp_add, Real.rpow_def_of_pos hq₀pos]
    have hgm := Real.geom_mean_le_arith_mean2_weighted hwa0 hwb0
      (Real.exp_pos (Real.log q₀ + -P.r * (ξ ω + K ω))).le
      (Real.exp_pos (Real.log q₀ * (-(P.p / P.r)) + -P.p * (-ξ ω - G ω - P.h / 2 * q ω))).le
      hwab
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← hx, ← hy] at hgm
    have he : Real.exp (-ρ * ((K ω - G ω) - P.h / 2 * q ω)) =
        Real.exp ((Real.log q₀ + -P.r * (ξ ω + K ω)) * wa +
          (Real.log q₀ * (-(P.p / P.r)) + -P.p * (-ξ ω - G ω - P.h / 2 * q ω)) * wb) := by
      congr 1
      rw [hρ, hwa, hwb]
      unfold rho
      field_simp
      ring
    rw [he]
    calc _ ≤ wa * (q₀ * a ω) + wb * (q₀ ^ (-(P.p / P.r)) * b ω) := hgm
      _ = ca * a ω + cb * b ω := by rw [hca, hcb]; ring
  -- integrate
  set A := ∫⁻ ω, ENNReal.ofReal (a ω) ∂Q with hA
  set B := ∫⁻ ω, ENNReal.ofReal (b ω) ∂Q with hB
  set C := ∫⁻ ω, ENNReal.ofReal (Real.exp (-ρ *
      ((∫ s in (0 : ℝ)..P.T, (delta P * Xr P s ω - cost P (ν.αr s ω) (ν.βr s ω))) -
        P.h / 2 * qvInt P ν P.T ω))) ∂Q with hC
  have hbm : Measurable fun ω => ENNReal.ofReal (cb) * ENNReal.ofReal (b ω) := by
    apply Measurable.const_mul
    apply ENNReal.measurable_ofReal.comp
    apply Real.measurable_exp.comp
    exact ((hξm.neg.sub hGm).sub (hqm.const_mul _)).const_mul _
  have hCle : C ≤ ENNReal.ofReal ca * A + ENNReal.ofReal cb * B := by
    calc C ≤ ∫⁻ ω, (ENNReal.ofReal ca * ENNReal.ofReal (a ω) +
          ENNReal.ofReal cb * ENNReal.ofReal (b ω)) ∂Q := by
          apply lintegral_mono
          intro ω
          dsimp only
          rw [hD ω, ← ENNReal.ofReal_mul hca0, ← ENNReal.ofReal_mul hcb0,
            ← ENNReal.ofReal_add (mul_nonneg hca0 (Real.exp_pos _).le)
              (mul_nonneg hcb0 (Real.exp_pos _).le)]
          exact ENNReal.ofReal_le_ofReal (hpt ω)
      _ = ENNReal.ofReal ca * A + ENNReal.ofReal cb * B := by
          rw [lintegral_add_right' _ hbm.aemeasurable,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- participation constraint: A ≤ -R₀
  have hJA : JA P ξ ν Q = -(A : EReal) := rfl
  have hJP : JP P ξ ν Q = -(B : EReal) := rfl
  rw [hJA] at hPC
  have hA1 : (A : EReal) ≤ ((-P.R₀ : ℝ) : EReal) := by
    rw [EReal.coe_neg]; exact EReal.le_neg_of_le_neg hPC
  have hAtop : A ≠ ⊤ := by
    intro h; rw [h] at hA1; simp at hA1
  rw [← EReal.coe_ennreal_toReal hAtop, EReal.coe_le_coe_iff] at hA1
  rw [hJP]
  by_cases hBtop : B = ⊤
  · rw [hBtop]; simp
  have hCtop : C ≠ ⊤ := by
    intro h
    rw [h, top_le_iff] at hCle
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAtop,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBtop⟩ hCle
  have hC1 : -w ≤ C.toReal := by
    have := EReal.neg_le_of_neg_le hCw
    rw [← EReal.coe_ennreal_toReal hCtop, ← EReal.coe_neg, EReal.coe_le_coe_iff] at this
    exact this
  have hC2 : C.toReal ≤ ca * A.toReal + cb * B.toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAtop,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBtop⟩) hCle
    rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAtop)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBtop), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hca0, ENNReal.toReal_ofReal hcb0] at this
  rw [← EReal.coe_ennreal_toReal hBtop, ← EReal.coe_neg, EReal.coe_le_coe_iff]
  -- real algebra
  have hwq : w = q₀ * P.R₀ := by rw [hq₀, div_mul_cancel₀ w hR.ne]
  set B' := B.toReal
  set A' := A.toReal
  have hpow_pos : 0 < q₀ ^ (P.p / P.r) := Real.rpow_pos_of_pos hq₀pos _
  have hinv : q₀ ^ (P.p / P.r) * q₀ ^ (-(P.p / P.r)) = 1 := by
    rw [← Real.rpow_add hq₀pos]; simp
  have hpow : q₀ ^ (1 + P.p / P.r) = q₀ * q₀ ^ (P.p / P.r) := by
    rw [Real.rpow_add hq₀pos, Real.rpow_one]
  have hwbpos : 0 < wb := by positivity
  -- q₀ (-R₀) ≤ q₀^{-p/r} B'
  have key : wb * (q₀ * (-P.R₀)) ≤ wb * (q₀ ^ (-(P.p / P.r)) * B') := by
    have h3 : ca * A' ≤ ca * (-P.R₀) := mul_le_mul_of_nonneg_left hA1 hca0
    rw [hca] at h3 hC2
    rw [hcb] at hC2
    have e1 : wa * q₀ * -P.R₀ = q₀ * (-P.R₀) - wb * (q₀ * (-P.R₀)) := by
      have : wa = 1 - wb := by linarith
      rw [this]; ring
    have e2 : wb * q₀ ^ (-(P.p / P.r)) * B' = wb * (q₀ ^ (-(P.p / P.r)) * B') := by ring
    have e3 : -w = q₀ * (-P.R₀) := by rw [hwq]; ring
    linarith
  have key2 : q₀ * (-P.R₀) ≤ q₀ ^ (-(P.p / P.r)) * B' := le_of_mul_le_mul_left key hwbpos
  have key3 : q₀ ^ (P.p / P.r) * (q₀ * (-P.R₀)) ≤ B' := by
    have := mul_le_mul_of_nonneg_left key2 hpow_pos.le
    calc _ ≤ q₀ ^ (P.p / P.r) * (q₀ ^ (-(P.p / P.r)) * B') := this
      _ = B' := by rw [← mul_assoc, hinv, one_mul]
  rw [hpow]
  nlinarith
