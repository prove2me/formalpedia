-- Prove2me | solution 1 for DemandResponse.FirstBest.eqA4_optimal_contract_attains
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T07:56:52.447916+00:00
-- url     : https://prove2.me/submissions/a5a4d5c4-4a33-43e7-97bb-9f0bf7aa0d7e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DemandResponse_FirstBest_Model
import Theorems.Thm_DemandResponse_FirstBest_admissible_exp_moment_absX

open MeasureTheory DemandResponse.FirstBest

namespace DRFBeqA4

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


lemma filt_T_eq (P : Params N d) : filt P (tT P) = instMeasurableSpacePath P := by
  apply le_antisymm ((filt P).le _)
  apply iSup_le
  intro s
  exact le_iSup₂_of_le (f := fun (s : Time P) (_ : s ≤ tT P) =>
    MeasurableSpace.comap (X P s) (inferInstance : MeasurableSpace ℝ)) s
    (Subtype.coe_le_coe.mp s.2.2) le_rfl

lemma measurable_intCost (P : Params N d) (ν : Control P) :
    Measurable fun ω : Path P => ∫ s in (0 : ℝ)..P.T, cost P (ν.αr s ω) (ν.βr s ω) := by
  have hα := (ν.α_prog (tT P)).measurable
  have hβ := (ν.β_prog (tT P)).measurable
  let g : Path P × ℝ → Set.Iic (tT P) × Path P := fun x =>
    (⟨Set.projIcc 0 P.T P.hT.le x.2,
      Set.mem_Iic.mpr (Subtype.coe_le_coe.mp (Set.projIcc 0 P.T P.hT.le x.2).2.2)⟩, x.1)
  have hg : @Measurable (Path P × ℝ) _ _ (MeasurableSpace.prod Subtype.instMeasurableSpace
      (filt P (tT P))) g := by
    apply Measurable.prod
    · apply Measurable.subtype_mk
      exact continuous_projIcc.measurable.comp measurable_snd
    · exact measurable_fst.mono le_rfl ((filt P).le _)
  have hαj : Measurable fun x : Path P × ℝ => ν.αr x.2 x.1 := hα.comp hg
  have hβj : Measurable fun x : Path P × ℝ => ν.βr x.2 x.1 := hβ.comp hg
  have hj : Measurable fun x : Path P × ℝ => cost P (ν.αr x.2 x.1) (ν.βr x.2 x.1) := by
    have hα' : ∀ i, Measurable fun x : Path P × ℝ => ν.αr x.2 x.1 i :=
      fun i => (measurable_pi_apply i).comp hαj
    have hβ' : ∀ j, Measurable fun x : Path P × ℝ => ν.βr x.2 x.1 j :=
      fun j => (measurable_pi_apply j).comp hβj
    unfold cost c1 c2
    fun_prop
  have := hj.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioc 0 P.T))
  simp_rw [intervalIntegral.integral_of_le P.hT.le]
  exact this.measurable

lemma qv_bounds (P : Params N d) (ν : Control P) (ω : Path P) :
    0 ≤ qvInt P ν P.T ω ∧ qvInt P ν P.T ω ≤ P.T * ∑ j, P.σ j ^ 2 := by
  have hβ := measurable_βr P ν ω
  have hβ' : ∀ j, Measurable fun s => ν.βr s ω j := fun j => (measurable_pi_apply j).comp hβ
  have hm : Measurable fun s => sigSq P (ν.βr s ω) := by unfold sigSq; fun_prop
  have hb : ∀ s, 0 ≤ sigSq P (ν.βr s ω) ∧ sigSq P (ν.βr s ω) ≤ ∑ j, P.σ j ^ 2 := by
    intro s
    have hmem := ν.β_mem (Set.projIcc 0 P.T P.hT.le s) ω
    unfold sigSq
    constructor
    · exact Finset.sum_nonneg fun j _ =>
        mul_nonneg (sq_nonneg _) (le_trans P.hε.le (hmem j).1)
    · exact Finset.sum_le_sum fun j _ => by
        have := (hmem j).2
        have := sq_nonneg (P.σ j)
        show P.σ j ^ 2 * ν.β (Set.projIcc 0 P.T P.hT.le s) ω j ≤ P.σ j ^ 2
        nlinarith
  have hint : IntervalIntegrable (fun s => sigSq P (ν.βr s ω)) volume 0 P.T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le P.hT.le]
    refine Measure.integrableOn_of_bounded (M := ∑ j, P.σ j ^ 2) measure_Ioc_lt_top.ne
      hm.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hb s).1]
    exact (hb s).2
  unfold qvInt
  constructor
  · exact intervalIntegral.integral_nonneg P.hT.le fun s _ => (hb s).1
  · calc (∫ s in (0 : ℝ)..P.T, sigSq P (ν.βr s ω)) ≤ ∫ s in (0 : ℝ)..P.T, ∑ j, P.σ j ^ 2 :=
          intervalIntegral.integral_mono_on P.hT.le hint intervalIntegrable_const
            fun s _ => (hb s).2
      _ = P.T * ∑ j, P.σ j ^ 2 := by simp

end DRFBeqA4

open DRFBeqA4 in
theorem solution {N d : ℕ} (P : Params N d)
    (ν : Control P) (Q : Measure (Path P)) (hQ : Admissible P ν Q) (w : ℝ) (hw : w < 0)
    (hCw : -(((∫⁻ ω, ENNReal.ofReal (Real.exp (-rho P *
      ((∫ s in (0 : ℝ)..P.T, (delta P * Xr P s ω - cost P (ν.αr s ω) (ν.βr s ω))) -
        P.h / 2 * qvInt P ν P.T ω))) ∂Q) : ENNReal) : EReal) = (w : EReal)) :
    ∃ ξ : Path P → ℝ, IsContract P ξ ∧ (P.R₀ : EReal) ≤ JA P ξ ν Q ∧
      JP P ξ ν Q = ((P.R₀ * (w / P.R₀) ^ (1 + P.p / P.r) : ℝ) : EReal) := by
  have hr := P.hr
  have hp := P.hp
  have hR := P.hR₀
  set q₀ : ℝ := w / P.R₀ with hq₀
  have hq₀pos : 0 < q₀ := div_pos_of_neg_of_neg hw hR
  have hwq : w = q₀ * P.R₀ := by rw [hq₀, div_mul_cancel₀ w hR.ne]
  set e : Path P → ℝ := fun ω => Real.exp (-rho P *
      ((∫ s in (0 : ℝ)..P.T, (delta P * Xr P s ω - cost P (ν.αr s ω) (ν.βr s ω))) -
        P.h / 2 * qvInt P ν P.T ω)) with he
  set K : Path P → ℝ := fun ω =>
    ∫ s in (0 : ℝ)..P.T, (P.κ * Xr P s ω - cost P (ν.αr s ω) (ν.βr s ω)) with hK
  set G : Path P → ℝ := fun ω => ∫ s in (0 : ℝ)..P.T, P.θ * Xr P s ω with hG
  set qv : Path P → ℝ := fun ω => qvInt P ν P.T ω with hqv
  have hKsplit : ∀ ω, K ω = (∫ s in (0 : ℝ)..P.T, P.κ * Xr P s ω) -
      ∫ s in (0 : ℝ)..P.T, cost P (ν.αr s ω) (ν.βr s ω) := by
    intro ω
    exact intervalIntegral.integral_sub
      ((continuous_const.mul (continuous_Xr P ω)).intervalIntegrable _ _)
      (cost_intervalIntegrable P ν ω)
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
  set ξ : Path P → ℝ := fun ω =>
    (1 / P.r) * Real.log q₀ - (P.r * K ω + P.p * (G ω + P.h / 2 * qv ω)) / (P.r + P.p) with hξ
  have hrho : rho P = P.r * P.p / (P.r + P.p) := rfl
  have ha : ∀ ω, Real.exp (-P.r * (ξ ω + K ω)) = q₀⁻¹ * e ω := by
    intro ω
    rw [he]
    dsimp only
    rw [hD ω, ← Real.exp_log (inv_pos.mpr hq₀pos), ← Real.exp_add, Real.log_inv]
    congr 1
    rw [hξ, hrho]
    dsimp only
    field_simp
    ring
  have hb : ∀ ω, Real.exp (-P.p * (-ξ ω - G ω - P.h / 2 * qv ω)) = q₀ ^ (P.p / P.r) * e ω := by
    intro ω
    rw [he]
    dsimp only
    rw [hD ω, Real.rpow_def_of_pos hq₀pos, ← Real.exp_add]
    congr 1
    rw [hξ, hrho]
    dsimp only
    field_simp
    ring
  -- the value of the reduced criterion
  set C := ∫⁻ ω, ENNReal.ofReal (e ω) ∂Q with hC
  have hC' : C = ENNReal.ofReal (-w) := by
    have h1 : (C : EReal) = ((-w : ℝ) : EReal) := by
      rw [EReal.coe_neg, ← hCw, neg_neg]
    have h2 : ((ENNReal.ofReal (-w) : ENNReal) : EReal) = ((-w : ℝ) : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left (by linarith)]
    exact EReal.coe_ennreal_injective (h1.trans h2.symm)
  have hcoe : ∀ x : ℝ, 0 ≤ x → ((ENNReal.ofReal x : ENNReal) : EReal) = (x : EReal) := by
    intro x hx
    rw [EReal.coe_ennreal_ofReal, max_eq_left hx]
  refine ⟨ξ, ?_, ?_, ?_⟩
  · -- ξ ∈ 𝒞
    have hqm : Measurable qv := by
      have h1 : Measurable fun ω => X P (tT P) ω - P.X₀ + driftInt P ν P.T ω :=
        (hQ.mart_drift.1 (tT P)).measurable.mono ((filt P).le _) le_rfl
      have h2 : Measurable fun ω =>
          (X P (tT P) ω - P.X₀ + driftInt P ν P.T ω) ^ 2 - qvInt P ν P.T ω :=
        (hQ.mart_qv.1 (tT P)).measurable.mono ((filt P).le _) le_rfl
      have : qv = fun ω => (X P (tT P) ω - P.X₀ + driftInt P ν P.T ω) ^ 2 -
          ((X P (tT P) ω - P.X₀ + driftInt P ν P.T ω) ^ 2 - qvInt P ν P.T ω) := by
        ext ω; simp only [hqv]; ring
      rw [this]
      exact (h1.pow_const 2).sub h2
    have hKm : Measurable K := by
      have : K = fun ω => (∫ s in (0 : ℝ)..P.T, P.κ * Xr P s ω) -
          ∫ s in (0 : ℝ)..P.T, cost P (ν.αr s ω) (ν.βr s ω) := funext hKsplit
      rw [this]
      exact (measurable_intX P P.κ).sub (measurable_intCost P ν)
    have hGm : Measurable G := measurable_intX P P.θ
    have hξm : Measurable ξ := by
      rw [hξ]
      exact measurable_const.sub
        (((hKm.const_mul _).add ((hGm.add (hqm.const_mul _)).const_mul _)).div_const _)
    -- pointwise bound of c ξ by a multiple of ∫|X|
    set Mc : ℝ := (1 / 2) * ∑ i, (P.μ i * P.Amax) ^ 2 / P.μ i +
      (1 / 2) * ∑ j, P.σ j ^ 2 / P.lam j * (P.ε⁻¹ - 1) with hMc
    set Ssig : ℝ := ∑ j, P.σ j ^ 2 with hSsig
    set IX : Path P → ℝ := fun ω => ∫ s in (0 : ℝ)..P.T, |Xr P s ω| with hIX
    have hIXnn : ∀ ω, 0 ≤ IX ω := fun ω =>
      intervalIntegral.integral_nonneg P.hT.le fun s _ => abs_nonneg _
    have hKb : ∀ ω, |K ω| ≤ |P.κ| * IX ω + P.T * Mc := by
      intro ω
      have i1 : IntervalIntegrable (fun s => P.κ * Xr P s ω - cost P (ν.αr s ω) (ν.βr s ω))
          volume 0 P.T :=
        ((continuous_const.mul (continuous_Xr P ω)).intervalIntegrable _ _).sub
          (cost_intervalIntegrable P ν ω)
      have hcX : Continuous fun s => |Xr P s ω| := (continuous_Xr P ω).abs
      have hc1 : Continuous fun s => |P.κ| * |Xr P s ω| := continuous_const.mul hcX
      have hc2 : Continuous fun s => |P.κ| * |Xr P s ω| + Mc := hc1.add continuous_const
      calc |K ω| ≤ ∫ s in (0 : ℝ)..P.T, |P.κ * Xr P s ω - cost P (ν.αr s ω) (ν.βr s ω)| :=
            intervalIntegral.abs_integral_le_integral_abs P.hT.le
        _ ≤ ∫ s in (0 : ℝ)..P.T, (|P.κ| * |Xr P s ω| + Mc) := by
            apply intervalIntegral.integral_mono_on P.hT.le i1.abs (hc2.intervalIntegrable _ _)
            intro s _
            have hc := cost_nonneg_le P (ν.αr s ω) (ν.βr s ω)
              (ν.α_mem (Set.projIcc 0 P.T P.hT.le s) ω) (ν.β_mem (Set.projIcc 0 P.T P.hT.le s) ω)
            calc |P.κ * Xr P s ω - cost P (ν.αr s ω) (ν.βr s ω)|
                ≤ |P.κ * Xr P s ω| + |cost P (ν.αr s ω) (ν.βr s ω)| := abs_sub _ _
              _ = |P.κ| * |Xr P s ω| + cost P (ν.αr s ω) (ν.βr s ω) := by
                  rw [abs_mul, abs_of_nonneg hc.1]
              _ ≤ |P.κ| * |Xr P s ω| + Mc := by linarith [hc.2]
        _ = |P.κ| * IX ω + P.T * Mc := by
            rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _)
              intervalIntegrable_const, intervalIntegral.integral_const_mul]
            simp [hIX]
    have hGb : ∀ ω, |G ω| ≤ |P.θ| * IX ω := by
      intro ω
      calc |G ω| ≤ ∫ s in (0 : ℝ)..P.T, |P.θ * Xr P s ω| :=
            intervalIntegral.abs_integral_le_integral_abs P.hT.le
        _ = |P.θ| * IX ω := by
            simp_rw [abs_mul]
            rw [intervalIntegral.integral_const_mul]
    have hmom : ∀ c : ℝ, (⨆ (ν' : Control P) (Q' : Measure (Path P)) (_ : Admissible P ν' Q'),
        ∫⁻ ω, ENNReal.ofReal (Real.exp (c * ξ ω)) ∂Q') < ⊤ := by
      intro c
      set L : ℝ := |c| * ((P.r * |P.κ| + P.p * |P.θ|) / (P.r + P.p)) with hL
      set A0 : ℝ := |c| * (|Real.log q₀| / P.r +
        (P.r * (P.T * Mc) + P.p * (P.h / 2 * (P.T * Ssig))) / (P.r + P.p)) with hA0
      have hpt : ∀ ω, c * ξ ω ≤ A0 + L * IX ω := by
        intro ω
        have hq := qv_bounds P ν ω
        have hrp : 0 < P.r + P.p := by linarith
        have h1 : |ξ ω| ≤ |Real.log q₀| / P.r +
            (P.r * |K ω| + P.p * (|G ω| + P.h / 2 * qv ω)) / (P.r + P.p) := by
          rw [hξ]
          dsimp only
          calc |1 / P.r * Real.log q₀ - (P.r * K ω + P.p * (G ω + P.h / 2 * qv ω)) / (P.r + P.p)|
              ≤ |1 / P.r * Real.log q₀| +
                |(P.r * K ω + P.p * (G ω + P.h / 2 * qv ω)) / (P.r + P.p)| := abs_sub _ _
            _ ≤ |Real.log q₀| / P.r +
                (P.r * |K ω| + P.p * (|G ω| + P.h / 2 * qv ω)) / (P.r + P.p) := by
                gcongr
                · rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / P.r)]
                  rw [div_mul_eq_mul_div, one_mul]
                · rw [abs_div, abs_of_pos hrp]
                  gcongr
                  calc |P.r * K ω + P.p * (G ω + P.h / 2 * qv ω)|
                      ≤ |P.r * K ω| + |P.p * (G ω + P.h / 2 * qv ω)| := abs_add_le _ _
                    _ ≤ P.r * |K ω| + P.p * (|G ω| + P.h / 2 * qv ω) := by
                        rw [abs_mul, abs_mul, abs_of_pos hr, abs_of_pos hp]
                        gcongr
                        calc |G ω + P.h / 2 * qv ω| ≤ |G ω| + |P.h / 2 * qv ω| :=
                              abs_add_le _ _
                          _ = |G ω| + P.h / 2 * qv ω := by
                              rw [abs_of_nonneg (mul_nonneg (by linarith [P.hh]) hq.1)]
        have h2 : |ξ ω| ≤ |Real.log q₀| / P.r +
            (P.r * (|P.κ| * IX ω + P.T * Mc) + P.p * (|P.θ| * IX ω + P.h / 2 * (P.T * Ssig)))
              / (P.r + P.p) := by
          refine h1.trans ?_
          gcongr
          · exact hKb ω
          · exact hGb ω
          · linarith [P.hh]
          · exact hq.2
        calc c * ξ ω ≤ |c| * |ξ ω| := by rw [← abs_mul]; exact le_abs_self _
          _ ≤ |c| * (|Real.log q₀| / P.r +
            (P.r * (|P.κ| * IX ω + P.T * Mc) + P.p * (|P.θ| * IX ω + P.h / 2 * (P.T * Ssig)))
              / (P.r + P.p)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg c)
          _ = A0 + L * IX ω := by rw [hA0, hL]; field_simp; ring
      have hS := admissible_exp_moment_absX P L
      refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := Real.exp A0)) hS)
      refine iSup_le fun ν' => iSup_le fun Q' => iSup_le fun hQ' => ?_
      calc ∫⁻ ω, ENNReal.ofReal (Real.exp (c * ξ ω)) ∂Q'
          ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp A0) *
              ENNReal.ofReal (Real.exp (L * ∫ s in (0 : ℝ)..P.T, |Xr P s ω|)) ∂Q' := by
            apply lintegral_mono
            intro ω
            dsimp only
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
            exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hpt ω))
        _ = ENNReal.ofReal (Real.exp A0) *
              ∫⁻ ω, ENNReal.ofReal (Real.exp (L * ∫ s in (0 : ℝ)..P.T, |Xr P s ω|)) ∂Q' :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (Real.exp A0) *
              ⨆ (ν : Control P) (Q : Measure (Path P)) (_ : Admissible P ν Q),
                ∫⁻ ω, ENNReal.ofReal (Real.exp (L * ∫ s in (0 : ℝ)..P.T, |Xr P s ω|)) ∂Q := by
            gcongr
            exact le_iSup_of_le ν' (le_iSup_of_le Q' (le_iSup_of_le hQ' le_rfl))
    refine ⟨?_, 2, one_lt_two, ENNReal.add_lt_top.mpr ⟨hmom (-P.r * 2), hmom (P.p * 2)⟩⟩
    rw [filt_T_eq]
    exact hξm
  · -- participation constraint binds: J_A = R₀
    have hJA : JA P ξ ν Q = -((∫⁻ ω, ENNReal.ofReal (Real.exp (-P.r * (ξ ω + K ω))) ∂Q :
        ENNReal) : EReal) := rfl
    rw [hJA]
    simp_rw [ha, ENNReal.ofReal_mul (inv_nonneg.mpr hq₀pos.le)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hC, hC',
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hq₀pos.le), hcoe _ (by
        have : 0 ≤ -w := by linarith
        positivity), ← EReal.coe_neg]
    apply le_of_eq
    congr 1
    rw [hwq]
    field_simp
  · -- producer's value
    have hJP : JP P ξ ν Q = -((∫⁻ ω, ENNReal.ofReal
        (Real.exp (-P.p * (-ξ ω - G ω - P.h / 2 * qv ω))) ∂Q : ENNReal) : EReal) := rfl
    rw [hJP]
    have hpos : 0 ≤ q₀ ^ (P.p / P.r) := (Real.rpow_pos_of_pos hq₀pos _).le
    simp_rw [hb, ENNReal.ofReal_mul hpos]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hC, hC',
      ← ENNReal.ofReal_mul hpos, hcoe _ (by
        have : 0 ≤ -w := by linarith
        positivity), ← EReal.coe_neg]
    congr 1
    rw [Real.rpow_add hq₀pos, Real.rpow_one, hwq]
    ring
