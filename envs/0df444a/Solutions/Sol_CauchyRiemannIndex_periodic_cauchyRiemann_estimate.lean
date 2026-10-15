-- Prove2me | solution 1 for CauchyRiemannIndex.periodic_cauchyRiemann_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T07:43:42.08973+00:00
-- url     : https://prove2.me/submissions/e4b5f291-8e61-4ecf-aba3-ce2c960017c4

import Theorems.Thm_CauchyRiemannIndex_plane_cauchyRiemann_estimate
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- ===== Scratch/CRLocPer.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Set Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-! ### Periodic functions: `L^p` over five periods -/

/-- The horizontal strip `ℝ × [k, k + 1)`. -/
def crpS (k : ℤ) : Set (ℝ × ℝ) := univ ×ˢ Ico (k : ℝ) (k + 1)

lemma crpS_floor {k : ℤ} {x : ℝ × ℝ} (h : x ∈ crpS k) : ⌊x.2⌋ = k :=
  Int.floor_eq_iff.2 ⟨h.2.1, h.2.2⟩

lemma crp_shift (G : ℝ × ℝ → ℝ≥0∞) (hG : ∀ s t, G (s, t + 1) = G (s, t)) (k : ℤ) :
    ∫⁻ x in crpS k, G x = ∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, G x := by
  set e : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.addRight (k : ℝ))
  have he : ∀ x : ℝ × ℝ, e x = (x.1, x.2 + k) := fun x => rfl
  have hGk : ∀ x : ℝ × ℝ, G (e x) = G x := by
    rintro ⟨s, t⟩
    have hp : Function.Periodic (fun t => G (s, t)) 1 := fun t => hG s t
    have := hp.int_mul k t
    rw [he]
    simpa using this
  have mp : MeasurePreserving e (volume : Measure (ℝ × ℝ)) volume :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (measurePreserving_add_right (volume : Measure ℝ) (k : ℝ))
  have hpre : e ⁻¹' crpS k = univ ×ˢ Ico (0 : ℝ) 1 := by
    ext ⟨s, t⟩
    simp only [crpS, mem_preimage, he, mem_prod, mem_univ, true_and, mem_Ico]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have h := mp.setLIntegral_comp_preimage_emb e.measurableEmbedding G (crpS k)
  rw [hpre] at h
  rw [← h]
  exact setLIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Ico)
    (fun x _ => hGk x)

lemma crp_five (G : ℝ × ℝ → ℝ≥0∞) (hG : ∀ s t, G (s, t + 1) = G (s, t)) :
    ∫⁻ x in univ ×ˢ Ico (-2 : ℝ) 3, G x ≤ 5 * ∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, G x := by
  have hsub : univ ×ˢ Ico (-2 : ℝ) 3 ⊆ ⋃ k ∈ Finset.Icc (-2 : ℤ) 2, crpS k := by
    rintro ⟨s, t⟩ ⟨-, h1, h2⟩
    simp only [mem_iUnion, Finset.mem_Icc, exists_prop]
    refine ⟨⌊t⌋, ⟨?_, ?_⟩, ?_⟩
    · exact Int.le_floor.2 (by push_cast; linarith)
    · have : ⌊t⌋ < 3 := Int.floor_lt.2 (by push_cast; linarith)
      omega
    · exact ⟨mem_univ _, Int.floor_le t, Int.lt_floor_add_one t⟩
  have hd : (↑(Finset.Icc (-2 : ℤ) 2) : Set ℤ).PairwiseDisjoint crpS := by
    intro k _ j _ hkj
    exact Set.disjoint_left.2 fun x hk hj => hkj (by rw [← crpS_floor hk, ← crpS_floor hj])
  have hm : ∀ k ∈ Finset.Icc (-2 : ℤ) 2, MeasurableSet (crpS k) :=
    fun k _ => MeasurableSet.univ.prod measurableSet_Ico
  calc ∫⁻ x in univ ×ˢ Ico (-2 : ℝ) 3, G x
      ≤ ∫⁻ x in ⋃ k ∈ Finset.Icc (-2 : ℤ) 2, crpS k, G x := lintegral_mono_set hsub
    _ = ∑ k ∈ Finset.Icc (-2 : ℤ) 2, ∫⁻ x in crpS k, G x := lintegral_biUnion_finset hd hm G
    _ = ∑ k ∈ Finset.Icc (-2 : ℤ) 2, ∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, G x :=
        Finset.sum_congr rfl fun k _ => crp_shift G hG k
    _ = 5 * ∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, G x := by
        rw [Finset.sum_const, nsmul_eq_mul]
        congr 1

lemma crp_eLpNorm_le {E : Type*} [NormedAddCommGroup E] (f : ℝ × ℝ → E)
    (hf : ∀ s t, f (s, t + 1) = f (s, t)) (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    eLpNorm f p (volume.restrict (univ ×ˢ Ico (-2 : ℝ) 3)) ≤ 5 * eLpNorm f p cylMeasure := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hpr : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hpt hp
    simpa using this
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  have h5 := crp_five (fun x => ‖f x‖ₑ ^ p.toReal) (fun s t => by simp only [hf])
  have hpos : 0 ≤ 1 / p.toReal := by positivity
  have hle1 : 1 / p.toReal ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hpr
  calc (∫⁻ x in univ ×ˢ Ico (-2 : ℝ) 3, ‖f x‖ₑ ^ p.toReal) ^ (1 / p.toReal)
      ≤ (5 * ∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, ‖f x‖ₑ ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow h5 hpos
    _ = (5 : ℝ≥0∞) ^ (1 / p.toReal) *
          (∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, ‖f x‖ₑ ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.mul_rpow_of_nonneg _ _ hpos
    _ ≤ 5 * (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂cylMeasure) ^ (1 / p.toReal) := by
        gcongr
        · calc (5 : ℝ≥0∞) ^ (1 / p.toReal) ≤ 5 ^ (1 : ℝ) :=
                ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hle1
            _ = 5 := ENNReal.rpow_one _
        · exact le_of_eq rfl

/-! ### The cut-off in `t` -/

/-- A bump in `t`, equal to `1` on `[-1/2, 3/2]` and supported in `[-3/2, 5/2]`. -/
def crpBump : ContDiffBump (1 / 2 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- The cut-off function `χ`. -/
def crpχ : ℝ → ℝ := fun t => crpBump t

lemma crpχ_contDiff : ContDiff ℝ ∞ crpχ := crpBump.contDiff

lemma crpχ_one {t : ℝ} (h1 : -1 / 2 ≤ t) (h2 : t ≤ 3 / 2) : crpχ t = 1 := by
  apply crpBump.one_of_mem_closedBall
  have : crpBump.rIn = 1 := rfl
  rw [this, Metric.mem_closedBall, Real.dist_eq, abs_le]
  constructor <;> linarith

lemma crpχ_abs_le (t : ℝ) : |crpχ t| ≤ 1 := by
  show |crpBump t| ≤ 1
  rw [abs_le]; exact ⟨by linarith [crpBump.nonneg (x := t)], crpBump.le_one⟩

lemma crpχ_zero {t : ℝ} (h : t ∉ Ico (-2 : ℝ) 3) : crpχ t = 0 := by
  by_contra hne
  have : t ∈ Function.support crpχ := hne
  have h' : t ∈ Metric.ball (1 / 2 : ℝ) crpBump.rOut := by
    rw [← crpBump.support_eq]; exact this
  have : crpBump.rOut = 2 := rfl
  rw [this, Metric.mem_ball, Real.dist_eq, abs_lt] at h'
  apply h; constructor <;> linarith

lemma crpχ_deriv_zero {t : ℝ} (h : t ∉ Ico (-2 : ℝ) 3) : deriv crpχ t = 0 := by
  by_contra hne
  have h1 : t ∈ tsupport crpχ := support_deriv_subset hne
  have h2 : t ∈ Metric.closedBall (1 / 2 : ℝ) crpBump.rOut := by
    rw [← crpBump.tsupport_eq]; exact h1
  have : crpBump.rOut = 2 := rfl
  rw [this, Metric.mem_closedBall, Real.dist_eq, abs_le] at h2
  apply h; constructor <;> linarith

lemma crpχ_deriv_bound : ∃ M : ℝ≥0, ∀ t, |deriv crpχ t| ≤ M := by
  have hc : Continuous (deriv crpχ) := crpχ_contDiff.continuous_deriv (by simp)
  have hs : HasCompactSupport (deriv crpχ) := crpBump.hasCompactSupport.deriv
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨C.toNNReal, fun t => (hC t).trans (Real.le_coe_toNNReal C)⟩

/-! ### Periodicity of derivatives -/

lemma crp_fderiv_per {u : ℝ × ℝ → Vec n} (hper : ∀ s t, u (s, t + 1) = u (s, t)) (s t : ℝ) :
    fderiv ℝ u (s, t + 1) = fderiv ℝ u (s, t) := by
  have hfun : (fun y : ℝ × ℝ => u (y + ((0 : ℝ), (1 : ℝ)))) = u := by
    funext ⟨a, b⟩
    simp only [Prod.mk_add_mk, add_zero, hper]
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := ((s, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ))
  rw [hfun, Prod.mk_add_mk, add_zero] at h
  exact h.symm

/-! ### The estimate -/

lemma crp_main (n : ℕ) (p : ℝ≥0∞) (hp : 1 < p) (hp' : p ≠ ⊤) :
    ∃ A : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, ContDiff ℝ 1 u → (∀ s t, u (s, t + 1) = u (s, t)) →
      (∃ R : ℝ, ∀ s t, R < |s| → u (s, t) = 0) →
      eLpNorm (partialS u) p cylMeasure + eLpNorm (partialT u) p cylMeasure ≤
        A * eLpNorm (fun x => partialS u x + Matrix.toEuclideanLin (J₀ n) (partialT u x)) p
            cylMeasure + A * eLpNorm u p cylMeasure := by
  obtain ⟨B, hB⟩ := plane_cauchyRiemann_estimate n p hp hp'
  obtain ⟨M, hM⟩ := crpχ_deriv_bound
  set Jc : Vec n →L[ℝ] Vec n := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (J₀ n))
  set N : ℝ≥0 := ‖Jc‖₊
  have hJ : ∀ w : Vec n, ‖Matrix.toEuclideanLin (J₀ n) w‖ ≤ N * ‖w‖ := fun w => Jc.le_opNorm w
  set A : ℝ≥0 := B * 5 * (1 + M * N)
  refine ⟨A, fun u hu hper ⟨R, hR⟩ => ?_⟩
  have hp1 : 1 ≤ p := hp.le
  have hT : MeasurableSet ((univ : Set ℝ) ×ˢ Ico (-2 : ℝ) 3) :=
    MeasurableSet.univ.prod measurableSet_Ico
  -- the cut-off map
  set v : ℝ × ℝ → Vec n := fun x => crpχ x.2 • u x with hv_def
  have hχ1 : ContDiff ℝ 1 crpχ := crpχ_contDiff.of_le (by simp)
  have hvc : ContDiff ℝ 1 v := (hχ1.comp contDiff_snd).smul hu
  have hvd : ∀ x : ℝ × ℝ, HasFDerivAt v
      (crpχ x.2 • fderiv ℝ u x +
        (deriv crpχ x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (u x)) x := by
    intro x
    have hc : HasFDerivAt (fun y : ℝ × ℝ => crpχ y.2)
        (deriv crpχ x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
      ((hχ1.differentiable one_ne_zero x.2).hasDerivAt).comp_hasFDerivAt x (hasFDerivAt_snd)
    exact hc.smul ((hu.differentiable one_ne_zero x).hasFDerivAt)
  have hvS : ∀ x, partialS v x = crpχ x.2 • partialS u x := by
    intro x
    simp only [partialS, (hvd x).fderiv]
    simp
  have hvT : ∀ x, partialT v x = crpχ x.2 • partialT u x + deriv crpχ x.2 • u x := by
    intro x
    simp only [partialT, (hvd x).fderiv]
    simp
  have hvs : HasCompactSupport v := by
    refine HasCompactSupport.intro (K := Icc (-|R|) |R| ×ˢ Icc (-2 : ℝ) 3)
      (isCompact_Icc.prod isCompact_Icc) ?_
    rintro ⟨s, t⟩ hx
    simp only [hv_def]
    by_cases h1 : R < |s|
    · rw [hR s t h1, smul_zero]
    · have hs : s ∈ Icc (-|R|) |R| := by
        rw [mem_Icc, ← abs_le]; exact (not_lt.1 h1).trans (le_abs_self R)
      have ht : t ∉ Ico (-2 : ℝ) 3 := fun ht => hx ⟨hs, ht.1, ht.2.le⟩
      rw [crpχ_zero ht, zero_smul]
  -- continuity
  have hcd : Continuous (fun x => fderiv ℝ u x) := hu.continuous_fderiv one_ne_zero
  have hcS : Continuous (partialS u) := hcd.clm_apply continuous_const
  have hcT : Continuous (partialT u) := hcd.clm_apply continuous_const
  have hcu : Continuous u := hu.continuous
  set F : ℝ × ℝ → Vec n := fun x => partialS u x + Matrix.toEuclideanLin (J₀ n) (partialT u x)
  have hcF : Continuous F := hcS.add (Jc.continuous.comp hcT)
  -- periodicity
  have hperS : ∀ s t, partialS u (s, t + 1) = partialS u (s, t) := fun s t => by
    simp only [partialS, crp_fderiv_per hper]
  have hperT : ∀ s t, partialT u (s, t + 1) = partialT u (s, t) := fun s t => by
    simp only [partialT, crp_fderiv_per hper]
  have hperF : ∀ s t, F (s, t + 1) = F (s, t) := fun s t => by
    simp only [F, hperS, hperT]
  -- step 1: on the strip, `v = u` near every point
  have hloc : ∀ x : ℝ × ℝ, x.2 ∈ Ico (0 : ℝ) 1 → fderiv ℝ v x = fderiv ℝ u x := by
    intro x hx
    apply Filter.EventuallyEq.fderiv_eq
    have hopen : IsOpen {y : ℝ × ℝ | y.2 ∈ Ioo (-1 / 2 : ℝ) (3 / 2)} :=
      isOpen_Ioo.preimage continuous_snd
    filter_upwards [hopen.mem_nhds (show x.2 ∈ Ioo (-1 / 2 : ℝ) (3 / 2) from
      ⟨by linarith [hx.1], by linarith [hx.2]⟩)] with y hy
    simp only [hv_def, crpχ_one hy.1.le hy.2.le, one_smul]
  have hae : ∀ᵐ x ∂cylMeasure, x.2 ∈ Ico (0 : ℝ) 1 := by
    unfold cylMeasure
    filter_upwards [ae_restrict_mem (show MeasurableSet ((univ : Set ℝ) ×ˢ Ico (0 : ℝ) 1) from
      MeasurableSet.univ.prod measurableSet_Ico)] with x hx
    exact hx.2
  have hcyl : cylMeasure ≤ (volume : Measure (ℝ × ℝ)) := by
    unfold cylMeasure; exact Measure.restrict_le_self
  have e1 : eLpNorm (partialS u) p cylMeasure ≤ eLpNorm (partialS v) p volume := by
    calc eLpNorm (partialS u) p cylMeasure = eLpNorm (partialS v) p cylMeasure := by
          apply eLpNorm_congr_ae
          filter_upwards [hae] with x hx
          simp only [partialS, hloc x hx]
      _ ≤ _ := eLpNorm_mono_measure _ hcyl
  have e2 : eLpNorm (partialT u) p cylMeasure ≤ eLpNorm (partialT v) p volume := by
    calc eLpNorm (partialT u) p cylMeasure = eLpNorm (partialT v) p cylMeasure := by
          apply eLpNorm_congr_ae
          filter_upwards [hae] with x hx
          simp only [partialT, hloc x hx]
      _ ≤ _ := eLpNorm_mono_measure _ hcyl
  -- step 2: the Cauchy–Riemann term of `v`
  set g1 : ℝ × ℝ → Vec n := (univ ×ˢ Ico (-2 : ℝ) 3).indicator F
  set g2 : ℝ × ℝ → Vec n :=
    (univ ×ˢ Ico (-2 : ℝ) 3).indicator (fun x => ((M * N : ℝ≥0) : ℝ) • u x)
  have hpt : ∀ x, ‖partialS v x + Matrix.toEuclideanLin (J₀ n) (partialT v x)‖ ≤
      ‖‖g1 x‖ + ‖g2 x‖‖ := by
    intro x
    have hform : partialS v x + Matrix.toEuclideanLin (J₀ n) (partialT v x) =
        crpχ x.2 • F x + deriv crpχ x.2 • Matrix.toEuclideanLin (J₀ n) (u x) := by
      rw [hvS, hvT, map_add, map_smul, map_smul]
      simp only [F, smul_add]
      abel
    rw [hform, Real.norm_of_nonneg (by positivity)]
    by_cases hx : x ∈ univ ×ˢ Ico (-2 : ℝ) 3
    · simp only [g1, g2, indicator_of_mem hx]
      calc ‖crpχ x.2 • F x + deriv crpχ x.2 • Matrix.toEuclideanLin (J₀ n) (u x)‖
          ≤ ‖crpχ x.2 • F x‖ + ‖deriv crpχ x.2 • Matrix.toEuclideanLin (J₀ n) (u x)‖ :=
            norm_add_le _ _
        _ ≤ ‖F x‖ + ‖((M * N : ℝ≥0) : ℝ) • u x‖ := by
            gcongr
            · rw [norm_smul, Real.norm_eq_abs]
              exact (mul_le_of_le_one_left (norm_nonneg _) (crpχ_abs_le _))
            · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg (show (0 : ℝ) ≤ ((M * N : ℝ≥0) : ℝ) from (M * N).2),
                NNReal.coe_mul, mul_assoc]
              exact mul_le_mul (hM _) (hJ _) (norm_nonneg _) M.2
    · have ht : x.2 ∉ Ico (-2 : ℝ) 3 := fun ht => hx ⟨mem_univ _, ht⟩
      rw [crpχ_zero ht, crpχ_deriv_zero ht, zero_smul, zero_smul, add_zero, norm_zero]
      positivity
  have hg1m : AEStronglyMeasurable g1 volume := hcF.aestronglyMeasurable.indicator hT
  have hg2m : AEStronglyMeasurable g2 volume :=
    (show Continuous (fun x => ((M * N : ℝ≥0) : ℝ) • u x) from
      by fun_prop).aestronglyMeasurable.indicator hT
  have e3 : eLpNorm (fun x => partialS v x + Matrix.toEuclideanLin (J₀ n) (partialT v x)) p
      volume ≤ 5 * eLpNorm F p cylMeasure + ((M * N : ℝ≥0) : ℝ≥0∞) * (5 * eLpNorm u p cylMeasure) := by
    calc _ ≤ eLpNorm (fun x => ‖g1 x‖ + ‖g2 x‖) p volume := eLpNorm_mono hpt
      _ ≤ eLpNorm (fun x => ‖g1 x‖) p volume + eLpNorm (fun x => ‖g2 x‖) p volume :=
          eLpNorm_add_le hg1m.norm hg2m.norm hp1
      _ = eLpNorm g1 p volume + eLpNorm g2 p volume := by rw [eLpNorm_norm, eLpNorm_norm]
      _ = eLpNorm F p (volume.restrict (univ ×ˢ Ico (-2 : ℝ) 3)) +
            eLpNorm (fun x => ((M * N : ℝ≥0) : ℝ) • u x) p
              (volume.restrict (univ ×ˢ Ico (-2 : ℝ) 3)) := by
          rw [eLpNorm_indicator_eq_eLpNorm_restrict hT, eLpNorm_indicator_eq_eLpNorm_restrict hT]
      _ = eLpNorm F p (volume.restrict (univ ×ˢ Ico (-2 : ℝ) 3)) +
            ((M * N : ℝ≥0) : ℝ≥0∞) * eLpNorm u p (volume.restrict (univ ×ˢ Ico (-2 : ℝ) 3)) := by
          congr 1
          rw [show (fun x => ((M * N : ℝ≥0) : ℝ) • u x) = ((M * N : ℝ≥0) : ℝ) • u from rfl,
            eLpNorm_const_smul]
          congr 1
          rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_coe_nnreal]
      _ ≤ 5 * eLpNorm F p cylMeasure + ((M * N : ℝ≥0) : ℝ≥0∞) * (5 * eLpNorm u p cylMeasure) := by
          gcongr
          · exact crp_eLpNorm_le F hperF p hp1 hp'
          · exact crp_eLpNorm_le u hper p hp1 hp'
  -- step 3: combine
  have hBv := hB v hvc hvs
  calc eLpNorm (partialS u) p cylMeasure + eLpNorm (partialT u) p cylMeasure
      ≤ eLpNorm (partialS v) p volume + eLpNorm (partialT v) p volume := add_le_add e1 e2
    _ ≤ B * eLpNorm (fun x => partialS v x + Matrix.toEuclideanLin (J₀ n) (partialT v x)) p
          volume := hBv
    _ ≤ B * (5 * eLpNorm F p cylMeasure +
          ((M * N : ℝ≥0) : ℝ≥0∞) * (5 * eLpNorm u p cylMeasure)) := by gcongr
    _ = (B * 5 : ℝ≥0) * eLpNorm F p cylMeasure +
          (B * 5 * (M * N) : ℝ≥0) * eLpNorm u p cylMeasure := by
        push_cast; ring
    _ ≤ A * eLpNorm F p cylMeasure + A * eLpNorm u p cylMeasure := by
        gcongr
        · exact_mod_cast (show B * 5 ≤ B * 5 * (1 + M * N) from
            le_mul_of_one_le_right (by positivity) le_self_add)
        · exact_mod_cast (show B * 5 * (M * N) ≤ B * 5 * (1 + M * N) by
            gcongr; exact le_add_self)

end

end CauchyRiemannIndex

-- ===== Scratch/CRLocPerSol.lean =====
open CauchyRiemannIndex in
theorem solution (n : ℕ) (p : ENNReal) (hp : 1 < p) (hp' : p ≠ ⊤) :
    ∃ A : NNReal, ∀ u : ℝ × ℝ → Vec n, ContDiff ℝ 1 u → (∀ s t, u (s, t + 1) = u (s, t)) →
      (∃ R : ℝ, ∀ s t, R < |s| → u (s, t) = 0) →
      MeasureTheory.eLpNorm (partialS u) p cylMeasure +
          MeasureTheory.eLpNorm (partialT u) p cylMeasure ≤
        A * MeasureTheory.eLpNorm
            (fun x => partialS u x + Matrix.toEuclideanLin (J₀ n) (partialT u x)) p cylMeasure +
          A * MeasureTheory.eLpNorm u p cylMeasure :=
  crp_main n p hp hp'
