-- Prove2me | solution 1 for EndToEndRisk.SquaredLoss.corollary_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:25:54.042474+00:00
-- url     : https://prove2.me/submissions/470f59cb-702c-402e-bfa3-642cf1461972

import Mathlib
import Definitions.Def_EndToEndRisk_SquaredLoss_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
open EndToEndRisk.SquaredLoss

namespace E2ECor3Aux

variable {m : ℕ}


lemma optVal_eq (X : Set (EuclideanSpace ℝ (Fin m))) (f : (EuclideanSpace ℝ (Fin m)) → ℝ) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m))) (hx : IsArgminSelection X f xstar)
    (c : (EuclideanSpace ℝ (Fin m))) : optVal X f c = f (xstar c) + ⟪c, xstar c⟫_ℝ := by
  unfold optVal
  apply IsLeast.csInf_eq
  refine ⟨⟨xstar c, (hx c).1, rfl⟩, ?_⟩
  rintro _ ⟨x, hxX, rfl⟩
  exact (hx c).2 x hxX

lemma trueLoss_eq (X : Set (EuclideanSpace ℝ (Fin m))) (f : (EuclideanSpace ℝ (Fin m)) → ℝ) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m))) (hx : IsArgminSelection X f xstar)
    (d c : (EuclideanSpace ℝ (Fin m))) : trueLoss X f xstar d c =
      f (xstar d) + ⟪c, xstar d⟫_ℝ - (f (xstar c) + ⟪c, xstar c⟫_ℝ) := by
  unfold trueLoss; rw [optVal_eq X f xstar hx]

lemma trueLoss_nonneg (X : Set (EuclideanSpace ℝ (Fin m))) (f : (EuclideanSpace ℝ (Fin m)) → ℝ) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m))) (hx : IsArgminSelection X f xstar)
    (d c : (EuclideanSpace ℝ (Fin m))) : 0 ≤ trueLoss X f xstar d c := by
  rw [trueLoss_eq X f xstar hx]
  have := (hx c).2 (xstar d) (hx d).1
  linarith

/-- The conditional excess true loss `Δ(d, e) = f(x*(d)) − f(x*(e)) + eᵀ(x*(d) − x*(e))`. -/
noncomputable def gap (f : (EuclideanSpace ℝ (Fin m)) → ℝ) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m))) (d e : (EuclideanSpace ℝ (Fin m))) : ℝ :=
  f (xstar d) - f (xstar e) + ⟪e, xstar d - xstar e⟫_ℝ

lemma gap_nonneg (X : Set (EuclideanSpace ℝ (Fin m))) (f : (EuclideanSpace ℝ (Fin m)) → ℝ) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m))) (hx : IsArgminSelection X f xstar)
    (d e : (EuclideanSpace ℝ (Fin m))) : 0 ≤ gap f xstar d e := by
  unfold gap
  have := (hx e).2 (xstar d) (hx d).1
  rw [inner_sub_right]
  linarith

/-- Lemma 5 / Theorem 4 of the paper: `Δ(d, e) ≤ ‖d − e‖ ‖x*(d) − x*(e)‖ ≤ B_X ‖d − e‖`. -/
lemma gap_le (X : Set (EuclideanSpace ℝ (Fin m))) (f : (EuclideanSpace ℝ (Fin m)) → ℝ) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m))) (hx : IsArgminSelection X f xstar)
    (hXb : Bornology.IsBounded X) (d e : (EuclideanSpace ℝ (Fin m))) :
    gap f xstar d e ≤ Metric.diam X * ‖d - e‖ := by
  unfold gap
  have h1 := (hx d).2 (xstar e) (hx e).1
  have h2 : f (xstar d) - f (xstar e) + ⟪e, xstar d - xstar e⟫_ℝ ≤
      ⟪d - e, xstar e - xstar d⟫_ℝ := by
    simp only [inner_sub_left, inner_sub_right] at *
    linarith
  have h3 : ⟪d - e, xstar e - xstar d⟫_ℝ ≤ ‖d - e‖ * ‖xstar e - xstar d‖ :=
    real_inner_le_norm _ _
  have h4 : ‖xstar e - xstar d‖ ≤ Metric.diam X := by
    rw [← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem hXb (hx e).1 (hx d).1
  have h5 : ‖d - e‖ * ‖xstar e - xstar d‖ ≤ ‖d - e‖ * Metric.diam X :=
    mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
  linarith

lemma measurable_f_xstar (X : Set (EuclideanSpace ℝ (Fin m))) (f : (EuclideanSpace ℝ (Fin m)) → ℝ) (hS : Standing X f) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)))
    (hx : IsArgminSelection X f xstar) (hxm : Measurable xstar) :
    Measurable (fun d => f (xstar d)) := by
  have hc : Continuous (X.domRestrict f) := hS.2.2.2.2.domRestrict
  have hm : Measurable (fun d => (⟨xstar d, (hx d).1⟩ : X)) := hxm.subtype_mk
  exact hc.measurable.comp hm


section Measure

variable (ν : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure ν]

lemma integrable_sq (h2 : ∫⁻ c, ‖c‖ₑ ^ 2 ∂ν < ⊤) : Integrable (fun c : (EuclideanSpace ℝ (Fin m)) => ‖c‖ ^ 2) ν := by
  refine ⟨(continuous_norm.pow 2).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  simpa [enorm_pow] using h2

lemma integrable_id' (h2 : ∫⁻ c, ‖c‖ₑ ^ 2 ∂ν < ⊤) : Integrable (fun c : (EuclideanSpace ℝ (Fin m)) => c) ν := by
  refine Integrable.mono' ((integrable_const (1:ℝ)).add (integrable_sq ν h2))
    aestronglyMeasurable_id (Filter.Eventually.of_forall ?_)
  intro c
  have := norm_nonneg c
  simp only [Pi.add_apply]
  nlinarith

lemma key (u v : (EuclideanSpace ℝ (Fin m)) → ℝ) (K : ℝ) (w : (EuclideanSpace ℝ (Fin m))) (hu : Integrable u ν) (hv : Integrable v ν)
    (hid : Integrable (fun c : (EuclideanSpace ℝ (Fin m)) => c) ν) (hK : 0 ≤ K) (hu0 : ∀ c, 0 ≤ u c) (hv0 : ∀ c, 0 ≤ v c)
    (h : ∀ c, u c = K + v c + ⟪c - ∫ c, c ∂ν, w⟫_ℝ) :
    ∫⁻ c, ENNReal.ofReal (u c) ∂ν = ENNReal.ofReal K + ∫⁻ c, ENNReal.ofReal (v c) ∂ν := by
  rw [← ofReal_integral_eq_lintegral_ofReal hu (Filter.Eventually.of_forall hu0),
    ← ofReal_integral_eq_lintegral_ofReal hv (Filter.Eventually.of_forall hv0),
    ← ENNReal.ofReal_add hK (integral_nonneg hv0)]
  congr 1
  have hi : Integrable (fun c => ⟪c - ∫ c, c ∂ν, w⟫_ℝ) ν := by
    have : Integrable (fun c => c - ∫ c, c ∂ν) ν := hid.sub (integrable_const _)
    simpa [real_inner_comm] using this.inner_const (𝕜 := ℝ) w
  have h0 : ∫ c, ⟪c - ∫ c, c ∂ν, w⟫_ℝ ∂ν = 0 := by
    have e1 : ∀ c, ⟪c - ∫ c, c ∂ν, w⟫_ℝ = ⟪w, c - ∫ c, c ∂ν⟫_ℝ := fun c => real_inner_comm _ _
    rw [integral_congr_ae (Filter.Eventually.of_forall e1),
      integral_inner (f := fun c => c - ∫ c, c ∂ν) (hid.sub (integrable_const _)) w,
      integral_sub hid (integrable_const _)]
    simp
  rw [integral_congr_ae (Filter.Eventually.of_forall h),
    integral_add (f := fun c => K + v c) ((integrable_const K).add hv) hi,
    integral_add (integrable_const K) hv, h0]
  simp


lemma integrable_sq_sub (h2 : ∫⁻ c, ‖c‖ₑ ^ 2 ∂ν < ⊤) (a : (EuclideanSpace ℝ (Fin m))) :
    Integrable (fun c : (EuclideanSpace ℝ (Fin m)) => ‖a - c‖ ^ 2) ν := by
  refine Integrable.mono' ((integrable_const (2 * ‖a‖ ^ 2)).add
    ((integrable_sq ν h2).const_mul 2))
    ((continuous_const.sub continuous_id).norm.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall ?_)
  intro c
  have h1 := norm_sub_le a c
  have := norm_nonneg a
  have := norm_nonneg c
  have := norm_nonneg (a - c)
  simp only [Pi.add_apply, norm_pow, norm_norm]
  nlinarith [mul_self_le_mul_self this h1, sq_nonneg (‖a‖ - ‖c‖)]

/-- Conditional decomposition of the squared loss:
`E‖d − c‖² = ‖d − c̄‖² + E‖c̄ − c‖²` with `c̄ = E c`. -/
lemma cond_ls (h2 : ∫⁻ c, ‖c‖ₑ ^ 2 ∂ν < ⊤) (d : (EuclideanSpace ℝ (Fin m))) :
    ∫⁻ c, ENNReal.ofReal (lsLoss d c) ∂ν =
      ENNReal.ofReal (‖d - ∫ c, c ∂ν‖ ^ 2) +
        ∫⁻ c, ENNReal.ofReal (lsLoss (∫ c, c ∂ν) c) ∂ν := by
  unfold lsLoss
  refine key ν _ _ _ ((-2 : ℝ) • (d - ∫ c, c ∂ν)) (integrable_sq_sub ν h2 d)
    (integrable_sq_sub ν h2 _) (integrable_id' ν h2) (sq_nonneg _) (fun _ => sq_nonneg _)
    (fun _ => sq_nonneg _) ?_
  intro c
  have : d - c = (d - ∫ c, c ∂ν) + ((∫ c, c ∂ν) - c) := by abel
  rw [this, norm_add_sq_real, inner_smul_right, real_inner_comm]
  have : c - ∫ c, c ∂ν = -((∫ c, c ∂ν) - c) := by abel
  rw [this, inner_neg_left]
  ring

/-- Conditional decomposition of the optimality-gap loss:
`E L(d, c) = Δ(d, c̄) + E L(c̄, c)` with `c̄ = E c`. -/
lemma cond_true (X : Set (EuclideanSpace ℝ (Fin m))) (f : (EuclideanSpace ℝ (Fin m)) → ℝ)
    (hS : Standing X f) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)))
    (hx : IsArgminSelection X f xstar) (hxm : Measurable xstar)
    (h2 : ∫⁻ c, ‖c‖ₑ ^ 2 ∂ν < ⊤) (d : (EuclideanSpace ℝ (Fin m))) :
    ∫⁻ c, ENNReal.ofReal (trueLoss X f xstar d c) ∂ν =
      ENNReal.ofReal (gap f xstar d (∫ c, c ∂ν)) +
        ∫⁻ c, ENNReal.ofReal (trueLoss X f xstar (∫ c, c ∂ν) c) ∂ν := by
  obtain ⟨K, hK⟩ := hS.2.1.exists_bound_of_continuousOn hS.2.2.2.2
  obtain ⟨R, hR⟩ := hS.2.1.isBounded.exists_norm_le
  have hid := integrable_id' ν h2
  have hfm := measurable_f_xstar X f hS xstar hx hxm
  have hint : ∀ e, Integrable (fun c => trueLoss X f xstar e c) ν := by
    intro e
    have i1 : Integrable (fun c : (EuclideanSpace ℝ (Fin m)) => ⟪c, xstar e⟫_ℝ) ν :=
      hid.inner_const (xstar e)
    have i2 : Integrable (fun c => f (xstar c)) ν :=
      Integrable.mono' (integrable_const K) hfm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun c => hK _ (hx c).1)
    have i3 : Integrable (fun c : (EuclideanSpace ℝ (Fin m)) => ⟪c, xstar c⟫_ℝ) ν := by
      refine Integrable.mono' (hid.norm.const_mul R) ?_ (Filter.Eventually.of_forall ?_)
      · exact (measurable_id.inner hxm).aestronglyMeasurable
      · intro c
        have h1 : |⟪c, xstar c⟫_ℝ| ≤ ‖c‖ * ‖xstar c‖ := abs_real_inner_le_norm _ _
        have h3 := hR _ (hx c).1
        have := norm_nonneg c
        rw [Real.norm_eq_abs]
        nlinarith
    have : (fun c => trueLoss X f xstar e c) =
        fun c => f (xstar e) + ⟪c, xstar e⟫_ℝ - (f (xstar c) + ⟪c, xstar c⟫_ℝ) := by
      funext c; exact trueLoss_eq X f xstar hx e c
    rw [this]
    exact ((integrable_const _).add i1).sub (i2.add i3)
  refine key ν _ _ _ (xstar d - xstar (∫ c, c ∂ν)) (hint d) (hint _) hid
    (gap_nonneg X f xstar hx _ _) (trueLoss_nonneg X f xstar hx d)
    (trueLoss_nonneg X f xstar hx _) ?_
  intro c
  rw [trueLoss_eq X f xstar hx, trueLoss_eq X f xstar hx]
  unfold gap
  simp only [inner_sub_left, inner_sub_right]
  ring

end Measure

lemma sq_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (u : α → ℝ≥0∞) (hu : Measurable u) : (∫⁻ a, u a ∂μ) ^ 2 ≤ ∫⁻ a, u a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hu.aemeasurable
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
  have hB : ∫⁻ a, u a ^ (2:ℝ) ∂μ = ∫⁻ a, u a ^ 2 ∂μ := by
    refine lintegral_congr fun a => ?_
    exact ENNReal.rpow_two _
  rw [hB] at h
  have e : ((∫⁻ a, u a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ (2:ℕ) = ∫⁻ a, u a ^ 2 ∂μ := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  calc (∫⁻ a, u a ∂μ) ^ 2 ≤ ((∫⁻ a, u a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ (2:ℕ) :=
        pow_le_pow_left₀ zero_le h 2
    _ = _ := e

end E2ECor3Aux

open E2ECor3Aux in
theorem solution {m : ℕ} {W : Type*} [MeasurableSpace W]
    (X : Set (EuclideanSpace ℝ (Fin m))) (f : EuclideanSpace ℝ (Fin m) → ℝ) (hS : Standing X f)
    (xstar : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hx : IsArgminSelection X f xstar) (hxm : Measurable xstar)
    (C : Set (EuclideanSpace ℝ (Fin m))) (hA2 : Bornology.IsBounded C)
    (μ : Measure W) [IsProbabilityMeasure μ]
    (κ : Kernel W (EuclideanSpace ℝ (Fin m))) [IsMarkovKernel κ]
    (hκ : ∀ w, κ w ∈ lsClass C)
    (hsq : ∫⁻ p, ‖p.2‖ₑ ^ 2 ∂(μ ⊗ₘ κ) < ⊤)
    (g : W → EuclideanSpace ℝ (Fin m)) (hg : Measurable g) :
    (risk (trueLoss X f xstar) (μ ⊗ₘ κ) g - EndToEndRisk.SquaredLoss.bayesRisk (trueLoss X f xstar) (μ ⊗ₘ κ)) ^ 2 ≤
      ENNReal.ofReal (Metric.diam X ^ 2) *
        (risk lsLoss (μ ⊗ₘ κ) g - EndToEndRisk.SquaredLoss.bayesRisk lsLoss (μ ⊗ₘ κ)) := by
  set cbar : W → EuclideanSpace ℝ (Fin m) := fun w => ∫ c, c ∂(κ w) with hcbar
  have hcm : Measurable cbar := (stronglyMeasurable_id.integral_kernel (κ := κ)).measurable
  have h2 : ∀ w, ∫⁻ c, ‖c‖ₑ ^ 2 ∂(κ w) < ⊤ := fun w => (hκ w).2.2.1
  have hfm := measurable_f_xstar X f hS xstar hx hxm
  -- measurability of the integrands
  have hmT : ∀ h : W → EuclideanSpace ℝ (Fin m), Measurable h →
      Measurable (fun p : W × EuclideanSpace ℝ (Fin m) =>
        ENNReal.ofReal (trueLoss X f xstar (h p.1) p.2)) := by
    intro h hh
    have : (fun p : W × EuclideanSpace ℝ (Fin m) => trueLoss X f xstar (h p.1) p.2) =
        fun p => f (xstar (h p.1)) + ⟪p.2, xstar (h p.1)⟫_ℝ -
          (f (xstar p.2) + ⟪p.2, xstar p.2⟫_ℝ) := by
      funext p; exact trueLoss_eq X f xstar hx _ _
    refine ENNReal.measurable_ofReal.comp ?_
    rw [this]
    have a1 : Measurable (fun p : W × EuclideanSpace ℝ (Fin m) => xstar (h p.1)) :=
      hxm.comp (hh.comp measurable_fst)
    have a2 : Measurable (fun p : W × EuclideanSpace ℝ (Fin m) => xstar p.2) :=
      hxm.comp measurable_snd
    exact ((hfm.comp (hh.comp measurable_fst)).add (measurable_snd.inner a1)).sub
      ((hfm.comp measurable_snd).add (measurable_snd.inner a2))
  have hmS : ∀ h : W → EuclideanSpace ℝ (Fin m), Measurable h →
      Measurable (fun p : W × EuclideanSpace ℝ (Fin m) =>
        ENNReal.ofReal (lsLoss (h p.1) p.2)) := by
    intro h hh
    unfold lsLoss
    exact ENNReal.measurable_ofReal.comp
      (((hh.comp measurable_fst).sub measurable_snd).norm.pow_const 2)
  have hgapm : ∀ h : W → EuclideanSpace ℝ (Fin m), Measurable h →
      Measurable (fun w => ENNReal.ofReal (gap f xstar (h w) (cbar w))) := by
    intro h hh
    unfold gap
    exact ENNReal.measurable_ofReal.comp
      (((hfm.comp hh).sub (hfm.comp hcm)).add
        (hcm.inner ((hxm.comp hh).sub (hxm.comp hcm))))
  have hQm : ∀ h : W → EuclideanSpace ℝ (Fin m), Measurable h →
      Measurable (fun w => ENNReal.ofReal (‖h w - cbar w‖ ^ 2)) := by
    intro h hh
    exact ENNReal.measurable_ofReal.comp ((hh.sub hcm).norm.pow_const 2)
  set mT : W → ℝ≥0∞ := fun w => ∫⁻ c, ENNReal.ofReal (trueLoss X f xstar (cbar w) c) ∂(κ w)
  set mS : W → ℝ≥0∞ := fun w => ∫⁻ c, ENNReal.ofReal (lsLoss (cbar w) c) ∂(κ w)
  have riskT : ∀ h : W → EuclideanSpace ℝ (Fin m), Measurable h →
      risk (trueLoss X f xstar) (μ ⊗ₘ κ) h =
        ∫⁻ w, ENNReal.ofReal (gap f xstar (h w) (cbar w)) ∂μ + ∫⁻ w, mT w ∂μ := by
    intro h hh
    unfold risk
    rw [Measure.lintegral_compProd (hmT h hh), ← lintegral_add_left (hgapm h hh)]
    refine lintegral_congr fun w => ?_
    exact cond_true (κ w) X f hS xstar hx hxm (h2 w) (h w)
  have riskS : ∀ h : W → EuclideanSpace ℝ (Fin m), Measurable h →
      risk lsLoss (μ ⊗ₘ κ) h =
        ∫⁻ w, ENNReal.ofReal (‖h w - cbar w‖ ^ 2) ∂μ + ∫⁻ w, mS w ∂μ := by
    intro h hh
    unfold risk
    rw [Measure.lintegral_compProd (hmS h hh), ← lintegral_add_left (hQm h hh)]
    refine lintegral_congr fun w => ?_
    exact cond_ls (κ w) (h2 w) (h w)
  -- lower bound on the Bayes true risk
  have hbT : ∫⁻ w, mT w ∂μ ≤ EndToEndRisk.SquaredLoss.bayesRisk (trueLoss X f xstar) (μ ⊗ₘ κ) := by
    unfold EndToEndRisk.SquaredLoss.bayesRisk
    refine le_iInf₂ fun h hh => ?_
    rw [riskT h hh]
    exact le_add_self
  -- upper bound on the Bayes squared-loss risk
  have hbS : EndToEndRisk.SquaredLoss.bayesRisk lsLoss (μ ⊗ₘ κ) ≤ ∫⁻ w, mS w ∂μ := by
    unfold EndToEndRisk.SquaredLoss.bayesRisk
    refine (iInf₂_le cbar hcm).trans ?_
    rw [riskS cbar hcm]
    simp
  have hmSfin : ∫⁻ w, mS w ∂μ ≠ ⊤ := by
    have hle : ∀ w, mS w ≤ ∫⁻ c, ENNReal.ofReal (lsLoss ((fun _ : W => (0 : EuclideanSpace ℝ (Fin m))) w) c) ∂(κ w) := by
      intro w
      rw [cond_ls (κ w) (h2 w)]
      exact le_add_self
    have h0 := Measure.lintegral_compProd (μ := μ) (κ := κ) (hmS (fun _ : W => (0 : EuclideanSpace ℝ (Fin m))) measurable_const)
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
    rw [← h0]
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hsq)
    refine lintegral_congr fun p => ?_
    simp [lsLoss, ENNReal.ofReal_pow]
  have hTle : risk (trueLoss X f xstar) (μ ⊗ₘ κ) g - EndToEndRisk.SquaredLoss.bayesRisk (trueLoss X f xstar) (μ ⊗ₘ κ) ≤
      ∫⁻ w, ENNReal.ofReal (gap f xstar (g w) (cbar w)) ∂μ := by
    refine (tsub_le_tsub_left hbT _).trans ?_
    rw [riskT g hg]
    exact add_tsub_le_right
  have hSge : ∫⁻ w, ENNReal.ofReal (‖g w - cbar w‖ ^ 2) ∂μ ≤
      risk lsLoss (μ ⊗ₘ κ) g - EndToEndRisk.SquaredLoss.bayesRisk lsLoss (μ ⊗ₘ κ) := by
    refine le_trans ?_ (tsub_le_tsub_left hbS _)
    rw [riskS g hg, ENNReal.add_sub_cancel_right hmSfin]
  -- pointwise bound and Cauchy–Schwarz
  have hXb : Bornology.IsBounded X := hS.2.1.isBounded
  have hD : 0 ≤ Metric.diam X := Metric.diam_nonneg
  set u : W → ℝ≥0∞ := fun w => ENNReal.ofReal ‖g w - cbar w‖ with hu
  have hum : Measurable u := ENNReal.measurable_ofReal.comp (hg.sub hcm).norm
  have hpt : ∀ w, ENNReal.ofReal (gap f xstar (g w) (cbar w)) ≤ ENNReal.ofReal (Metric.diam X) * u w := by
    intro w
    rw [hu, ← ENNReal.ofReal_mul hD]
    exact ENNReal.ofReal_le_ofReal (gap_le X f xstar hx hXb _ _)
  have hint : ∫⁻ w, ENNReal.ofReal (gap f xstar (g w) (cbar w)) ∂μ ≤
      ENNReal.ofReal (Metric.diam X) * ∫⁻ w, u w ∂μ := by
    rw [← lintegral_const_mul _ hum]
    exact lintegral_mono hpt
  have hQ : ∫⁻ w, ENNReal.ofReal (‖g w - cbar w‖ ^ 2) ∂μ = ∫⁻ w, u w ^ 2 ∂μ := by
    refine lintegral_congr fun w => ?_
    rw [hu, ENNReal.ofReal_pow (norm_nonneg _)]
  calc (risk (trueLoss X f xstar) (μ ⊗ₘ κ) g - EndToEndRisk.SquaredLoss.bayesRisk (trueLoss X f xstar) (μ ⊗ₘ κ)) ^ 2
      ≤ (ENNReal.ofReal (Metric.diam X) * ∫⁻ w, u w ∂μ) ^ 2 :=
        pow_le_pow_left₀ zero_le (hTle.trans hint) 2
    _ = ENNReal.ofReal (Metric.diam X ^ 2) * (∫⁻ w, u w ∂μ) ^ 2 := by
        rw [mul_pow, ENNReal.ofReal_pow hD]
    _ ≤ ENNReal.ofReal (Metric.diam X ^ 2) * ∫⁻ w, u w ^ 2 ∂μ := by
        gcongr
        exact sq_lintegral_le μ u hum
    _ ≤ ENNReal.ofReal (Metric.diam X ^ 2) *
        (risk lsLoss (μ ⊗ₘ κ) g - EndToEndRisk.SquaredLoss.bayesRisk lsLoss (μ ⊗ₘ κ)) := by
        gcongr
        rw [← hQ]
        exact hSge

