-- Prove2me | solution 1 for FunctionalInequalities.Probability.exists_pos_le_mul_lintegral_toReal_of_convex_epigraph_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:41:47.061841+00:00
-- url     : https://prove2.me/submissions/5695b82b-7490-4229-8493-6b247aad13f8

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ConvexSupport
import Theorems.Thm_FunctionalInequalities_Probability_exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure_readable
import Theorems.Thm_FunctionalInequalities_Probability_mem_interior_setOf_ne_top_of_lintegral_ne_top_readable
import Theorems.Thm_FunctionalInequalities_Probability_strict_sublevel_convex_and_interior_readable

open MeasureTheory
open scoped RealInnerProductSpace
section PointControl
open Set
private lemma FunctionalInequalities.Probability.finite_value_coe {E : Type*} {φ : E → EReal}
    (h0 : ∀ x, 0 ≤ φ x) {x : E} (hx : φ x ≠ ⊤) :
    ((φ x).toReal : EReal) = φ x := by
  exact EReal.coe_toReal hx (ne_of_gt (EReal.bot_lt_zero.trans_le (h0 x)))
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section FiniteDimensional
variable [FiniteDimensional ℝ E]
private theorem FunctionalInequalities.Probability.exists_unit_halfspace_le_or_isMin_of_convex_epigraph {φ : E → EReal} (h0 : ∀ x, 0 ≤ φ x)
    (hφ : Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)}) {x₀ : E} (hx₀ : x₀ ∈ interior {x | φ x ≠ ⊤}) :
    (∃ u : E, ‖u‖ = 1 ∧ ∀ x, 0 < ⟪u, x - x₀⟫ → φ x₀ ≤ φ x) ∨ ∀ x, φ x₀ ≤ φ x := by
  classical
  by_cases hmin : ∀ x, φ x₀ ≤ φ x
  · exact Or.inr hmin
  obtain ⟨y, hy⟩ := not_forall.mp hmin
  have hylt : φ y < φ x₀ := lt_of_not_ge hy
  obtain ⟨hSconv, hSint⟩ := strict_sublevel_convex_and_interior_readable h0 hφ hx₀ hylt
  obtain ⟨L, hL, hsep⟩ := geometric_hahn_banach_of_nonempty_interior_point (x := x₀) hSconv
    (by
      intro hx
      have hx' : x₀ ∈ {x | φ x < φ x₀} := interior_subset hx
      exact (lt_irrefl (φ x₀)) hx') hSint
  let w : E := (InnerProductSpace.toDual ℝ E).symm L
  have hw : w ≠ 0 := by
    intro hwzero
    apply hL
    have h := congrArg (InnerProductSpace.toDual ℝ E) hwzero
    simpa only [w, LinearIsometryEquiv.apply_symm_apply, map_zero] using h
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  left
  refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwpos), inv_mul_cancel₀ hwpos.ne']
  · intro x hx
    by_contra hnot
    have hs : x ∈ {x | φ x < φ x₀} := lt_of_not_ge hnot
    have hle : L x ≤ L x₀ := hsep x hs
    have hinner : ⟪w, x - x₀⟫ = L x - L x₀ := by
      dsimp [w]
      rw [inner_sub_right, InnerProductSpace.toDual_symm_apply,
        InnerProductSpace.toDual_symm_apply]
    rw [real_inner_smul_left, hinner] at hx
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos
      (inv_nonneg.mpr (norm_nonneg w)) (sub_nonpos.mpr hle))) hx
end FiniteDimensional
/-- **CEK Lemma 16, pointwise bound.** For a finite Borel measure and an interior point of the convex hull of its support
there is `C > 0`, chosen before `φ`, with `φ x₀ ≤ C · (∫⁻ φ dμ).toReal` for every nonnegative extended-real `φ` with convex
real epigraph, a.e.-measurable `toENNReal` and finite lintegral. -/
theorem solution [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (x₀ : E) :
    x₀ ∈ interior (convexHull ℝ μ.support) →
      ∃ C : ℝ, 0 < C ∧ ∀ φ : E → EReal,
        (∀ x, 0 ≤ φ x) → Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} →
        AEMeasurable (fun x => (φ x).toENNReal) μ →
        (∫⁻ x, (φ x).toENNReal ∂μ) ≠ ⊤ →
          φ x₀ ≤ ((C * (∫⁻ x, (φ x).toENNReal ∂μ).toReal : ℝ) : EReal) := by
  intro hx₀
  obtain ⟨m, hmpos, hmass, hhalf⟩ :=
    FunctionalInequalities.Probability.exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure_readable μ hx₀
  refine ⟨m⁻¹, inv_pos.mpr hmpos, ?_⟩
  intro φ h_nonneg h_epi h_meas h_int
  have hxD : x₀ ∈ interior {x | φ x ≠ ⊤} :=
    FunctionalInequalities.Probability.mem_interior_setOf_ne_top_of_lintegral_ne_top_readable μ x₀ hx₀ φ h_nonneg h_epi h_meas h_int
  have hset : ∃ S : Set E, m ≤ μ.real S ∧ ∀ x ∈ S, φ x₀ ≤ φ x := by
    rcases FunctionalInequalities.Probability.exists_unit_halfspace_le_or_isMin_of_convex_epigraph h_nonneg h_epi hxD with hgeo | hmin
    · obtain ⟨u, hu, hbound⟩ := hgeo
      exact ⟨{x | 0 < ⟪u, x - x₀⟫}, hhalf u hu, fun x hx => hbound x hx⟩
    · exact ⟨Set.univ, hmass, fun x _ => hmin x⟩
  obtain ⟨S, hSmass, hSphi⟩ := hset
  have hlow : (φ x₀).toENNReal * μ S ≤ ∫⁻ x, (φ x).toENNReal ∂μ := by
    rw [← setLIntegral_const]
    exact (setLIntegral_mono_ae h_meas.restrict
      (Filter.Eventually.of_forall fun x hx => EReal.toENNReal_le_toENNReal (hSphi x hx))).trans
      (setLIntegral_le_lintegral S _)
  have hreal := ENNReal.toReal_mono h_int hlow
  rw [ENNReal.toReal_mul, EReal.toReal_toENNReal (h_nonneg x₀)] at hreal
  have hmq : m * (φ x₀).toReal ≤ (∫⁻ x, (φ x).toENNReal ∂μ).toReal := by
    calc
      m * (φ x₀).toReal ≤ μ.real S * (φ x₀).toReal :=
        mul_le_mul_of_nonneg_right hSmass (EReal.toReal_nonneg (h_nonneg x₀))
      _ = (φ x₀).toReal * (μ S).toReal := by rw [measureReal_def, mul_comm]
      _ ≤ (∫⁻ x, (φ x).toENNReal ∂μ).toReal := hreal
  rw [← FunctionalInequalities.Probability.finite_value_coe h_nonneg (interior_subset hxD)]
  apply EReal.coe_le_coe_iff.mpr
  simpa only [div_eq_mul_inv, mul_comm] using (le_div_iff₀' hmpos).mpr hmq
