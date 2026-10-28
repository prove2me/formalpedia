-- Prove2me | solution 1 for FunctionalInequalities.Probability.strict_sublevel_convex_and_interior_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:39:17.815915+00:00
-- url     : https://prove2.me/submissions/c29a637b-a611-46cc-a3fe-dbf17f5fc4ad

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ConvexSupport
import Theorems.Thm_FunctionalInequalities_Probability_real_convexOn_effective_domain_readable

open MeasureTheory
open scoped RealInnerProductSpace
section EffectiveDomain
open MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]
omit [MeasurableSpace E] in
private lemma FunctionalInequalities.Probability.effective_domain_convex (φ : E → EReal)
    (hφ : Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)}) : Convex ℝ {x | φ x ≠ ⊤} := by
  have himage : (LinearMap.fst ℝ E ℝ) '' {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} = {x | φ x ≠ ⊤} := by
    ext x
    constructor
    · rintro ⟨⟨y,t⟩, hp, hxy⟩
      change y = x at hxy
      subst y
      change φ x ≤ (t : EReal) at hp
      exact (lt_of_le_of_lt hp (EReal.coe_lt_top t)).ne
    · intro hx
      refine ⟨(x,(φ x).toReal), ?_, rfl⟩
      exact EReal.le_coe_toReal hx
  rw [← himage]
  exact hφ.linear_image (LinearMap.fst ℝ E ℝ)
end EffectiveDomain
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
 lemma solution {φ : E → EReal}
    (h0 : ∀ x, 0 ≤ φ x) (hφ : Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)})
    {x₀ y : E} (hx₀ : x₀ ∈ interior {x | φ x ≠ ⊤}) (hy : φ y < φ x₀) :
    Convex ℝ {x | φ x < φ x₀} ∧ (interior {x | φ x < φ x₀}).Nonempty := by
  let D : Set E := {x | φ x ≠ ⊤}
  let f : E → ℝ := fun x => (φ x).toReal
  have hxD : x₀ ∈ D := interior_subset hx₀
  have hyD : y ∈ D := (hy.trans_le le_top).ne
  have hDconv : Convex ℝ D := FunctionalInequalities.Probability.effective_domain_convex φ hφ
  have hcf : ConvexOn ℝ D f := FunctionalInequalities.Probability.real_convexOn_effective_domain_readable h0 hφ
  have hS : {x | φ x < φ x₀} = {x ∈ D | f x < f x₀} := by
    ext x
    constructor
    · intro hx
      change φ x < φ x₀ at hx
      have hxD' : x ∈ D := (hx.trans_le le_top).ne
      refine ⟨hxD', ?_⟩
      rw [← FunctionalInequalities.Probability.finite_value_coe h0 hxD', ← FunctionalInequalities.Probability.finite_value_coe h0 hxD] at hx
      exact EReal.coe_lt_coe_iff.mp hx
    · rintro ⟨hxD', hx⟩
      change φ x < φ x₀
      rw [← FunctionalInequalities.Probability.finite_value_coe h0 hxD', ← FunctionalInequalities.Probability.finite_value_coe h0 hxD]
      exact EReal.coe_lt_coe_iff.mpr hx
  have hconv : Convex ℝ {x | φ x < φ x₀} := by
    rw [hS]
    exact hcf.convex_lt (f x₀)
  let z : E := (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • x₀
  have hzD : z ∈ interior D :=
    hDconv.combo_self_interior_mem_interior hyD hx₀ (by norm_num) (by norm_num) (by norm_num)
  have hyf : f y < f x₀ := by
    rw [← FunctionalInequalities.Probability.finite_value_coe h0 hyD, ← FunctionalInequalities.Probability.finite_value_coe h0 hxD] at hy
    exact EReal.coe_lt_coe_iff.mp hy
  have hzle : f z ≤ (1 / 2 : ℝ) * f y + (1 / 2 : ℝ) * f x₀ :=
    hcf.2 hyD hxD (by norm_num) (by norm_num) (by norm_num)
  have hzlt : f z < f x₀ := by linarith
  have hcont : ContinuousOn f (interior D) :=
    (hcf.subset interior_subset hDconv.interior).continuousOn isOpen_interior
  have hopen : IsOpen (interior D ∩ f ⁻¹' Set.Iio (f x₀)) :=
    hcont.isOpen_inter_preimage isOpen_interior isOpen_Iio
  have hsubset : interior D ∩ f ⁻¹' Set.Iio (f x₀) ⊆ {x | φ x < φ x₀} := by
    rw [hS]
    intro x hx
    exact ⟨interior_subset hx.1, hx.2⟩
  have hzU : z ∈ interior (interior D ∩ f ⁻¹' Set.Iio (f x₀)) := by
    rw [hopen.interior_eq]
    exact ⟨hzD, hzlt⟩
  exact ⟨hconv, ⟨z, (interior_mono hsubset) hzU⟩⟩
