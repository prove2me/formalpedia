-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.integral_minors_weight_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:36.395646+00:00
-- url     : https://prove2.me/submissions/0db61dba-0cbb-4624-8fcd-129705d2293b

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_integral_points_weight_sum_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hf : BlockEndMinorFibreFinite) (hs : IdealInversePowerSum) (E : Type) [Field E] [NumberField E]
    [NumberField.IsTotallyComplex E] (p : ℕ) (s : Fin p → ℕ) (hs1 : ∀ a, 1 ≤ s a)
    (T : Finset (Fin p → E))
    (hT : ∀ t ∈ T, ∀ a, IsIntegral ℤ (IndexedMinorEntry s t a) ∧ IndexedMinorEntry s t a ≠ 0) :
    ∑ t ∈ T, (∏ a : Fin p, ∏ w : InfinitePlace E, (1 + (w (IndexedMinorEntry s t a)) ^ 2) ^ 2)⁻¹ ≤
      ((∏ a, s a : ℕ) : ℝ) * 16 ^ (Fintype.card (InfinitePlace E) * p) := by
  classical
  set φ : E → ℝ := fun x => ∏ w : InfinitePlace E, ((1 + (w x) ^ 2) ^ 2)⁻¹ with hφ
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => Finset.prod_nonneg fun w _ => by positivity
  set m : (Fin p → E) → (Fin p → E) := fun t a => IndexedMinorEntry s t a with hm
  set g : (Fin p → E) → ℝ := fun d => ∏ a, φ (d a) with hg
  have hg0 : ∀ d, 0 ≤ g d := fun d => Finset.prod_nonneg fun a _ => hφ0 _
  have e1 : ∀ t, (∏ a : Fin p, ∏ w : InfinitePlace E, (1 + (w (IndexedMinorEntry s t a)) ^ 2) ^ 2)⁻¹ = g (m t) := by
    intro t
    simp only [hg, hφ, hm, Finset.prod_inv_distrib]
  simp_rw [e1]

  have hne : ∀ t ∈ T, ∀ a, t a ≠ 0 := by
    intro t ht a h0
    apply (hT t ht a).2
    unfold IndexedMinorEntry
    apply Finset.prod_eq_zero (i := a) (by simp)
    rw [h0, zero_pow (by have := hs1 a; omega), mul_zero]
  rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image m) (g := m)
    (fun x hx => Finset.mem_image_of_mem m hx)]
  have e2 : ∀ d ∈ T.image m, ∑ t ∈ T with m t = d, g (m t) ≤ ((∏ a, s a : ℕ) : ℝ) * g d := by
    intro d _
    have : ∑ t ∈ T with m t = d, g (m t) = ∑ t ∈ T with m t = d, g d := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [(Finset.mem_filter.mp ht).2]
    rw [this, Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (hg0 d)
    have := hf E p s d (T.filter (fun t => m t = d)) hs1 (by
      intro t ht
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp ht
      exact ⟨hne t h1, fun a => congrFun h2 a⟩)
    exact_mod_cast this
  refine (Finset.sum_le_sum e2).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  set Ta : Fin p → Finset E := fun a => T.image (fun t => m t a) with hTa
  have e3 : ∑ d ∈ T.image m, g d ≤ ∑ d ∈ Fintype.piFinset Ta, g d := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
      rw [Fintype.mem_piFinset]
      intro a
      exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
    · intro d _ _; exact hg0 d
  refine e3.trans ?_
  rw [← Finset.prod_univ_sum Ta (fun _ x => φ x)]
  have e4 : ∀ a ∈ (Finset.univ : Finset (Fin p)), ∑ x ∈ Ta a, φ x ≤ 16 ^ Fintype.card (InfinitePlace E) := by
    intro a _
    apply integral_points_weight_sum_le hs E
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact (hT t ht a).1
  refine (Finset.prod_le_prod (fun a _ => Finset.sum_nonneg fun x _ => hφ0 x) e4).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
end Formalism.HermitianLatticeCounting.P
