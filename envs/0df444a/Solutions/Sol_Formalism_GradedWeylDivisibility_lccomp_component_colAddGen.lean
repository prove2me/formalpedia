-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lccomp_component_colAddGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:48.877801+00:00
-- url     : https://prove2.me/submissions/f7edb950-841c-43d8-9b16-de6ea9f719e1

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCcompLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lccomp_colAddGen_homog
import Theorems.Thm_Formalism_GradedWeylDivisibility_lccomp_sum_components
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial
noncomputable section
namespace Formalism.GradedWeylDivisibility
private lemma weightedHomogeneousComponent_self_of_isWH_ring {σ M R : Type*} [CommRing R] [AddCommMonoid M] {w : σ → M} {m : M}
    {p : MvPolynomial σ R} (h : IsWeightedHomogeneous w p m) :
    weightedHomogeneousComponent w m p = p := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · rfl
  · by_contra hne
    exact hd (h (Ne.symm hne))
private lemma weightedHomogeneousComponent_eq_zero_of_ne_isWH {σ M R : Type*} [CommRing R] [AddCommMonoid M] {w : σ → M} {m n : M}
    {p : MvPolynomial σ R} (h : IsWeightedHomogeneous w p m) (hn : n ≠ m) :
    weightedHomogeneousComponent w n p = 0 := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with hd
  · by_contra hne
    exact hn (hd.symm.trans (h hne))
  · rfl
end Formalism.GradedWeylDivisibility
end
end

set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n)
    (ω : Fin r × Fin n →₀ ℕ) (f : MvPolynomial (Fin r × Fin n) B) :
    weightedHomogeneousComponent (lccompW l j) ω (colAddGen B l j f) =
      colAddGen B l j (weightedHomogeneousComponent (pairW l j) ω f) := by
  classical
  have hf := lccomp_sum_components (pairW l j) f (f.support.image (Finsupp.weight (pairW l j)))
    (fun d hd => Finset.mem_image_of_mem _ hd)
  conv_lhs => rw [hf]
  rw [map_sum, map_sum]
  by_cases hω : ω ∈ f.support.image (Finsupp.weight (pairW l j))
  · rw [Finset.sum_eq_single ω]
    · exact weightedHomogeneousComponent_self_of_isWH_ring
        (lccomp_colAddGen_homog l j ω _ (weightedHomogeneousComponent_isWeightedHomogeneous ω f))
    · intro b _ hb
      exact weightedHomogeneousComponent_eq_zero_of_ne_isWH
        (lccomp_colAddGen_homog l j b _ (weightedHomogeneousComponent_isWeightedHomogeneous b f))
        (Ne.symm hb)
    · intro h
      exact absurd hω h
  · rw [Finset.sum_eq_zero]
    · have h0 : weightedHomogeneousComponent (pairW l j) ω f = 0 := by
        ext d
        rw [coeff_weightedHomogeneousComponent, coeff_zero]
        split_ifs with h
        · by_contra hne
          exact hω (h ▸ Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))
        · rfl
      rw [h0, map_zero]
    · intro b hb
      refine weightedHomogeneousComponent_eq_zero_of_ne_isWH
        (lccomp_colAddGen_homog l j b _ (weightedHomogeneousComponent_isWeightedHomogeneous b f)) ?_
      rintro rfl
      exact hω hb
end Formalism.GradedWeylDivisibility
