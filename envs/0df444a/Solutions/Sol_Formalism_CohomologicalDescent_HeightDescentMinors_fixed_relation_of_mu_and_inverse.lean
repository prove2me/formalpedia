-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.fixed_relation_of_mu_and_inverse
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:10.751796+00:00
-- url     : https://prove2.me/submissions/5538ee03-1e0b-4f9e-bdd6-40f06f6b22d5

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_exists_subst_of_invariant
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_prime_sub_one_pos_alt
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_binomialSeriesSubOne
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_pi0_alt
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_br_eq_X_mul_const
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_exists_mu_generator_pow_sub_one_isUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (hm : MuFacts) (h1 : R1) (hi : DivisibilityInvariant) : RootsOfUnityInvariants := by
  intro l _ O _ _ h2 f
  constructor
  · intro hf
    obtain ⟨w, hw, -⟩ := h1 l O h2
    obtain ⟨d, hd, hdu⟩ := exists_mu_generator_pow_sub_one_isUnit l hm
    obtain ⟨s, hs, hs0⟩ := br_eq_X_mul_const l O d
    have hinv : f.subst (X * s) = f := by
      rw [← hs]
      exact hf d hd
    have hP : ((w : O⟦X⟧) * X ^ (l - 1)).subst (X * s) = (w : O⟦X⟧) * X ^ (l - 1) := by
      rw [← hs, ← hw]
      exact hi l O d hd
    have hu : ∀ j, 0 < j → j < l - 1 → IsUnit (constantCoeff s ^ j - 1) := by
      intro j h0 hj
      rw [hs0]
      have := (hdu j h0 hj).map (algebraMap ℤ_[l] O)
      simpa using this
    obtain ⟨g, hg⟩ := exists_subst_of_invariant (l - 1) (prime_sub_one_pos_alt l) w s f hP hinv hu
    refine ⟨g, ?_⟩
    unfold inc
    rw [hw]
    exact hg
  · rintro ⟨g, rfl⟩ d hd
    have h := hi l O d hd
    unfold act at h
    unfold act inc
    rw [subst_comp_subst_apply (hasSubst_pi0_alt l O) (hasSubst_binomialSeriesSubOne l O d), h]
end Formalism.CohomologicalDescent.HeightDescentMinors
