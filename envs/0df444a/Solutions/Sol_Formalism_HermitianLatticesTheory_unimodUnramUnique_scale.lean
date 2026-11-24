-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.unimodUnramUnique_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:43:19.1688+00:00
-- url     : https://prove2.me/submissions/dc8b5746-3574-445e-a270-7ac960f1537d

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementJac
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_hermFix
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
open Polynomial IsLocalRing Matrix
variable {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R}
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution [HenselianLocalRing R₀] [Finite (ResidueField R₀)]
    (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ))
    {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) (hA : Aᴴ = A) (i : ι)
    (hi : IsUnit (A i i)) : ∃ g : Matrix ι ι R, IsUnit g.det ∧ (gᴴ * A * g) i i = 1 := by
  have hfix := unimodUnramUnique_hermFix A hA i i
  obtain ⟨v, hv⟩ := hi.exists_right_inv
  have h1 : star v * A i i = 1 := by
    have := congrArg star hv; rwa [star_mul, hfix, star_one] at this
  have hvfix : star v = v := by
    calc star v = star v * (A i i * v) := by rw [hv, mul_one]
      _ = (star v * A i i) * v := by ring
      _ = v := by rw [h1, one_mul]
  have hvu : IsUnit v := isUnit_iff_exists_inv.2 ⟨A i i, by rw [mul_comm]; exact hv⟩
  obtain ⟨w, hw⟩ := unimodUnramUnique_norm hR₀ hθ hvfix hvu
  have hwu : IsUnit w := isUnit_of_mul_isUnit_right (hw ▸ hvu)
  refine ⟨diagonal (Function.update 1 i w), ?_, ?_⟩
  · rw [det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simpa using hwu
  · rw [diagonal_conjTranspose]
    simp [diagonal_mul, mul_diagonal]
    linear_combination (A i i) * hw + hv
end Formalism.HermitianLatticesTheory
