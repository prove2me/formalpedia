-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.lord_nonneg_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:08:28.225935+00:00
-- url     : https://prove2.me/submissions/bb531d0b-9426-4099-a9d5-940e9c5711e7

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {R : Type} [CommRing R] (f : LaurentPolynomial R)
    (hf : f ∈ (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R).range) : 0 ≤ lord f := by
  obtain ⟨q, rfl⟩ := hf
  unfold lord
  apply Finset.le_min
  intro n hn
  rw [LaurentPolynomial.support_coeff_toLaurent] at hn
  simp only [Finset.mem_map, Nat.castEmbedding_apply] at hn
  obtain ⟨m, -, rfl⟩ := hn
  exact_mod_cast Nat.zero_le m
end Formalism.MainNotions.PlaneGram
