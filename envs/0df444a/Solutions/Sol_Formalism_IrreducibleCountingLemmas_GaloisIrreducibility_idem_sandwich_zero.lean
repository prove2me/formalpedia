-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.idem_sandwich_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:17:48.860953+00:00
-- url     : https://prove2.me/submissions/07e472fc-4517-4684-8e3e-75b16d470185

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_idem_sandwich

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {G : Type} [Group G] [Fintype G]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (J : Subgroup G) (χ : J →* ℂˣ) (u u' : J) (g : G)
    (h : (u : G) * g * u' = g) (hne : χ u * χ u' ≠ 1) :
    twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ = 0 := by
  have h1 := idem_sandwich J χ u u' g
  rw [h] at h1
  set X := twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ
  have h2 : ((1 : ℂ) - ((χ u * χ u' : ℂˣ) : ℂ)) • X = 0 := by
    rw [sub_smul, one_smul, ← h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exfalso
    apply hne
    apply Units.ext
    rw [Units.val_one]
    exact (sub_eq_zero.mp h3).symm
  · exact h3
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
