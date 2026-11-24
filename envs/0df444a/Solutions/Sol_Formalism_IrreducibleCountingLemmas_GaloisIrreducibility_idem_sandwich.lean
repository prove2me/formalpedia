-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.idem_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:00:53.900561+00:00
-- url     : https://prove2.me/submissions/e749a55a-94c2-4df5-a574-2a979f5fa116

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_twistedIdem_mul_of
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_of_mul_twistedIdem
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {G : Type} [Group G] [Fintype G]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (J : Subgroup G) (χ : J →* ℂˣ) (u u' : J) (g : G) :
    twistedIdem J χ * MonoidAlgebra.of ℂ G ((u : G) * g * u') * twistedIdem J χ =
      (((χ u * χ u' : ℂˣ)) : ℂ) •
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) := by
  rw [map_mul, map_mul]
  calc twistedIdem J χ * (MonoidAlgebra.of ℂ G (u : G) * MonoidAlgebra.of ℂ G g *
        MonoidAlgebra.of ℂ G (u' : G)) * twistedIdem J χ
      = (twistedIdem J χ * MonoidAlgebra.of ℂ G (u : G)) * MonoidAlgebra.of ℂ G g *
        (MonoidAlgebra.of ℂ G (u' : G) * twistedIdem J χ) := by simp only [mul_assoc]
    _ = _ := by
      rw [twistedIdem_mul_of, of_mul_twistedIdem, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
        smul_smul, Units.val_mul]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
