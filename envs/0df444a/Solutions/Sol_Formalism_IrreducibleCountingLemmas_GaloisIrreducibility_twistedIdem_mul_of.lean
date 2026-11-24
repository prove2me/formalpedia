-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem_mul_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:51:59.776255+00:00
-- url     : https://prove2.me/submissions/843b0c57-6382-4b62-8911-4588f0cc404e

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_twistedIdem_def
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
open Classical
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (J : Subgroup G) (χ : J →* ℂˣ)
    (v : J) : twistedIdem J χ * MonoidAlgebra.of ℂ G (v : G)
      = ((χ v : ℂˣ) : ℂ) • twistedIdem J χ := by
  rw [twistedIdem_def, Finset.sum_mul, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight v) _ _ (fun u => ?_)
  simp only [Equiv.coe_mulRight, smul_mul_assoc, ← map_mul, smul_smul, Subgroup.coe_mul]
  congr 1
  have h1 : ((χ v : ℂˣ) : ℂ) ≠ 0 := (χ v).ne_zero
  have h2 : ((χ u : ℂˣ) : ℂ) ≠ 0 := (χ u).ne_zero
  rw [map_mul, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
  field_simp
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
