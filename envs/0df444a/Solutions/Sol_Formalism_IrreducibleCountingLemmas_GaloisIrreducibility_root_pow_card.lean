-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.root_pow_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:40.454053+00:00
-- url     : https://prove2.me/submissions/0afd7a26-ba3c-4249-b97e-ae92fc81e78e

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRFrobOrbitIrred
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSamePartCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CoeffZeroNeZeroOfIrreducible
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
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
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {f : K[X]} (hi : Irreducible f) {x : L} (hx : aeval x f = 0) :
    x ^ Fintype.card K ^ f.natDegree = x := by
  classical
  have hxi : IsIntegral K x := (show IsAlgebraic K x from ⟨f, hi.ne_zero, hx⟩).isIntegral
  have hass := (minpoly.irreducible hxi).associated_of_dvd hi (minpoly.dvd K x hx)
  have hdeg : (minpoly K x).natDegree = f.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hass)
  haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) := IntermediateField.adjoin.finiteDimensional hxi
  haveI : Finite (IntermediateField.adjoin K {x}) := Module.finite_of_finite K
  letI : Fintype (IntermediateField.adjoin K {x}) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin K {x}) = Fintype.card K ^ f.natDegree := by
    rw [Module.card_eq_pow_finrank (K := K) (V := IntermediateField.adjoin K {x}),
      IntermediateField.adjoin.finrank hxi, hdeg]
  have h := FiniteField.pow_card
    (⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ : IntermediateField.adjoin K {x})
  rw [hcard] at h
  simpa using congrArg Subtype.val h
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
