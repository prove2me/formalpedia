-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sum_coef_twisted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:52:05.049437+00:00
-- url     : https://prove2.me/submissions/1fca0c10-aeab-487a-964b-7d6248504965

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_PropositionOneCentralCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRDivisorDegreeSubSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartEqIff
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRTypeCountExact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleTypeProb
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open scoped ComplexOrder
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Classical
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {G : Type} [Group G] [Fintype G] (J : Subgroup G) (χ : J →* ℂˣ) :
    ∑ u : J, ((Nat.card J : ℂ)⁻¹ * (((χ u)⁻¹ : ℂˣ) : ℂ)) * ((χ u : ℂˣ) : ℂ) = 1 := by
  have h0 : (Nat.card J : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := J)).ne'
  calc ∑ u : J, ((Nat.card J : ℂ)⁻¹ * (((χ u)⁻¹ : ℂˣ) : ℂ)) * ((χ u : ℂˣ) : ℂ)
      = ∑ _u : J, (Nat.card J : ℂ)⁻¹ := by
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [mul_assoc, Units.inv_mul, mul_one]
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul,
          mul_inv_cancel₀ h0]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
