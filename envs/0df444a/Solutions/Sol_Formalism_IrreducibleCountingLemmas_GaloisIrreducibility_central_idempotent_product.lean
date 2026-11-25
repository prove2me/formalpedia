-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.central_idempotent_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:06:34.125798+00:00
-- url     : https://prove2.me/submissions/a777209a-5eaf-4223-9640-fa715eb735a0

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


section
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
private theorem cip_lemma {G : Type} [Group G] [Fintype G] (c : G → ℂ) (x : G) :
    (∑ y, c y • MonoidAlgebra.of ℂ G y).coeff x = c x := by
  classical
  rw [MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, Finset.sum_eq_single x]
  · simp [MonoidAlgebra.coeff_smul, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single]
  · intro b _ hb
    simp [MonoidAlgebra.coeff_smul, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, hb]
  · simp
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Polynomial Formalism.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Polynomial
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Polynomial
section aux
variable {α β : Type} [Fintype α]
end aux
section prod
variable {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
end prod
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Polynomial
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

set_option autoImplicit false
open Finset Polynomial
open scoped ComplexOrder
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : CentralIdemProduct := by
  intro G H V W _ _ _ _ _ _ _ _ _ _ ρ σ g h
  unfold centralIdem
  rw [cip_lemma, cip_lemma, cip_lemma, Representation.char_tensor]
  have e3 : Module.finrank ℂ (TensorProduct ℂ V W) = Module.finrank ℂ V * Module.finrank ℂ W :=
    Module.finrank_tensorProduct
  rw [e3, Fintype.card_prod]
  show ((Module.finrank ℂ V * Module.finrank ℂ W : ℕ) : ℂ) / ((Fintype.card G * Fintype.card H : ℕ) : ℂ) *
      (ρ.character g⁻¹ * σ.character h⁻¹) =
    (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * ρ.character g⁻¹ *
      ((Module.finrank ℂ W : ℂ) / (Fintype.card H : ℂ) * σ.character h⁻¹)
  push_cast
  ring
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
