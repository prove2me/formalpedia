-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.weight_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:01:33.146537+00:00
-- url     : https://prove2.me/submissions/f782a521-4f4d-410e-b919-fd6084f2e4d9

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
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_trace_asAlgebraHom
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
theorem _root_.solution : WeightFormula := by
  intro G V _ _ _ _ _ ρ e he
  classical
  have hz : ∀ h : G, (centralIdem ρ).coeff h =
      (Module.finrank ℂ V : ℂ) / Fintype.card G * ρ.character h⁻¹ := by
    intro h
    unfold centralIdem
    rw [cip_lemma]
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (fun i => by simp)]
  simp only [mul_one, hz, inv_inv]
  have htr := trace_asAlgebraHom ρ e
  set f := ρ.asAlgebraHom e with hf
  have hff : f * f = f := by rw [hf, ← map_mul, he]
  have hproj : LinearMap.IsProj (LinearMap.range f) f :=
    ⟨fun x => LinearMap.mem_range_self f x, fun x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact congrArg (fun g : Module.End ℂ V => g y) hff⟩
  rw [hproj.trace] at htr
  have hs : ∑ h, e.coeff h * ((Module.finrank ℂ V : ℂ) / Fintype.card G * ρ.character h) =
      (Module.finrank ℂ V : ℂ) / Fintype.card G * ∑ h, e.coeff h * ρ.character h := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h _ => by ring)
  rw [hs, ← htr]
  ring
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
