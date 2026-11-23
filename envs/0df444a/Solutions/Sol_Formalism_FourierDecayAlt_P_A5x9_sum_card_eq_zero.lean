-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.sum_card_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:38.733261+00:00
-- url     : https://prove2.me/submissions/1e06aaf6-6b01-4c77-a03b-8673931bd111

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
open Classical
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution {α X : Type} (F : Finset α) (Φ : α → ℂ) (rel : X → α → Prop)
    (hfin : ∀ q ∈ F, Finite {x // rel x q})
    (h0 : ∀ x, ∑ q ∈ F.filter (fun q => rel x q), Φ q = 0) :
    ∑ q ∈ F, (Nat.card {x // rel x q} : ℂ) * Φ q = 0 := by
  have hT : (⋃ q ∈ F, {x | rel x q}).Finite := by
    apply Set.Finite.biUnion F.finite_toSet
    intro q hq
    have : Finite ({x | rel x q} : Set X) := hfin q hq
    exact Set.toFinite {x | rel x q}
  let U : Finset X := hT.toFinset
  have hU : ∀ q ∈ F, ∀ x, rel x q → x ∈ U := by
    intro q hq x hx
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_biUnion hq hx
  have hc : ∀ q ∈ F, (Nat.card {x // rel x q} : ℂ) * Φ q =
      ∑ x ∈ U, if rel x q then Φ q else 0 := by
    intro q hq
    rw [Nat.subtype_card (U.filter (fun x => rel x q))
      (fun x => by rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hU q hq x h, h⟩⟩),
      ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hc, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro x _
  rw [← Finset.sum_filter]
  exact h0 x
end Formalism.FourierDecayAlt.P.A5x9
