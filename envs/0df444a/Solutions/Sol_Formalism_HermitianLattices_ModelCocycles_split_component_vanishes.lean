-- Prove2me | solution 1 for Formalism.HermitianLattices.ModelCocycles.split_component_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:57.783915+00:00
-- url     : https://prove2.me/submissions/4610082c-a4fb-4b62-9a2a-b47c5292adee

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ModelCocycleExponent
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_TeichmullerUnitAllPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ModelCocycles
open Finset Formalism.HermitianLattices.IntegralLatticeDensity
namespace Formalism.HermitianLattices.ModelCocycles
theorem _root_.solution : SplitVanish := by
  intro Z M Q _ _ _ _ _ φ a abar h1 h2 h3 hu hev h0 h22
  have symm : ∀ a b, cob φ a b = cob φ b a := by
    intro a b; unfold cob; rw [add_comm a b]; abel
  have c0 : ∀ x y, cob φ x y = 0 := by
    intro x y
    have e : (a - abar) • cob φ x y = 0 := by
      rw [sub_smul, ← h2, h3, symm x, h2, symm y, sub_self]
    obtain ⟨w, hw⟩ := hu
    have := congrArg (fun t => (↑w⁻¹ : Z) • t) e
    simpa [← hw, smul_smul] using this
  refine ⟨c0, fun u => h22 _ ?_⟩
  have := c0 u (-u)
  unfold cob at this
  rw [add_neg_cancel, h0, hev] at this
  have h : φ u + φ u = -(0 - φ u - φ u) := by abel
  rw [h, this, neg_zero]
end Formalism.HermitianLattices.ModelCocycles
