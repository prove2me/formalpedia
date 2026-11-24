-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_foldr_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:50:44.262297+00:00
-- url     : https://prove2.me/submissions/5adf8b97-0cac-4a02-923c-b090995c3ad1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {X : Type*} [AddCommGroup X] [Module ℂ X] (L : List (X → X))
    (hL : ∀ T ∈ L, IsLinearMap ℂ T) : IsLinearMap ℂ (fun x => L.foldr (fun T h => T h) x) := by
  induction L with
  | nil => exact ⟨fun x y => rfl, fun c x => rfl⟩
  | cons T L ih =>
    have hT := hL T (by simp)
    have ih' := ih (fun S hS => hL S (by simp [hS]))
    refine ⟨fun x y => ?_, fun c x => ?_⟩
    · have e1 := ih'.map_add x y
      have e2 := hT.map_add (List.foldr (fun T h => T h) x L) (List.foldr (fun T h => T h) y L)
      try simp only at e1
      simp only [List.foldr_cons, e1, e2]
    · have e1 := ih'.map_smul c x
      have e2 := hT.map_smul c (List.foldr (fun T h => T h) x L)
      try simp only at e1
      simp only [List.foldr_cons, e1, e2]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
