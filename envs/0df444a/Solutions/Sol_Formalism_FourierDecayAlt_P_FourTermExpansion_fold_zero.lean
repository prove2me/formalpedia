-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.fold_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:00:38.177377+00:00
-- url     : https://prove2.me/submissions/1ee0c092-9855-4f60-bf33-8be249f05587

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_EZ_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_EZ_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_fold_cons
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_FourTermExpansion_top_apply___a095e6ea583d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r)
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
theorem _root_.solution (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ x ∈ GV k r, fold M ts (fun _ : Mat k r => (0 : E)) x = 0 := by
  induction ts with
  | nil => intro x _; rfl
  | cons t ts ih =>
    intro x hx
    rw [fold_cons, top_apply'' M, ih x hx,
      EZ_congr (Φ₂ := fun _ => (0 : E)) isOpen_univ (Set.mem_univ x) hx (fun y _ hy => ih y hy) (M t.2.1 t.2.2),
      EZ_zero]
    simp
end Formalism.FourierDecayAlt.P.FourTermExpansion
