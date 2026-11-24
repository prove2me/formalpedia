-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:40:18.561794+00:00
-- url     : https://prove2.me/submissions/6425a33f-6f7f-4b3b-b89a-19d2eea10bdc

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChartIntegralLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_cont_Dmin
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_cont_Gf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Formalism.FourierDecayAlt.Q.OmPlus k r z z') := by
  have e : Formalism.FourierDecayAlt.Q.OmPlus k r z z' =
      (⋂ l : Fin (r + 2), {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0}) ∩ {g | 0 < Gf k r z z' g} := by
    ext g; simp [Formalism.FourierDecayAlt.Q.OmPlus]
  rw [e]
  refine (isOpen_iInter_of_finite fun l => ?_).inter
    (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Ux8.cont_Gf k r z z'))
  by_cases hl : l.val ≤ r
  · have e2 : {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0} = {g | Dmin k r z z' g l ≠ 0} := by
      ext g; simp [hl]
    rw [e2]; exact isOpen_ne_fun (Formalism.FourierDecayAlt.P.Ux8.cont_Dmin k r z z' l) continuous_const
  · have e2 : {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0} = Set.univ := by
      ext g; simp [hl]
    rw [e2]; exact isOpen_univ
end Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
