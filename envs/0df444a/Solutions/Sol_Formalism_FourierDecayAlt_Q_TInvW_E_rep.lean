-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.E_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:36:41.033946+00:00
-- url     : https://prove2.me/submissions/710a3367-c109-4965-8b53-ccc8388514e3

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
variable (hP : EabPres) (hC : StepCongr) (hD : IsOpen D)
include hP hC hD
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution {F : Mx k r → E} {x : Sm E k r i D} (h : Rep F x.1) (a b : Fin (mdim k r i)) :
    Rep (EH k r (posL k r i a) (posL k r i b) F) (Ealg hP hC hD a b x).1 := by
  intro g hg
  show EH k r (posL k r i a) (posL k r i b) F g = EH k r (posL k r i a) (posL k r i b) (ext k r i D x.1) g
  exact hC E k r i D a b F (ext k r i D x.1) g hD hg (fun y hy => by rw [h y hy, ext_at hy])
end Formalism.FourierDecayAlt.Q.TInvW
