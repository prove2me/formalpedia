-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.qdet_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:58:44.790208+00:00
-- url     : https://prove2.me/submissions/dc843159-d141-4f02-a04d-ccbf773730fc

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_qminor_rep

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
theorem _root_.solution (u : ℂ) {F : Mx k r → E} {x : Sm E k r i D} (h : Rep F x.1) (g : Mx k r)
    (hg : g ∈ Glev k r i ∩ D) :
    capL k r i u F g = (qdet (Ealg hP hC hD) u x).1 ⟨g, hg⟩ := qminor_rep hP hC hD id id u h g hg
end Formalism.FourierDecayAlt.Q.TInvW
