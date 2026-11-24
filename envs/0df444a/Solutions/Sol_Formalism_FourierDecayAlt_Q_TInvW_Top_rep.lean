-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.Top_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:55:19.619159+00:00
-- url     : https://prove2.me/submissions/172886bb-eb2c-49be-8cac-9b9917916e93

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_posL_inj
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_E_rep

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
theorem _root_.solution {F : Mx k r → E} {x : Sm E k r i D} (h : Rep F x.1) (u : ℂ)
    (a b : Fin (mdim k r i)) :
    Rep (Formalism.QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) F) (Tm (Ealg hP hC hD) u a b x).1 := by
  intro g hg
  have h2 := E_rep hP hC hD h a b g hg
  by_cases hab : a = b
  · subst hab
    simp [Formalism.QuantumDeterminants.Top, Tm, h g hg, h2]
  · have hne : posL k r i a ≠ posL k r i b := fun e => hab (posL_inj e)
    simp [Formalism.QuantumDeterminants.Top, Tm, hab, hne, h2]
end Formalism.FourierDecayAlt.Q.TInvW
