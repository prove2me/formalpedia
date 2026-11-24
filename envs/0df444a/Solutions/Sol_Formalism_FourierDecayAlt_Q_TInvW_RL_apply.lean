-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.RL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:55:00.992908+00:00
-- url     : https://prove2.me/submissions/505d1a98-9174-496a-ad43-6dc54759bb9d

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
variable {s' : Mx k r} (hs' : ∀ g ∈ Glev k r i ∩ D, g * s' ∈ Glev k r i ∩ D)
variable (hRS : StepRSm) (hs'G : s' ∈ Glev k r i)
include hRS hs'G
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution (M M' : Module.End ℂ (Sm E k r i D)) (hM : M * RL (E := E) hP hC hD hs' hRS hs'G = RL (E := E) hP hC hD hs' hRS hs'G * M')
    (x : Sm E k r i D) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    (M (RL hP hC hD hs' hRS hs'G x)).1 ⟨g, hg⟩ = (M' x).1 ⟨g * s', hs' g hg⟩ := congrArg (fun T : Module.End ℂ (Sm E k r i D) => (T x).1 ⟨g, hg⟩) hM
end Formalism.FourierDecayAlt.Q.TInvW
