-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.chat_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:58:43.73155+00:00
-- url     : https://prove2.me/submissions/e64acfee-36f0-4dd8-8a77-0e93e9dcd0ee

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
theorem _root_.solution (u : ℂ) (a β : Mx k r → Fin (mdim k r i) → ℂ) {F : Mx k r → E}
    {x : Sm E k r i D} (h : Rep F x.1) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chatL (EH k r) (posL k r i) u a β F g = (chatA (Ealg hP hC hD) u (a g) (β g) x).1 ⟨g, hg⟩ := by
  unfold chatL chatA
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [qminor_rep hP hC hD (skip1 i) (skip1 j) u h g hg]
end Formalism.FourierDecayAlt.Q.TInvW
