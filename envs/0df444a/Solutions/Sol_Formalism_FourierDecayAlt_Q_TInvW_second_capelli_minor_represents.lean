-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.second_capelli_minor_represents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:58:45.648523+00:00
-- url     : https://prove2.me/submissions/76eca2ca-6833-49f7-ab55-bc0f58906afb

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
theorem _root_.solution (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ) {F : Mx k r → E}
    {x : Sm E k r i D} (h : Rep F x.1) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chat2L (EH k r) (posL k r i) u a a' β β' F g =
      (chat2A (Ealg hP hC hD) u (a g) (a' g) (β g) (β' g) x).1 ⟨g, hg⟩ := by
  unfold chat2L chat2A
  simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  split_ifs
  · simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [qminor_rep hP hC hD (skip2 i i') (skip2 j j') u h g hg]
  · simp
end Formalism.FourierDecayAlt.Q.TInvW
