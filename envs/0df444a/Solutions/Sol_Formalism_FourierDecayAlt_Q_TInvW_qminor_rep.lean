-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.qminor_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:40:19.783665+00:00
-- url     : https://prove2.me/submissions/8772014c-73a8-49cd-a6d5-fbc3aa2480ea

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_foldr_rep
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_qminor_apply

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
theorem _root_.solution {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) {F : Mx k r → E}
    {x : Sm E k r i D} (h : Rep F x.1) :
    Rep (qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u F) (qminor (Ealg hP hC hD) a b u x).1 := by
  intro g hg
  rw [qminor_apply hP hC hD a b u x]
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have hf := foldr_rep hP hC hD (List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)) h g hg
  simpa [List.map_ofFn, Function.comp_def] using hf
end Formalism.FourierDecayAlt.Q.TInvW
