-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.second_capelli_minor_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:28:26.58159+00:00
-- url     : https://prove2.me/submissions/43a3457b-bf80-4acd-87a1-f4abc4f7f901

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_SecondCapelliMinorContinuousLinear
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_qminor_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_sg_const
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_sg_mul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_sg_sub
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_sl_smul_fun
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_sl_zero
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_TPresMain_sl_sum__cd5de3938d2f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.Q.TPresMain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
section Ops
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
private lemma smoothLev_ite_zero (P : Prop) [Decidable P] {F : Mx k r → E} (hF : P → SmoothLev k r i D F) :
    SmoothLev k r i D (fun g => if P then F g else 0) := by
  by_cases hP : P
  · simp only [hP, ↓reduceIte]
    exact hF hP
  · simp only [hP, ↓reduceIte]
    exact sl_zero
end Ops
end Formalism.FourierDecayAlt.Q.TPresMain
end
end

set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresMain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.Q.TPresMain
theorem _root_.solution (hD : IsOpen D) (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ)
    (ha : ∀ j, SmoothG k r i (fun g => a g j)) (ha' : ∀ j, SmoothG k r i (fun g => a' g j))
    (hβ : ∀ j, SmoothG k r i (fun g => β g j)) (hβ' : ∀ j, SmoothG k r i (fun g => β' g j))
    (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (chat2L (EH k r) (posL k r i) u a a' β β' f) := by
  unfold chat2L
  exact sl_sum' _ fun i0 => sl_sum' _ fun i1 => sl_sum' _ fun j0 => sl_sum' _ fun j1 =>
    smoothLev_ite_zero _ fun _ => sl_smul_fun
      (sg_mul (sg_mul (sg_const _) (sg_sub (sg_mul (hβ i0) (hβ' i1)) (sg_mul (hβ i1) (hβ' i0))))
        (sg_sub (sg_mul (ha j0) (ha' j1)) (sg_mul (ha j1) (ha' j0))))
      (qminor_smooth hD _ _ u f hf)
end Formalism.FourierDecayAlt.Q.TPresMain
