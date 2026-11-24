-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.yv_sg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:35:05.735165+00:00
-- url     : https://prove2.me/submissions/6d4566c5-1880-487a-abd2-80a605041ff4

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_SecondCapelliMinorContinuousLinear
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_entry_cd
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_inv_glev
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
private lemma contDiff_mulVec_apply_of_contDiff {M : Mx k r → Mx k r} (hM : ∀ a b, ContDiff ℝ ∞ (fun g => M g a b))
    (v : (Fin (2 * r + k + 1) → ℂ)) (p : Fin (2 * r + k + 1)) : ContDiff ℝ ∞ (fun g => (M g *ᵥ v) p) := by
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiff.sum fun q _ => (hM p q).mul contDiff_const
private lemma contDiff_hpk_conjTranspose_hpk_apply (a b : Fin (2 * r + k + 1)) :
    ContDiff ℝ ∞ (fun g : Mx k r => (Hpk k r * gᴴ * Hpk k r) a b) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hs : ∀ c d : Fin (2 * r + k + 1), ContDiff ℝ ∞ (fun g : Mx k r => star (g c d)) :=
    fun c d => Complex.conjCLE.contDiff.comp (entry_cd c d)
  exact ContDiff.sum fun c _ => (ContDiff.sum fun d _ => contDiff_const.mul (hs c d)).mul contDiff_const
section Ops
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
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
namespace Formalism.FourierDecayAlt.Q.TPresMain
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (j : Fin (mdim k r i)) :
    SmoothG k r i (fun g => yv k r z i g j) := by
  refine ⟨fun g => ((Hpk k r * gᴴ * Hpk k r) *ᵥ fvec k r z i) (posL k r i j), ?_, fun g hg => ?_⟩
  · exact contDiff_mulVec_apply_of_contDiff contDiff_hpk_conjTranspose_hpk_apply _ _
  · simp only [yv, inv_glev hg]
end Formalism.FourierDecayAlt.Q.TPresMain
