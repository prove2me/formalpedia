-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.ybv_sg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:57:54.343785+00:00
-- url     : https://prove2.me/submissions/62851536-5ad3-4a7c-90d9-c6e9fd9dccdb

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_SecondCapelliMinorContinuousLinear
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_entry_cd
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
private lemma contDiff_mul_left_apply (H : Mx k r) (a b : Fin (2 * r + k + 1)) :
    ContDiff ℝ ∞ (fun g : Mx k r => (H * g) a b) := by
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun c _ => contDiff_const.mul (entry_cd c b)
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
    SmoothG k r i (fun g => ybv k r z i g j) := by
  refine ⟨fun g => ybv k r z i g j, ?_, fun _ _ => rfl⟩
  simp only [ybv, herm, dotProduct, Matrix.mulVec_mulVec]
  exact ContDiff.sum fun x _ => contDiff_const.mul (contDiff_mulVec_apply_of_contDiff (contDiff_mul_left_apply (Hpk k r)) _ x)
end Formalism.FourierDecayAlt.Q.TPresMain
