-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.contDiff_dm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:30:35.135128+00:00
-- url     : https://prove2.me/submissions/97984c0e-2e5d-4257-b3c8-8b4da5353662

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MpFOne
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_HasFDerivAtOrb
import Theorems.Thm_CompanionTheory_ThKR_LL_Intw_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_Intw_smul
import Theorems.Thm_CompanionTheory_ThKR_LL_Iso_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKR.Mp
theorem _root_.solution {k : ℕ} (γ : (Fin k → ℝ) → G l)
    (hs : ∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Mat l) a b) (a b : l ⊕ l) (n : ℕ) :
    ContDiff ℝ n fun t => dm γ t a b := by
  have hinv : ∀ a c, ContDiff ℝ ∞ fun t => ((pr (γ t))⁻¹ : Sp l).1 a c := by
    intro a c
    have e : (fun t => ((pr (γ t))⁻¹ : Sp l).1 a c) =
        fun t => ∑ e, (∑ d, (-J l ℝ) a d * (pr (γ t) : Mat l) e d) * J l ℝ e c := by
      funext t
      show ((-J l ℝ) * (pr (γ t) : Mat l)ᵀ * J l ℝ) a c = _
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [e]
    exact ContDiff.sum fun e _ => (ContDiff.sum fun d _ => contDiff_const.mul (hs e d)).mul contDiff_const
  have hn : ((n : WithTop ℕ∞)) ≤ ∞ := by exact_mod_cast le_top
  have hn1 : ((n : WithTop ℕ∞)) + 1 ≤ ∞ := by exact_mod_cast le_top
  unfold dm
  exact ContDiff.sum fun c _ => ((hinv a c).of_le hn).smul ((hs c b).fderiv_right hn1)
end CompanionTheory.ThKR.Mp
