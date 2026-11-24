-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.costV_ok
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:23.782899+00:00
-- url     : https://prove2.me/submissions/1017d52b-4290-4133-b484-c3b2101d049e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Theorems.Thm_Formalism_MainNotions_PlaneGram_Slope_one
import Theorems.Thm_Formalism_MainNotions_PlaneGram_Slope_mul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_one_fun
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_mul_fun
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_add_fun
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_smul_fun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
open MvPolynomial
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (fam : Set (Finset L))
    (hadd : ∀ S ∈ fam, ∀ (θ : ℝ) (F G : MvPolynomial (L × Fin r) K),
      vala sg S θ F → vala sg S θ G → vala sg S θ (F + G))
    (hsmul : ∀ S ∈ fam, ∀ (θ : ℝ) (a : K) (F : MvPolynomial (L × Fin r) K),
      vala sg S θ F → vala sg S θ (a • F)) :
    CostOK (CostV (K := K) (r := r) sg fam) where
  one := by
    intro S _ θ F h
    rw [dg_one_fun]; simpa using h
  mul := by
    intro m n f g hf hg S hS θ F h
    rw [dg_mul_fun]
    have := hf S hS _ _ (hg S hS θ F h)
    have e : θ - ((m + n : ℕ) : ℝ) = θ - n - m := by push_cast; ring
    rw [e]; exact this
  add := by
    intro n f g hf hg S hS θ F h
    rw [dg_add_fun]
    exact hadd S hS _ _ _ (hf S hS θ F h) (hg S hS θ F h)
  smul := by
    intro n a f hf S hS θ F h
    rw [dg_smul_fun]
    exact hsmul S hS _ _ _ (hf S hS θ F h)
  mono := by
    intro m n f hmn hf S hS θ F h
    have h1 := hf S hS θ F h
    unfold vala at h1 ⊢
    refine le_trans ?_ h1
    have : θ - (n : ℝ) ≤ θ - (m : ℝ) := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    exact_mod_cast this
end Formalism.MainNotions.PlaneGram
