-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.pieriDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:43:54.428797+00:00
-- url     : https://prove2.me/submissions/d7e6be8a-dea0-4844-b970-6aee6ab20319

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_TTotal
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_finsum_prop_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_star_star
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_hstrip_star
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_dom_star
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_wsize_star
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_weylDim_star

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
open Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
namespace Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
theorem _root_.solution (hP : PieriDim) (n : ℕ) (mu : Fin n → ℤ) (B : ℕ) (hn : 1 ≤ n) (hd : Dom n (extW mu)) :
    ∑ᶠ (mu' : Fin n → ℤ) (_ : HStrip n (extW mu') (extW mu) ∧ wsize n (extW mu) - wsize n (extW mu') = B),
      weylDim n (extW mu') = weylDim n (extW mu) * ((B + n - 1).choose (n - 1) : ℝ) := by
  have h := hP n (star mu) B hn (dom_star hd)
  rw [weylDim_star] at h
  rw [← h]
  let e : (Fin n → ℤ) ≃ (Fin n → ℤ) := Function.Involutive.toPerm star star_star
  have h2 := finsum_comp_equiv e (f := fun z : Fin n → ℤ =>
    ∑ᶠ (_ : HStrip n (extW (star mu)) (extW z) ∧ wsize n (extW z) - wsize n (extW (star mu)) = B),
      weylDim n (extW z))
  rw [← h2]
  refine (finsum_prop_congr (fun y => ?_) (fun y _ => ?_)).symm
  · show HStrip n (extW (star mu)) (extW (star y)) ∧ _ ↔ _
    have e1 : e y = star y := rfl
    rw [e1, wsize_star, wsize_star]
    constructor
    · rintro ⟨h1, h3⟩
      have := hstrip_star h1
      rw [star_star, star_star] at this
      exact ⟨this, by omega⟩
    · rintro ⟨h1, h3⟩
      exact ⟨hstrip_star h1, by omega⟩
  · show weylDim n (extW (star y)) = _
    exact weylDim_star y
end Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
