-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.tails_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:48.685837+00:00
-- url     : https://prove2.me/submissions/63848cad-bc85-4f5c-a25e-2a53abab292a

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Dom_anti
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_stage_add

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
variable {D : Letters} {mu : D.Stages}
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (hD : Dom D.k (ent mu D.n0))
    (hI : ∀ j, j < D.r → Interl (D.k - (j + 1)) (stage mu (D.n0 + (j + 1))) (stage mu (D.n0 + j))) :
    ∀ j, j ≤ D.r → ∀ l, l < D.k - j →
      ent mu D.n0 (D.k - 1) ≤ stage mu (D.n0 + j) l ∧ stage mu (D.n0 + j) l ≤ ent mu D.n0 0 := by
  intro j
  induction j with
  | zero =>
    intro _ l hl
    rw [stage_add]
    simp only [Nat.add_zero] at hl ⊢
    exact ⟨hD.anti l (D.k - 1) (by omega) (by omega), hD.anti 0 l (Nat.zero_le _) (by omega)⟩
  | succ j ih =>
    intro hj l hl
    obtain ⟨h1, h2⟩ := hI j (by omega) l (by omega)
    obtain ⟨h3, h4⟩ := ih (by omega) l (by omega)
    obtain ⟨h5, h6⟩ := ih (by omega) (l + 1) (by omega)
    exact ⟨h5.trans h2, h1.trans h4⟩
end Formalism.InvariantFactorPaths.BranchingDimensions
