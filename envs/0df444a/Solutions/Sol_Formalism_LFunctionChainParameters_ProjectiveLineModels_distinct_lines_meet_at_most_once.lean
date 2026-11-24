-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.distinct_lines_meet_at_most_once
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:30:35.133258+00:00
-- url     : https://prove2.me/submissions/daa5f3bf-dd38-4d67-8bd0-1d6fb0753abc

import Definitions.Def_Formalism_SizeWindowBrackets_JointDPublishedSizes
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ProjectiveLineModels
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)
open Formalism.LFunctionChainParameters.MatrixLatticeEstimates
variable (p : ℕ) [Fact p.Prime]
namespace Formalism.LFunctionChainParameters.ProjectiveLineModels
theorem _root_.solution (i j : Option (ZMod p) × ZMod p) (hij : i ≠ j) (t t' s s' : ZMod p)
    (h1 : linePt p i t = linePt p j t') (h2 : linePt p i s = linePt p j s') : t = s ∧ t' = s' := by
  rcases i with ⟨_ | m, b⟩ <;> rcases j with ⟨_ | m', b'⟩ <;> simp [linePt] at h1 h2 hij ⊢
  · exact absurd h1.1 hij
  · obtain ⟨a1, a2⟩ := h1
    obtain ⟨c1, c2⟩ := h2
    subst a1
    subst c1
    exact ⟨by rw [a2, c2], rfl⟩
  · obtain ⟨a1, a2⟩ := h1
    obtain ⟨c1, c2⟩ := h2
    subst a1
    subst c1
    exact ⟨rfl, by rw [← a2, ← c2]⟩
  · obtain ⟨a1, a2⟩ := h1
    obtain ⟨c1, c2⟩ := h2
    subst a1
    subst c1
    by_cases hm : m = m'
    · subst hm
      exact absurd (add_left_cancel a2) (hij rfl)
    · have h3 : (m - m') * (t - s) = 0 := by linear_combination a2 - c2
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd (sub_eq_zero.1 h4) hm
      · exact ⟨sub_eq_zero.1 h4, sub_eq_zero.1 h4⟩
end Formalism.LFunctionChainParameters.ProjectiveLineModels
