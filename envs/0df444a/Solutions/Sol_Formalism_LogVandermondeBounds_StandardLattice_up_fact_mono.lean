-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.up_fact_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:37:38.699374+00:00
-- url     : https://prove2.me/submissions/3d0ee60c-cdec-473e-b592-27f728fb2d71

import Definitions.Def_Formalism_LogVandermondeBounds_UpperPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_UpperPlaceHolds
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_up_fact_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution (N P : ℕ) (h : N ≤ P) :
    ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ) ≤ ∏ i ∈ range P, ((i.factorial : ℕ) : ℝ) := by
  induction P, h using Nat.le_induction with
  | base => exact le_refl _
  | succ P _ ih =>
    rw [Finset.prod_range_succ]
    have h0 : 1 ≤ P.factorial := Nat.factorial_pos P
    have h1 : (1 : ℝ) ≤ ((P.factorial : ℕ) : ℝ) := by exact_mod_cast h0
    have h2 : 0 ≤ ∏ i ∈ range P, ((i.factorial : ℕ) : ℝ) := le_of_lt (up_fact_pos P)
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    linarith
end Formalism.LogVandermondeBounds.StandardLattice
