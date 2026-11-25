-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.t_BoxesFit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:35:04.716861+00:00
-- url     : https://prove2.me/submissions/fbc8cd71-e7ae-4d73-8799-661d1af33d34

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_onBoxes_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : BoxesFit := by
  intro S hL h6
  have hsub : ∀ a, a < S.Ntot → S.box a ⊆ Set.Icc (S.α + (S.β - S.α) / 3) (S.β - (S.β - S.α) / 3) := by
    intro a ha x hx
    have ha' : (a:ℝ) + 1 ≤ S.Ntot := by exact_mod_cast ha
    have ha0 : (0:ℝ) ≤ a := Nat.cast_nonneg _
    obtain ⟨h1, h2⟩ := hx
    constructor
    · nlinarith
    · nlinarith
  have hdist : ∀ a b, a < b → ∀ x ∈ S.box a, ∀ y ∈ S.box b, S.L ≤ y - x := by
    intro a b hab x hx y hy
    have hab' : (a:ℝ) + 1 ≤ b := by exact_mod_cast hab
    obtain ⟨_, h2⟩ := hx
    obtain ⟨h3, _⟩ := hy
    nlinarith
  refine ⟨hsub, hdist, ?_⟩
  intro w
  induction w with
  | nil => intro _ _; exact ⟨by simp [plus], by simp [plus]⟩
  | cons Y w ih =>
    intro hOn hlen
    have hlen' : w.length < S.Ntot := by simpa [Nat.succ_le_iff] using hlen
    have hA := ih hOn.2 hlen'.le
    have hN : (1:ℝ) ≤ S.Ntot := by exact_mod_cast (by omega : 1 ≤ S.Ntot)
    have hI : 0 ≤ S.β - S.α := by nlinarith
    constructor
    · intro x hx
      simp only [plus, List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · have := hsub _ hlen' hOn.1
        exact ⟨by linarith [this.1], by linarith [this.2]⟩
      · exact hA.1 x hx
    · simp only [plus, List.map_cons, List.pairwise_cons]
      refine ⟨?_, hA.2⟩
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨a, ha, hm⟩ := onBoxes_mem S w hOn.2 y hy
      have := hdist a w.length ha y hm Y hOn.1
      show 2 < |Y - y|
      rw [abs_of_nonneg (by linarith)]
      linarith
end Formalism.FourierDecayAlt.P.LEx2
