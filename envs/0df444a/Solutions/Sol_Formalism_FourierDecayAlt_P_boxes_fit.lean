-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.boxes_fit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:12.354976+00:00
-- url     : https://prove2.me/submissions/cbc0b6c1-0fba-42c0-a9df-45ae3a9bb360

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivedCoefficientIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
private theorem le_boxesFit_proof : Formalism.FourierDecayAlt.LE.BoxesFit := by
  intro S hL hfit
  have hL0 : 0 < S.L := by linarith
  have hN0 : (0:ℝ) ≤ S.Ntot := Nat.cast_nonneg _
  have hαβ : S.α ≤ S.β := by nlinarith [mul_nonneg hN0 hL0.le]
  have hmid : ∀ a, a < S.Ntot →
      S.box a ⊆ Set.Icc (S.α + (S.β - S.α) / 3) (S.β - (S.β - S.α) / 3) := by
    intro a ha x hx
    have ha1 : a + 1 ≤ S.Ntot := ha
    have ha' : (a:ℝ) + 1 ≤ S.Ntot := by exact_mod_cast ha1
    have ha0 : (0:ℝ) ≤ a := Nat.cast_nonneg _
    obtain ⟨hx1, hx2⟩ := hx
    have h1 : 0 ≤ 2 * (a:ℝ) * S.L := by positivity
    have h2 := mul_le_mul_of_nonneg_right ha' hL0.le
    constructor
    · linarith
    · nlinarith
  have hsep : ∀ a b, a < b → ∀ x ∈ S.box a, ∀ y ∈ S.box b, S.L ≤ y - x := by
    intro a b hab x hx y hy
    have hab1 : a + 1 ≤ b := hab
    have hab' : (a:ℝ) + 1 ≤ b := by exact_mod_cast hab1
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    nlinarith [mul_le_mul_of_nonneg_right hab' hL0.le]
  refine ⟨hmid, hsep, ?_⟩
  have hmem : ∀ w : List ℝ, S.OnBoxes w → ∀ Z ∈ w, ∃ j, j < w.length ∧ Z ∈ S.box j := by
    intro w
    induction w with
    | nil =>
      intro _ Z hZ
      simp at hZ
    | cons Y w ih =>
      intro hOn Z hZ
      have hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w := hOn
      rcases List.mem_cons.mp hZ with rfl | hZ'
      · exact ⟨w.length, by simp only [List.length_cons]; omega, hOn'.1⟩
      · obtain ⟨j, hj, hZj⟩ := ih hOn'.2 Z hZ'
        exact ⟨j, by simp only [List.length_cons]; omega, hZj⟩
  have hin : ∀ j, j < S.Ntot → ∀ x ∈ S.box j, x ∈ Set.Icc S.α S.β := by
    intro j hj x hx
    have hx' := hmid j hj hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  intro w
  induction w with
  | nil =>
    intro _ _
    refine ⟨fun x hx => ?_, List.Pairwise.nil⟩
    simp [Formalism.FourierDecayAlt.LE.plus] at hx
  | cons Y w ih =>
    intro hOn hlen
    have hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w := hOn
    have hlen' : w.length < S.Ntot := by
      simp only [List.length_cons] at hlen
      omega
    obtain ⟨ih1, ih2⟩ := ih hOn'.2 (by omega)
    show (∀ x ∈ (true, Y) :: Formalism.FourierDecayAlt.LE.plus w, x.2 ∈ Set.Icc S.α S.β) ∧
      ((true, Y) :: Formalism.FourierDecayAlt.LE.plus w).Pairwise fun x y => 2 < |x.2 - y.2|
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hin _ hlen' _ hOn'.1
      · exact ih1 x hx'
    · refine List.Pairwise.cons ?_ ih2
      intro z hz
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hz
      obtain ⟨j, hj, hZj⟩ := hmem w hOn'.2 Z hZ
      have hd := hsep j w.length hj Z hZj Y hOn'.1
      show 2 < |Y - Z|
      rw [abs_of_pos (by linarith)]
      linarith
end Formalism.FourierDecayAlt.P.LEx2
end

set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.LE.BoxesFit := Formalism.FourierDecayAlt.P.LEx2.le_boxesFit_proof
end Formalism.FourierDecayAlt.P
