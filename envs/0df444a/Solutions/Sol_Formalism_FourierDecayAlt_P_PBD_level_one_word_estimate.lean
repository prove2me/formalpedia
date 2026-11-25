-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.level_one_word_estimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:39:39.632428+00:00
-- url     : https://prove2.me/submissions/30a70db7-de4d-4d82-90da-53f82186faf5

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelOneWordEstimate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
private lemma exp_le_succ_div_self_le_exp_of_le_abs {z dl : ℝ} (hdl : 8 ≤ dl) (hz : dl ≤ |z|) :
    Real.exp (-2 * (1 / dl)) ≤ (z + 1) / z ∧ (z + 1) / z ≤ Real.exp (1 / dl) := by
  have hdl0 : 0 < dl := by linarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, abs_zero] at hz
    linarith
  have hx : |1 / z| ≤ 1 / dl := by
    rw [abs_div, abs_one]
    exact one_div_le_one_div_of_le hdl0 hz
  have hx8 : 1 / dl ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hdl
  have hx0 : 0 < 1 / dl := by positivity
  rw [add_div, div_self hz0]
  have h1 := abs_le.mp hx
  constructor
  · have hexp : 1 + 2 * (1 / dl) ≤ Real.exp (2 * (1 / dl)) := by
      linarith [Real.add_one_le_exp (2 * (1 / dl))]
    have hone : Real.exp (-2 * (1 / dl)) * Real.exp (2 * (1 / dl)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hpos := Real.exp_pos (-2 * (1 / dl))
    have h2 : Real.exp (-2 * (1 / dl)) * (1 + 2 * (1 / dl)) ≤ 1 := by
      calc Real.exp (-2 * (1 / dl)) * (1 + 2 * (1 / dl))
          ≤ Real.exp (-2 * (1 / dl)) * Real.exp (2 * (1 / dl)) := mul_le_mul_of_nonneg_left hexp hpos.le
        _ = 1 := hone
    have h3 : Real.exp (-2 * (1 / dl)) ≤ 1 - 1 / dl := by
      by_contra hc
      push_neg at hc
      have h4 : (1 - 1 / dl) * (1 + 2 * (1 / dl)) < Real.exp (-2 * (1 / dl)) * (1 + 2 * (1 / dl)) :=
        mul_lt_mul_of_pos_right hc (by positivity)
      nlinarith [mul_nonneg hx0.le (by linarith : (0 : ℝ) ≤ 1 - 2 * (1 / dl))]
    linarith [h1.1]
  · linarith [Real.add_one_le_exp (1 / dl), h1.2]
private lemma exp_le_qw_div_le_exp_of_far_letters {S : Type} (q : ℝ → ℝ) (dl Y : ℝ) (hdl : 8 ≤ dl) (hq : q Y ≠ 0)
    (w : List (Letter ℝ S))
    (hw : ∀ l ∈ w, if l.plus then dl ≤ |Y - l.pt| else dl ≤ |Y - l.pt| ∧ dl ≤ |Y - (l.pt - 1)|) :
    Real.exp (-2 * (1 / dl) * w.length) ≤ qw q w Y / q Y ∧ qw q w Y / q Y ≤ Real.exp (1 / dl * w.length) := by
  induction w with
  | nil => simp [qw, div_self hq]
  | cons l w ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun l' hl' => hw l' (List.mem_cons_of_mem l hl'))
    have hl := hw l (List.mem_cons.2 (Or.inl rfl))
    obtain ⟨F, hF, hF1, hF2⟩ : ∃ F, qw q (l :: w) Y / q Y = qw q w Y / q Y * F ∧
        Real.exp (-2 * (1 / dl)) ≤ F ∧ F ≤ Real.exp (1 / dl) := by
      cases hp : l.plus
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hl
        have hz : dl ≤ |l.pt - Y - 1| := by
          rw [show l.pt - Y - 1 = -(Y - (l.pt - 1)) by ring, abs_neg]
          exact hl.2
        refine ⟨(l.pt - Y - 1 + 1) / (l.pt - Y - 1), ?_, exp_le_succ_div_self_le_exp_of_le_abs hdl hz⟩
        simp only [qw, hp, Bool.false_eq_true, ↓reduceIte]
        rw [mul_div_right_comm, show l.pt - Y - 1 + 1 = l.pt - Y by ring]
      · simp only [hp, ↓reduceIte] at hl
        refine ⟨(Y - l.pt + 1) / (Y - l.pt), ?_, exp_le_succ_div_self_le_exp_of_le_abs hdl hl⟩
        simp only [qw, hp, ↓reduceIte]
        rw [mul_div_right_comm]
    have hA : 0 < Real.exp (-2 * (1 / dl) * w.length) := Real.exp_pos _
    have hr0 : 0 ≤ qw q w Y / q Y := le_trans hA.le ih1
    have hF0 : 0 ≤ F := le_trans (Real.exp_pos _).le hF1
    rw [hF, List.length_cons]
    push_cast
    constructor
    · calc Real.exp (-2 * (1 / dl) * ((w.length : ℝ) + 1))
          = Real.exp (-2 * (1 / dl) * w.length) * Real.exp (-2 * (1 / dl)) := by
            rw [← Real.exp_add]
            ring_nf
        _ ≤ qw q w Y / q Y * F := mul_le_mul ih1 hF1 (Real.exp_pos _).le hr0
    · calc qw q w Y / q Y * F ≤ Real.exp (1 / dl * w.length) * Real.exp (1 / dl) :=
          mul_le_mul ih2 hF2 hF0 (Real.exp_pos _).le
        _ = Real.exp (1 / dl * ((w.length : ℝ) + 1)) := by
            rw [← Real.exp_add]
            ring_nf
end Formalism.FourierDecayAlt.P.PBD
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P.PBD
theorem _root_.solution : LevelOneWordEstimate := by
  intro S _ _ q w N dl Y hN hlen hdl hw hq
  have hN8 : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hdl8 : 8 ≤ dl := by nlinarith [mul_le_mul hN8 hN8 (by norm_num) (by linarith)]
  obtain ⟨h1, h2⟩ := exp_le_qw_div_le_exp_of_far_letters q dl Y hdl8 hq w hw
  have hdl0 : 0 < dl := by linarith
  have hlenR : (w.length : ℝ) ≤ N := by exact_mod_cast hlen
  have hx : (1 / dl) * w.length ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hdl0]
    nlinarith [mul_le_mul_of_nonneg_left hN8 (by linarith : (0 : ℝ) ≤ N)]
  constructor
  · calc Real.exp (-2) ≤ Real.exp (-2 * (1 / dl) * w.length) := Real.exp_le_exp.2 (by nlinarith)
      _ ≤ _ := h1
  · calc _ ≤ Real.exp (1 / dl * w.length) := h2
      _ ≤ Real.exp 2 := Real.exp_le_exp.2 (by linarith)
end Formalism.FourierDecayAlt.P.PBD
