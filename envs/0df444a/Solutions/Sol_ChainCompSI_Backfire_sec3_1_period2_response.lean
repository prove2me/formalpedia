-- Prove2me | solution 1 for ChainCompSI.Backfire.sec3_1_period2_response
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:01:14.359985+00:00
-- url     : https://prove2.me/submissions/4044ed6f-33a5-43c1-807e-38b64e754f3e

import Mathlib
import Definitions.Def_ChainCompSI_Backfire_Model

open ChainCompSI.Backfire in
theorem solution (θ h : ℝ) (hθ : 0 < θ) (hh : 0 ≤ h) (si : Fin 2 → Bool) (E : Profile) (hE : IsEq θ h si E) (i : Fin 2) (H : Hist) (hI : 0 ≤ H.I) (w : ℝ) (hw : 0 ≤ w) (hrep : 2 * H.I < 1 + θ * E.p2' (rival i) - (1 + θ) * w) : E.p2 i H w = (1 + θ * E.p2' (rival i) + (1 + θ) * w) / (2 * (1 + θ)) ∧ demand θ (E.p2 i H w) (E.p2' (rival i)) = (1 + θ * E.p2' (rival i) - (1 + θ) * w) / 2 := by
  have hopt := (hE.1 i H hI w hw)
  obtain ⟨a, ha⟩ : ∃ a, a = E.p2' (rival i) := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = E.p2 i H w := ⟨_, rfl⟩
  rw [← ha, ← hp] at hopt ⊢
  rw [← ha] at hrep
  obtain ⟨hp0, hmax⟩ := hopt
  have hk : 0 < 1 + θ := by linarith
  obtain ⟨qs, hqsdef⟩ : ∃ qs, qs = (1 + θ * a + (1 + θ) * w) / (2 * (1 + θ)) := ⟨_, rfl⟩
  have hqs : 2 * (1 + θ) * qs = 1 + θ * a + (1 + θ) * w := by
    rw [hqsdef]; field_simp
  have hdem : ∀ q, demand θ q a = 1 + θ * a - (1 + θ) * q := by
    intro q; unfold demand; ring
  have hDqs : demand θ qs a = (1 + θ * a - (1 + θ) * w) / 2 := by
    rw [hdem]; linarith
  have hqs0 : 0 ≤ qs := by nlinarith
  have hDpos : H.I < demand θ qs a := by rw [hDqs]; linarith
  have hRqs : retP2 θ a H.I w qs = qs * demand θ qs a - w * (demand θ qs a - H.I) := by
    unfold retP2 sales
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
  have hle := hmax qs hqs0
  rw [hRqs] at hle
  have hgap : 0 < qs - w := by nlinarith
  have hfq : 0 < qs * demand θ qs a - w * (demand θ qs a - H.I) := by
    nlinarith [mul_pos hgap (lt_of_le_of_lt hI hDpos)]
  have hpeq : p = qs := by
    by_cases hneg : demand θ p a < 0
    · exfalso
      have : retP2 θ a H.I w p = 0 := by
        unfold retP2 sales
        rw [max_eq_right hneg.le, zero_sub, max_eq_right (by linarith)]
        ring
      linarith
    · push_neg at hneg
      have hR : retP2 θ a H.I w p ≤ p * demand θ p a - w * (demand θ p a - H.I) := by
        unfold retP2 sales
        rw [max_eq_left hneg]
        have := le_max_left (demand θ p a - H.I) 0
        nlinarith
      rw [hdem p] at hR
      rw [hdem qs] at hle
      have hid : (qs * (1 + θ * a - (1 + θ) * qs) - w * ((1 + θ * a - (1 + θ) * qs) - H.I)) -
          (p * (1 + θ * a - (1 + θ) * p) - w * ((1 + θ * a - (1 + θ) * p) - H.I)) =
          (1 + θ) * (p - qs) ^ 2 := by
        linear_combination (p - qs) * hqs
      have hsq : (1 + θ) * (p - qs) ^ 2 ≤ 0 := by linarith
      have : (p - qs) ^ 2 ≤ 0 := by
        by_contra hc
        push_neg at hc
        have := mul_pos hk hc
        linarith
      have : p - qs = 0 := by nlinarith [sq_nonneg (p - qs)]
      linarith
  refine ⟨hpeq.trans hqsdef, ?_⟩
  rw [hpeq, hDqs]
