-- Prove2me | solution 1 for FreemiumActions.Threshold.proposition_5
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:15:24.092325+00:00
-- url     : https://prove2.me/submissions/17db1c98-f615-4a2a-b9af-bb2e05e627d5

import Mathlib
import Definitions.Def_FreemiumActions_Threshold_Effects
open scoped ENNReal
open FreemiumActions.Threshold

namespace S228FR5

lemma sum_pa (g : PlayerAction → ℝ) :
    ∑ a, g a = g .monetize + g .incented + g .quit := by
  rw [show (Finset.univ : Finset PlayerAction) = {.monetize, .incented, .quit} from rfl]
  simp [Finset.sum_insert, add_assoc]

lemma geo (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) :
    ∑' t : ℕ, (ENNReal.ofReal x) ^ t = ENNReal.ofReal (1 / (1 - x)) := by
  rw [ENNReal.tsum_geometric, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ h0,
    ← ENNReal.ofReal_inv_of_pos (by linarith), one_div]

lemma vis {N : ℕ} (d : Data N) (y : Policy N) (e f : Level N)
    (h0 : 0 ≤ transient d y e f) (h1 : transient d y e f < 1) :
    visits d y e f = ENNReal.ofReal (1 / (1 - transient d y e f)) :=
  geo _ h0 h1

lemma pv_real {N : ℕ} (d : Data N) (y : Policy N) (e : Level N)
    (hT : ∀ f, 0 ≤ transient d y e f ∧ transient d y e f < 1)
    (hr : ∀ f, 0 ≤ reward d f (y f)) :
    policyValue d y e = ENNReal.ofReal
      (∑ f, 1 / (1 - transient d y e f) * reward d f (y f)) := by
  unfold policyValue
  rw [ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun f _ => ?_
    rw [vis d y e f (hT f).1 (hT f).2, ENNReal.ofReal_mul]
    have := (hT f).2
    exact div_nonneg zero_le_one (by linarith)
  · intro f _
    have := (hT f).2
    exact mul_nonneg (div_nonneg zero_le_one (by linarith)) (hr f)

noncomputable def dd : Data 1 where
  pM := fun _ => 0
  pI := fun _ => 1/2
  pQ := fun _ => 1/2
  qM := fun e => if e = 0 then 1/4 else 1/2
  qQ := fun e => if e = 0 then 3/4 else 1/2
  alpha := fun e => if e = 0 then 1/2 else 1
  tauM := 1
  tauI := 1/4
  muM := 1
  muI := 0

lemma mono2 (g : Fin 2 → ℝ) (h : g 0 ≤ g 1) : Monotone g := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

lemma anti2 (g : Fin 2 → ℝ) (h : g 1 ≤ g 0) : Antitone g := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

lemma hA14 : Assumptions14 dd := by
  refine ⟨⟨fun e => ?_, ?_, ?_, ?_⟩, fun e => ?_, ⟨?_, ?_, ?_, ?_, fun e => ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals first
    | exact mono2 _ (by simp [dd] <;> norm_num)
    | exact anti2 _ (by simp [dd] <;> norm_num)
    | (fin_cases e <;> simp [dd, Set.mem_Icc] <;> norm_num)
    | (simp [dd, A4, Set.mem_Icc, monotone_const, antitone_const] <;> norm_num)

lemma hA : Assumptions16 dd := by
  refine ⟨hA14, ?_, ?_⟩
  · simp [A5, dd]
  · intro e f hf
    fin_cases e <;> fin_cases f <;> simp_all [dd] <;> norm_num

lemma coe_sub (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((ENNReal.ofReal a : ℝ≥0∞) : EReal) - ((ENNReal.ofReal b : ℝ≥0∞) : EReal) =
      ((a - b : ℝ) : EReal) := by
  rw [EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal, max_eq_left ha, max_eq_left hb,
    EReal.coe_sub]

def y0 : Policy 1 := fun _ => false

lemma d10 : deltaVisits dd y0 1 0 = ((8/7 - 4/3 : ℝ) : EReal) := by
  have hT : transient dd (localPolicy y0 0 true) 0 1 = 1/8 := by
    simp [transient, toMDP, transition, sum_pa, choice, actionTransition, dd, localPolicy]; try norm_num
  have hF : transient dd (localPolicy y0 0 false) 0 1 = 1/4 := by
    simp [transient, toMDP, transition, sum_pa, choice, actionTransition, dd, localPolicy]; try norm_num
  unfold deltaVisits
  rw [vis _ _ _ _ (by rw [hT]; norm_num) (by rw [hT]; norm_num),
    vis _ _ _ _ (by rw [hF]; norm_num) (by rw [hF]; norm_num), hT, hF,
    coe_sub _ _ (by norm_num) (by norm_num)]
  norm_num

lemma d11 : deltaVisits dd y0 1 1 = ((0 : ℝ) : EReal) := by
  have hT : transient dd (localPolicy y0 1 true) 1 1 = 1/2 := by
    simp [transient, toMDP, transition, sum_pa, choice, actionTransition, dd, localPolicy]; try norm_num
  have hF : transient dd (localPolicy y0 1 false) 1 1 = 1/2 := by
    simp [transient, toMDP, transition, sum_pa, choice, actionTransition, dd, localPolicy]; try norm_num
  unfold deltaVisits
  rw [vis _ _ _ _ (by rw [hT]; norm_num) (by rw [hT]; norm_num),
    vis _ _ _ _ (by rw [hF]; norm_num) (by rw [hF]; norm_num), hT, hF,
    coe_sub _ _ (by norm_num) (by norm_num)]
  norm_num

end S228FR5

open S228FR5 in
theorem solution : ¬ (∀ {N : ℕ} (d : FreemiumActions.Threshold.Data N)
    (h : FreemiumActions.Threshold.Assumptions16 d)
    (y : FreemiumActions.Threshold.Policy N),
    (∀ e b : FreemiumActions.Threshold.Level N,
      FreemiumActions.Threshold.deltaVisits d y e b < 0 →
      ∀ b' : FreemiumActions.Threshold.Level N, b ≤ b' →
        FreemiumActions.Threshold.deltaVisits d y e b' < 0) ∧
    (∀ b : FreemiumActions.Threshold.Level N,
      FreemiumActions.Threshold.currentBenefit d y b < 0 →
      ∀ b' : FreemiumActions.Threshold.Level N, b ≤ b' →
        FreemiumActions.Threshold.currentBenefit d y b' < 0)) := by
  intro H
  have h1 := (H dd hA y0).1 1 0 (by rw [d10]; exact_mod_cast (by norm_num : (8/7 - 4/3 : ℝ) < 0))
    1 (by decide)
  rw [d11] at h1
  exact lt_irrefl _ (by exact_mod_cast h1)
