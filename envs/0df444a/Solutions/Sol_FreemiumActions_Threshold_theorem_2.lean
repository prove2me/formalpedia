-- Prove2me | solution 1 for FreemiumActions.Threshold.theorem_2
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:13:00.105053+00:00
-- url     : https://prove2.me/submissions/c74ea131-1450-4375-8bec-fb22eb2720e6

import Mathlib
import Definitions.Def_FreemiumActions_Threshold_ThresholdPolicy
open scoped ENNReal
open FreemiumActions.Threshold

namespace S228FR2

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
  qM := fun e => if e = 0 then 1/8 else 1/2
  qQ := fun e => if e = 0 then 7/8 else 1/2
  alpha := fun e => if e = 0 then 1/4 else 1
  tauM := 1
  tauI := 3/4
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

lemma hA : Assumptions17 dd := by
  refine ⟨⟨hA14, ?_, ?_⟩, ?_⟩
  · simp [A5, dd]
  · intro e f hf
    fin_cases e <;> fin_cases f <;> simp_all [dd] <;> norm_num
  · intro e f he hf
    fin_cases e <;> fin_cases f <;> simp_all

lemma hT (y : Policy 1) (e f : Level 1) :
    0 ≤ transient dd y e f ∧ transient dd y e f < 1 := by
  obtain ⟨b, hb⟩ : ∃ b, y e = b := ⟨_, rfl⟩
  fin_cases e <;> fin_cases f <;>
    simp [transient, toMDP, transition, sum_pa, choice, actionTransition, dd] at hb ⊢ <;>
    simp [hb] <;> cases b <;> norm_num

lemma hr (y : Policy 1) (f : Level 1) : 0 ≤ reward dd f (y f) := by
  fin_cases f <;> simp [reward, dd] <;> cases y _ <;> norm_num

lemma vr (y : Policy 1) (e : Level 1) (b0 b1 : Bool) (hb0 : y 0 = b0) (hb1 : y 1 = b1) :
    policyValue dd y e = ENNReal.ofReal
      (if e = 0 then
        (match b0, b1 with
          | false, false => 39/56 | false, true => 1/8 | true, false => 4/5 | true, true => 0)
      else
        (match b0, b1 with
          | false, false => 9/8 | false, true => 1/8 | true, false => 1 | true, true => 0)) := by
  rw [pv_real _ _ _ (hT _ e) (hr _)]
  congr 1
  fin_cases e <;>
    simp [Fin.sum_univ_succ, Fin.sum_univ_zero, transient, toMDP, transition, sum_pa, choice, actionTransition, dd,
      reward, hb0, hb1] <;>
    cases b0 <;> cases b1 <;> norm_num

end S228FR2

open S228FR2 in
theorem solution : ¬ (∀ {N : ℕ} (d : FreemiumActions.Threshold.Data N)
    (h : FreemiumActions.Threshold.Assumptions17 d),
    ∃ y : FreemiumActions.Threshold.Policy N,
      FreemiumActions.Threshold.IsOptimal d y ∧ FreemiumActions.Threshold.IsThreshold y) := by
  intro H
  obtain ⟨y, hy, -⟩ := H dd hA
  have h1 := hy ![false, false] 1
  have h0 := hy ![true, false] 0
  obtain ⟨b0, hb0⟩ : ∃ b, y 0 = b := ⟨_, rfl⟩
  obtain ⟨b1, hb1⟩ : ∃ b, y 1 = b := ⟨_, rfl⟩
  rw [vr y 1 b0 b1 hb0 hb1, vr ![false, false] 1 false false rfl rfl] at h1
  rw [vr y 0 b0 b1 hb0 hb1, vr ![true, false] 0 true false rfl rfl] at h0
  rw [ENNReal.ofReal_le_ofReal_iff'] at h0 h1
  cases b0 <;> cases b1 <;> first | (norm_num at h0; done) | (norm_num at h1; done)
