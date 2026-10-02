-- Prove2me | solution 1 for FoundationsML.OnlineLearning.rwm_loss_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T13:25:38.441677+00:00
-- url     : https://prove2.me/submissions/f43c5d5e-07bd-42bf-8b31-f10a3f9cdb7a

import Mathlib
import Definitions.Def_FoundationsML_OnlineLearning_RWMCumulativeLoss
import Definitions.Def_FoundationsML_OnlineLearning_RWMMinExpertLoss

set_option autoImplicit false

namespace RWMProof1b5d

open FoundationsML.OnlineLearning

lemma weight_pos {β : ℝ} (hβ : 0 < β) (N : ℕ) (l : ℕ → Fin N → ℝ) (t : ℕ) (i : Fin N) :
    0 < RWMWeight β N l t i := by
  induction t with
  | zero => simp [RWMWeight]
  | succ t ih =>
    simp only [RWMWeight]
    split_ifs
    · exact mul_pos hβ ih
    · exact ih

lemma weight_succ (β : ℝ) (N : ℕ) (l : ℕ → Fin N → ℝ) (hl : ∀ t i, l t i = 0 ∨ l t i = 1)
    (t : ℕ) (i : Fin N) :
    RWMWeight β N l (t + 1) i = RWMWeight β N l t i - (1 - β) * (RWMWeight β N l t i * l t i) := by
  simp only [RWMWeight]
  rcases hl t i with h | h
  · rw [if_neg (by rw [h]; norm_num), h]; ring
  · rw [if_pos h, h]; ring

lemma log_weight {β : ℝ} (hβ : 0 < β) (N : ℕ) (l : ℕ → Fin N → ℝ)
    (hl : ∀ t i, l t i = 0 ∨ l t i = 1) (t : ℕ) (i : Fin N) :
    Real.log (RWMWeight β N l t i) = RWMExpertCumulativeLoss N l t i * Real.log β := by
  induction t with
  | zero => simp [RWMWeight, RWMExpertCumulativeLoss]
  | succ t ih =>
    have hw := weight_pos hβ N l t i
    simp only [RWMExpertCumulativeLoss, Finset.sum_range_succ] at ih ⊢
    simp only [RWMWeight]
    rcases hl t i with h | h
    · rw [if_neg (by rw [h]; norm_num), h, ih]; ring
    · rw [if_pos h, h, Real.log_mul hβ.ne' hw.ne', ih]; ring

lemma potential_pos {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) (l : ℕ → Fin N → ℝ) (t : ℕ) :
    0 < RWMPotential β N l t := by
  unfold RWMPotential
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact Finset.sum_pos (fun i _ => weight_pos hβ N l t i) Finset.univ_nonempty

lemma roundLoss_mul {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) (l : ℕ → Fin N → ℝ) (t : ℕ) :
    RWMRoundLoss β N l t * RWMPotential β N l t = ∑ i, RWMWeight β N l t i * l t i := by
  have hW := (potential_pos hβ hN l t).ne'
  unfold RWMRoundLoss RWMDist
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  field_simp

lemma roundLoss_nonneg {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) (l : ℕ → Fin N → ℝ)
    (hl : ∀ t i, l t i = 0 ∨ l t i = 1) (t : ℕ) : 0 ≤ RWMRoundLoss β N l t := by
  have hW := potential_pos hβ hN l t
  have h := roundLoss_mul hβ hN l t
  have hs : 0 ≤ ∑ i, RWMWeight β N l t i * l t i := by
    refine Finset.sum_nonneg (fun i _ => ?_)
    rcases hl t i with h' | h' <;> rw [h'] <;> nlinarith [weight_pos hβ N l t i]
  nlinarith

lemma roundLoss_le_one {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) (l : ℕ → Fin N → ℝ)
    (hl : ∀ t i, l t i = 0 ∨ l t i = 1) (t : ℕ) : RWMRoundLoss β N l t ≤ 1 := by
  have hW := potential_pos hβ hN l t
  have h := roundLoss_mul hβ hN l t
  have hs : ∑ i, RWMWeight β N l t i * l t i ≤ RWMPotential β N l t := by
    unfold RWMPotential
    refine Finset.sum_le_sum (fun i _ => ?_)
    rcases hl t i with h' | h' <;> rw [h'] <;> nlinarith [weight_pos hβ N l t i]
  nlinarith

lemma cumLoss_le {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) (l : ℕ → Fin N → ℝ)
    (hl : ∀ t i, l t i = 0 ∨ l t i = 1) (T : ℕ) : RWMCumulativeLoss β N l T ≤ T := by
  unfold RWMCumulativeLoss
  calc ∑ t ∈ Finset.range T, RWMRoundLoss β N l t ≤ ∑ t ∈ Finset.range T, (1 : ℝ) :=
        Finset.sum_le_sum (fun t _ => roundLoss_le_one hβ hN l hl t)
    _ = T := by simp

lemma log_potential {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {N : ℕ} (hN : 0 < N)
    (l : ℕ → Fin N → ℝ) (hl : ∀ t i, l t i = 0 ∨ l t i = 1) (T : ℕ) :
    Real.log (RWMPotential β N l T) ≤ Real.log N - (1 - β) * RWMCumulativeLoss β N l T := by
  induction T with
  | zero => simp [RWMPotential, RWMWeight, RWMCumulativeLoss]
  | succ t ih =>
    have hW := potential_pos hβ hN l t
    have hW' := potential_pos hβ hN l (t + 1)
    have hrec : RWMPotential β N l (t + 1) =
        RWMPotential β N l t * (1 - (1 - β) * RWMRoundLoss β N l t) := by
      have h := roundLoss_mul hβ hN l t
      unfold RWMPotential at h ⊢
      simp only [weight_succ β N l hl t, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [← h]; ring
    have hfac : 0 < 1 - (1 - β) * RWMRoundLoss β N l t := by
      rw [hrec] at hW'
      exact pos_of_mul_pos_right hW' hW.le
    have hstep : Real.log (RWMPotential β N l (t + 1)) ≤
        Real.log (RWMPotential β N l t) - (1 - β) * RWMRoundLoss β N l t := by
      rw [hrec, Real.log_mul hW.ne' hfac.ne']
      have := Real.log_le_sub_one_of_pos hfac
      linarith
    have hsum : RWMCumulativeLoss β N l (t + 1) =
        RWMCumulativeLoss β N l t + RWMRoundLoss β N l t := by
      simp [RWMCumulativeLoss, Finset.sum_range_succ]
    rw [hsum]
    nlinarith

lemma neg_log_le {β : ℝ} (h1 : 1 / 2 ≤ β) (h2 : β < 1) : -Real.log β ≤ (1 - β) * (2 - β) := by
  set x := 1 - β with hx
  have hx0 : 0 < x := by linarith
  have hx1 : x ≤ 1 / 2 := by linarith
  have habs : |x| = x := abs_of_pos hx0
  have key := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [habs]; linarith) 4
  rw [habs] at key
  have hβ : β = 1 - x := by linarith
  rw [hβ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at key
  have hle := (abs_le.mp key).1
  have h1x : 0 < 1 - x := by linarith
  have hdiv : x ^ 5 / (1 - x) ≤ 2 * x ^ 5 := by
    rw [div_le_iff₀ h1x]
    have : 0 ≤ x ^ 5 := by positivity
    nlinarith [mul_nonneg this (by linarith : (0:ℝ) ≤ 1 - 2 * x)]
  norm_num at hle
  have hpoly : x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4 + 2 * x ^ 5 ≤ x * (1 + x) := by
    have h3 : x ^ 3 ≤ x ^ 2 / 2 := by nlinarith [sq_nonneg x]
    have h4 : x ^ 4 ≤ x ^ 3 / 2 := by nlinarith [pow_pos hx0 3]
    have h5 : x ^ 5 ≤ x ^ 4 / 2 := by nlinarith [pow_pos hx0 4]
    nlinarith
  nlinarith

lemma minLoss_facts {N : ℕ} (hN : 0 < N) (l : ℕ → Fin N → ℝ)
    (hl : ∀ t i, l t i = 0 ∨ l t i = 1) (T : ℕ) :
    0 ≤ RWMMinExpertLoss N l T ∧ RWMMinExpertLoss N l T ≤ T ∧
      ∃ i, RWMExpertCumulativeLoss N l T i = RWMMinExpertLoss N l T := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hle : ∀ i, RWMExpertCumulativeLoss N l T i ≤ T := by
    intro i
    unfold RWMExpertCumulativeLoss
    calc ∑ t ∈ Finset.range T, l t i ≤ ∑ t ∈ Finset.range T, (1 : ℝ) :=
          Finset.sum_le_sum (fun t _ => by rcases hl t i with h | h <;> rw [h] <;> norm_num)
      _ = T := by simp
  have hge : ∀ i, 0 ≤ RWMExpertCumulativeLoss N l T i := by
    intro i
    unfold RWMExpertCumulativeLoss
    exact Finset.sum_nonneg (fun t _ => by rcases hl t i with h | h <;> rw [h] <;> norm_num)
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := RWMExpertCumulativeLoss N l T)
  unfold RWMMinExpertLoss
  refine ⟨?_, ?_, i, hi⟩
  · rw [← hi]; exact hge i
  · rw [← hi]; exact hle i

lemma part1 {N : ℕ} (hN : 0 < N) (l : ℕ → Fin N → ℝ) (hl : ∀ t i, l t i = 0 ∨ l t i = 1)
    (T : ℕ) (β : ℝ) (h1 : 1 / 2 ≤ β) (h2 : β < 1) :
    RWMCumulativeLoss β N l T ≤ Real.log N / (1 - β) + (2 - β) * RWMMinExpertLoss N l T := by
  have hβ : 0 < β := by linarith
  obtain ⟨hm0, -, i, hi⟩ := minLoss_facts hN l hl T
  have hlogw := log_weight hβ N l hl T i
  have hpot := log_potential hβ h2.le hN l hl T
  have hwle : Real.log (RWMWeight β N l T i) ≤ Real.log (RWMPotential β N l T) := by
    apply Real.log_le_log (weight_pos hβ N l T i)
    unfold RWMPotential
    exact Finset.single_le_sum (f := fun j => RWMWeight β N l T j)
      (fun j _ => (weight_pos hβ N l T j).le) (Finset.mem_univ i)
  rw [hlogw, hi] at hwle
  have hnl := neg_log_le h1 h2
  have h1b : 0 < 1 - β := by linarith
  rw [div_add' _ _ _ h1b.ne', le_div_iff₀ h1b]
  nlinarith

end RWMProof1b5d

open FoundationsML.OnlineLearning in
theorem solution {N : ℕ} (hN : 0 < N) (l : ℕ → Fin N → ℝ) (hl : ∀ t i, l t i = 0 ∨ l t i = 1)
    (T : ℕ) (hT : 1 ≤ T) :
    (∀ β : ℝ, 1 / 2 ≤ β → β < 1 →
      RWMCumulativeLoss β N l T ≤
        Real.log N / (1 - β) + (2 - β) * RWMMinExpertLoss N l T) ∧
    RWMCumulativeLoss (max (1 / 2) (1 - Real.sqrt (Real.log N / T))) N l T ≤
      RWMMinExpertLoss N l T + 2 * Real.sqrt (T * Real.log N) := by
  refine ⟨fun β h1 h2 => RWMProof1b5d.part1 hN l hl T β h1 h2, ?_⟩
  obtain ⟨hm0, hmT, -⟩ := RWMProof1b5d.minLoss_facts hN l hl T
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  set s := Real.sqrt (Real.log N / T) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = Real.log N / T := Real.mul_self_sqrt (div_nonneg hlogN hTpos.le)
  have hsq : Real.sqrt (T * Real.log N) = T * s := by
    have h2 : (T : ℝ) * Real.log N = (T * s) ^ 2 := by
      rw [mul_pow, pow_two s, hss]; field_simp
    rw [h2, Real.sqrt_sq (by positivity)]
  rw [hsq]
  rcases eq_or_lt_of_le hs0 with h0 | hpos
  · -- s = 0, so log N = 0, N = 1
    have hlog0 : Real.log N = 0 := by
      have : Real.log N / T = 0 := by rw [← hss, ← h0]; ring
      rcases div_eq_zero_iff.mp this with h | h
      · exact h
      · exact absurd h hTpos.ne'
    have hN1 : N = 1 := by
      have := Real.eq_one_of_pos_of_log_eq_zero (by exact_mod_cast hN) hlog0
      exact_mod_cast this
    subst hN1
    rw [← h0]
    have hmax : max (1 / 2 : ℝ) (1 - 0) = 1 := by norm_num
    rw [hmax]
    have hcum : RWMCumulativeLoss 1 1 l T = RWMExpertCumulativeLoss 1 l T 0 := by
      unfold RWMCumulativeLoss RWMExpertCumulativeLoss
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have hw : ∀ t' j, RWMWeight 1 1 l t' j = 1 := by
        intro t' j
        induction t' with
        | zero => rfl
        | succ t' ih => simp only [RWMWeight]; split_ifs <;> simp [ih]
      simp [RWMRoundLoss, RWMDist, RWMPotential, hw]
    have hmin : RWMMinExpertLoss 1 l T = RWMExpertCumulativeLoss 1 l T 0 := by
      unfold RWMMinExpertLoss
      rw [ciInf_unique]
      rfl
    rw [hcum, hmin]; simp
  · rcases le_or_gt s (1 / 2) with hsle | hsgt
    · have hmax : max (1 / 2 : ℝ) (1 - s) = 1 - s := max_eq_right (by linarith)
      rw [hmax]
      have h := RWMProof1b5d.part1 hN l hl T (1 - s) (by linarith) (by linarith)
      have hlogs : Real.log N / (1 - (1 - s)) = T * s := by
        rw [sub_sub_cancel, div_eq_iff hpos.ne']
        rw [mul_assoc, hss]; field_simp
      rw [hlogs] at h
      nlinarith
    · have hmax : max (1 / 2 : ℝ) (1 - s) = 1 / 2 := max_eq_left (by linarith)
      rw [hmax]
      have h := RWMProof1b5d.cumLoss_le (by norm_num : (0 : ℝ) < 1 / 2) hN l hl T
      nlinarith
