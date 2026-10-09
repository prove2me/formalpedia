-- Prove2me | solution 1 for FosterQueues.MG1.mg1_classification
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T16:44:00.242636+00:00
-- url     : https://prove2.me/submissions/6ea36eac-5c60-4ab6-8add-35647eb0a766
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FosterQueues_MG1_Model
import Theorems.Thm_QueueingFundamentals_Foundations_foster_criterion
import Theorems.Thm_FosterQueues_MG1_theorem3_first_passage_equations
import Theorems.Thm_FosterQueues_MG1_mean_first_passage_linear
import Theorems.Thm_FosterQueues_MG1_theorem4_transience_criterion
import Theorems.Thm_FosterQueues_MG1_theorem5_recurrence_criterion
import Theorems.Thm_FosterQueues_MG1_theorem7_branching_root

set_option autoImplicit false

section

open scoped ENNReal
open QueueingFundamentals.Foundations
open FosterQueues.MG1

theorem b13_stepProb_succ (P : TransitionMatrix) (n i j : ℕ) :
    P.stepProb (n + 1) i j = ∑' l, P.p i l * P.stepProb n l j := rfl

theorem b13_stepProb_bounds (P : TransitionMatrix) :
    ∀ n i j, 0 ≤ P.stepProb n i j ∧ P.stepProb n i j ≤ 1 := by
  intro n
  induction n with
  | zero =>
    intro i j
    show 0 ≤ (if i = j then (1:ℝ) else 0) ∧ (if i = j then (1:ℝ) else 0) ≤ 1
    split_ifs <;> norm_num
  | succ n ih =>
    intro i j
    rw [b13_stepProb_succ]
    have hs : Summable (fun l => P.p i l * P.stepProb n l j) :=
      (P.row_sum i).summable.of_nonneg_of_le
        (fun l => mul_nonneg (P.nonneg i l) (ih l j).1)
        (fun l => mul_le_of_le_one_right (P.nonneg i l) (ih l j).2)
    refine ⟨tsum_nonneg fun l => mul_nonneg (P.nonneg i l) (ih l j).1, ?_⟩
    calc ∑' l, P.p i l * P.stepProb n l j ≤ ∑' l, P.p i l :=
          hs.tsum_le_tsum (fun l => mul_le_of_le_one_right (P.nonneg i l) (ih l j).2)
            (P.row_sum i).summable
      _ = 1 := (P.row_sum i).tsum_eq

theorem b13_stepProb_ge (P : TransitionMatrix) (n i l j : ℕ) :
    P.p i l * P.stepProb n l j ≤ P.stepProb (n + 1) i j := by
  rw [b13_stepProb_succ]
  have hb := b13_stepProb_bounds P
  have hs : Summable (fun l => P.p i l * P.stepProb n l j) :=
    (P.row_sum i).summable.of_nonneg_of_le
      (fun l => mul_nonneg (P.nonneg i l) (hb n l j).1)
      (fun l => mul_le_of_le_one_right (P.nonneg i l) (hb n l j).2)
  exact hs.le_tsum l (fun l' _ => mul_nonneg (P.nonneg i l') (hb n l' j).1)

theorem b13_mg1_irreducible_aperiodic (k : ℕ → ℝ) (hk : ∀ i, 0 < k i)
    (P : TransitionMatrix) (hP : P.p = mg1Matrix k) : P.Irreducible ∧ P.Aperiodic := by
  have hstep0 : ∀ j, P.stepProb 0 j j = 1 := fun j => by
    show (if j = j then (1:ℝ) else 0) = 1
    simp
  constructor
  · intro i j
    refine ⟨i + 1, ?_⟩
    induction i with
    | zero =>
      have h := b13_stepProb_ge P 0 0 j j
      rw [hstep0, mul_one, hP] at h
      have : mg1Matrix k 0 j = k j := by simp [mg1Matrix]
      rw [this] at h
      exact lt_of_lt_of_le (hk j) h
    | succ m ih =>
      have h := b13_stepProb_ge P (m + 1) (m + 1) m j
      have hpm : P.p (m + 1) m = k 0 := by
        rw [hP]; simp [mg1Matrix]
      rw [hpm] at h
      exact lt_of_lt_of_le (mul_pos (hk 0) ih) h
  · intro s d hd
    have h := b13_stepProb_ge P 0 s s s
    rw [hstep0, mul_one] at h
    have hpos : 0 < P.p s s := by
      rw [hP]
      unfold mg1Matrix
      split_ifs with h1 h2
      · exact hk s
      · exact hk _
      · omega
    exact Nat.dvd_one.mp (hd 1 one_pos (lt_of_lt_of_le hpos h))

theorem b13_hasSum_shift (k : ℕ → ℝ) (g : ℕ → ℝ) (m : ℕ) (a : ℝ)
    (h : HasSum (fun n => k n * g (n + m)) a) :
    HasSum (fun j => mg1Matrix k (m + 1) j * g j) a := by
  rw [← hasSum_nat_add_iff' m]
  have h0 : ∑ i ∈ Finset.range m, mg1Matrix k (m + 1) i * g i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have : ¬ (m + 1 ≤ i + 1) := by simp at hi; omega
    simp [mg1Matrix, this]
  rw [h0, sub_zero]
  have e : (fun n => mg1Matrix k (m + 1) (n + m) * g (n + m)) = fun n => k n * g (n + m) := by
    funext n
    have : m + 1 ≤ n + m + 1 := by omega
    have e2 : n + m + 1 - (m + 1) = n := by omega
    simp only [mg1Matrix, this, if_true, Nat.add_one_ne_zero, if_false, e2]
  rw [e]
  exact h

theorem b13_mg1_pow_harmonic (k : ℕ → ℝ) (hk : ∀ i, 0 < k i) (hsum : HasSum k 1)
    (P : TransitionMatrix) (hP : P.p = mg1Matrix k) (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (hroot : ∑' n : ℕ, ξ ^ n * k n = ξ) :
    ∀ i : ℕ, i ≠ 0 → HasSum (fun j => P.p i j * ξ ^ j) (ξ ^ i) := by
  intro i hi
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [hP]
  apply b13_hasSum_shift
  have hs : Summable (fun n => ξ ^ n * k n) :=
    hsum.summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg hξ0.le n) (hk n).le)
      (fun n => mul_le_of_le_one_left (hk n).le (pow_le_one₀ hξ0.le hξ1.le))
  have h2 := (hs.hasSum.mul_left (ξ ^ m))
  rw [hroot] at h2
  have e : (fun n => k n * ξ ^ (n + m)) = fun i => ξ ^ m * (ξ ^ i * k i) := by
    funext n; rw [pow_add]; ring
  rw [e, pow_succ]
  exact h2

theorem b13_mg1_linear_drift (k : ℕ → ℝ) (hk : ∀ i, 0 < k i) (hsum : HasSum k 1)
    (P : TransitionMatrix) (hP : P.p = mg1Matrix k) (hρ : rho k < ⊤) :
    (∀ i : ℕ, i ≠ 0 → HasSum (fun j => P.p i j * (j : ℝ)) ((i : ℝ) - 1 + (rho k).toReal)) ∧
      HasSum (fun j => P.p 0 j * (j : ℝ)) (rho k).toReal := by
  have hfin : ∀ n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (k n) ≠ ⊤ := fun n =>
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) ENNReal.ofReal_ne_top
  have hρ' : (∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (k n)) ≠ ⊤ := hρ.ne
  have hterm : ∀ n : ℕ, ((n : ℝ≥0∞) * ENNReal.ofReal (k n)).toReal = k n * n := fun n => by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hk n).le, ENNReal.toReal_natCast, mul_comm]
  have hmean : HasSum (fun n => k n * (n : ℝ)) (rho k).toReal := by
    have hs := ENNReal.summable_toReal hρ'
    have he := ENNReal.tsum_toReal_eq hfin
    simp only [hterm] at hs he
    unfold rho
    rw [he]
    exact hs.hasSum
  refine ⟨fun i hi => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    rw [hP]
    apply b13_hasSum_shift
    have h2 := hmean.add (hsum.mul_right (m : ℝ))
    convert h2 using 1
    · funext n; push_cast; ring
    · push_cast; ring
  · rw [hP]
    simpa [mg1Matrix] using hmean

theorem solution (k : ℕ → ℝ) (hk : ∀ i, 0 < k i) (hsum : HasSum k 1)
    (P : TransitionMatrix) (hP : P.p = mg1Matrix k) :
    (P.PositiveRecurrent ↔ rho k < 1) ∧ (IsRecurrent P ↔ rho k ≤ 1) := by
  obtain ⟨hirr, hap⟩ := b13_mg1_irreducible_aperiodic k hk P hP
  refine ⟨⟨fun hpos => ?_, fun hρ => ?_⟩, ⟨fun hrec => ?_, fun hρ => ?_⟩⟩
  · -- positive recurrent ⇒ ρ < 1 :  μ₁₀ = 1 + ρ μ₁₀ with μ₁₀ < ∞
    obtain ⟨hfin, heq, -⟩ := FosterQueues.MG1.theorem3_first_passage_equations P hirr hap hpos
    obtain ⟨-, hlin⟩ := FosterQueues.MG1.mean_first_passage_linear k hk hsum P hP hpos
    set M := meanFirstPassage P 1 0 with hMdef
    have hM : M < ⊤ := hfin 1 one_ne_zero
    have hp1 : ∀ j : ℕ, P.p 1 (j + 1) = k (j + 1) := by
      intro j; rw [hP]; simp [mg1Matrix]
    have hsumρ : ∑' j : ℕ, ENNReal.ofReal (P.p 1 (j + 1)) * meanFirstPassage P (j + 1) 0 =
        rho k * M := by
      have hρs : rho k = ∑' j : ℕ, ((j + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (k (j + 1)) := by
        unfold rho
        rw [tsum_eq_zero_add' ENNReal.summable]
        simp
      rw [hρs, ← ENNReal.tsum_mul_right]
      refine tsum_congr fun j => ?_
      rw [hp1 j, hlin (j + 1) (Nat.succ_ne_zero j)]
      ring
    have h1 := heq 1 one_ne_zero
    rw [hsumρ] at h1
    by_contra hρ
    have hρ1 : 1 ≤ rho k := not_lt.mp hρ
    have : M + 1 ≤ M := by
      calc M + 1 = 1 + 1 * M := by rw [one_mul, add_comm]
        _ ≤ 1 + rho k * M := by gcongr
        _ = M := h1.symm
    exact absurd this (not_le.mpr (ENNReal.lt_add_right hM.ne one_ne_zero))
  · -- ρ < 1 ⇒ positive recurrent : Foster with x_j = j / (1 - ρ)
    have hρtop : rho k < ⊤ := lt_of_lt_of_le hρ le_top
    obtain ⟨hdr, hdr0⟩ := b13_mg1_linear_drift k hk hsum P hP hρtop
    set r := (rho k).toReal with hr
    have hr1 : r < 1 := by
      have := (ENNReal.toReal_lt_toReal hρtop.ne ENNReal.one_ne_top).mpr hρ
      simpa using this
    have hr1' : 0 < 1 - r := by linarith
    refine QueueingFundamentals.Foundations.foster_criterion P hirr hap (fun j => (j : ℝ) / (1 - r))
      (fun j => div_nonneg (Nat.cast_nonneg j) hr1'.le) (fun i => ?_) (fun i hi => ?_)
    · rcases eq_or_ne i 0 with rfl | hi
      · simpa [mul_div_assoc] using hdr0.summable.div_const (1 - r)
      · simpa [mul_div_assoc] using (hdr i hi).summable.div_const (1 - r)
    · have h := ((hdr i hi).div_const (1 - r)).tsum_eq
      simp only [mul_div_assoc] at h
      rw [h]
      apply le_of_eq
      field_simp
      ring
  · -- recurrent ⇒ ρ ≤ 1 : otherwise ξ^j is a bounded nonconstant harmonic function
    by_contra hρ
    have hρ1 : 1 < rho k := not_le.mp hρ
    obtain ⟨ξ, hξ0, hξ1, hroot⟩ :=
      (FosterQueues.MG1.theorem7_branching_root k (fun n => (hk n).le) hsum (hk 0)).mpr hρ1
    have htr : IsTransient P := (FosterQueues.MG1.theorem4_transience_criterion P hirr hap).mpr
      ⟨fun j => ξ ^ j, ⟨1, fun i => by
          rw [abs_of_nonneg (pow_nonneg hξ0.le i)]; exact pow_le_one₀ hξ0.le hξ1.le⟩,
        ⟨0, 1, by simp; exact hξ1.ne'⟩,
        b13_mg1_pow_harmonic k hk hsum P hP ξ hξ0 hξ1 hroot⟩
    have h0 := htr 0
    rw [hrec 0] at h0
    exact lt_irrefl _ h0
  · -- ρ ≤ 1 ⇒ recurrent : Foster's Theorem 5 with y_j = j
    have hρtop : rho k < ⊤ := lt_of_le_of_lt hρ ENNReal.one_lt_top
    obtain ⟨hdr, hdr0⟩ := b13_mg1_linear_drift k hk hsum P hP hρtop
    have hr1 : (rho k).toReal ≤ 1 := by
      have := (ENNReal.toReal_le_toReal hρtop.ne ENNReal.one_ne_top).mpr hρ
      simpa using this
    refine FosterQueues.MG1.theorem5_recurrence_criterion P hirr hap (fun j => (j : ℝ))
      (fun i hi => (hdr i hi).summable) (fun i hi => ?_) tendsto_natCast_atTop_atTop
    rw [(hdr i hi).tsum_eq]
    linarith

end
