-- Prove2me | solution 1 for DurrettProbability.markov_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T07:08:48.797191+00:00
-- url     : https://prove2.me/submissions/4d0cd8b8-fed9-43c1-80c3-5d2f98141b56

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain

open Filter

-- ===== Basic =====

open Filter
open scoped ENNReal

namespace DurrettProbability

variable {S : Type*} [DecidableEq S]

/-! ## Extended-nonnegative-real versions of the chain quantities -/

/-- The transition kernel as an `ℝ≥0∞`-valued function. -/
noncomputable def PE (p : S → S → ℝ) (x y : S) : ℝ≥0∞ := ENNReal.ofReal (p x y)

/-- `ℝ≥0∞` version of `stepProb`. -/
noncomputable def stepE (p : S → S → ℝ) : ℕ → S → S → ℝ≥0∞
  | 0, x, y => if x = y then 1 else 0
  | (n + 1), x, y => ∑' z, PE p x z * stepE p n z y

/-- `ℝ≥0∞` version of `firstPassage`. -/
noncomputable def fpE (p : S → S → ℝ) : ℕ → S → S → ℝ≥0∞
  | 0, _, _ => 0
  | 1, x, y => PE p x y
  | (n + 2), x, y => ∑' z, if z = y then 0 else PE p x z * fpE p (n + 1) z y

/-- `ℝ≥0∞` version of `hitProb`. -/
noncomputable def rhoE (p : S → S → ℝ) (x y : S) : ℝ≥0∞ := ∑' n : ℕ, fpE p (n + 1) x y

/-- Green function `∑_{n ≥ 1} pⁿ(x,y)`. -/
noncomputable def greenE (p : S → S → ℝ) (x y : S) : ℝ≥0∞ := ∑' n : ℕ, stepE p (n + 1) x y

lemma stepE_zero (p : S → S → ℝ) (x y : S) : stepE p 0 x y = if x = y then 1 else 0 := rfl

lemma stepE_succ (p : S → S → ℝ) (n : ℕ) (x y : S) :
    stepE p (n + 1) x y = ∑' z, PE p x z * stepE p n z y := rfl

lemma fpE_one (p : S → S → ℝ) (x y : S) : fpE p 1 x y = PE p x y := rfl

lemma fpE_succ_succ (p : S → S → ℝ) (n : ℕ) (x y : S) :
    fpE p (n + 2) x y = ∑' z, if z = y then 0 else PE p x z * fpE p (n + 1) z y := rfl

/-- Cauchy product formula for `ℝ≥0∞`-valued series. -/
theorem ennreal_cauchy (a b : ℕ → ℝ≥0∞) :
    ∑' n, ∑ m ∈ Finset.range (n + 1), a m * b (n - m) = (∑' m, a m) * (∑' k, b k) := by
  have h1 : ∀ n, ∑ m ∈ Finset.range (n + 1), a m * b (n - m) =
      ∑' m, if m ≤ n then a m * b (n - m) else 0 := by
    intro n
    rw [tsum_eq_sum (s := Finset.range (n + 1)) (fun m hm => by
      simp only [Finset.mem_range, not_lt] at hm; rw [if_neg (by omega)])]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    simp only [Finset.mem_range] at hm
    rw [if_pos (by omega)]
  have h2 : ∀ m, ∑' n, (if m ≤ n then a m * b (n - m) else 0) = a m * ∑' k, b k := by
    intro m
    rw [← ENNReal.tsum_mul_left]
    have hinj : Function.Injective (fun k : ℕ => k + m) := add_left_injective m
    rw [← hinj.tsum_eq (f := fun n => if m ≤ n then a m * b (n - m) else 0)]
    · refine tsum_congr (fun k => ?_)
      simp only [le_add_iff_nonneg_left, zero_le, if_true, Nat.add_sub_cancel]
    · intro n hn
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
      exact ⟨n - m, by simp only; omega⟩
  simp_rw [h1]
  rw [ENNReal.tsum_comm]
  simp_rw [h2]
  rw [ENNReal.tsum_mul_right]

/-- Split off the term at `y` of an `ℝ≥0∞`-valued sum (with the `DecidableEq` instance). -/
lemma tsum_split_at (f : S → ℝ≥0∞) (y : S) :
    ∑' z, f z = f y + ∑' z, if z = y then 0 else f z := by
  convert ENNReal.tsum_eq_add_tsum_ite y

section Transition

variable {p : S → S → ℝ}

omit [DecidableEq S] in
lemma IsTransition.nonneg (hp : IsTransition p) (x y : S) : 0 ≤ p x y := hp.1 x y

omit [DecidableEq S] in
lemma IsTransition.le_one (hp : IsTransition p) (x y : S) : p x y ≤ 1 := by
  rw [← hp.2.2 x]
  exact (hp.2.1 x).le_tsum y (fun j _ => hp.1 x j)

omit [DecidableEq S] in
lemma IsTransition.sum_PE (hp : IsTransition p) (x : S) : ∑' y, PE p x y = 1 := by
  unfold PE
  rw [← ENNReal.ofReal_tsum_of_nonneg (hp.1 x) (hp.2.1 x), hp.2.2 x, ENNReal.ofReal_one]

omit [DecidableEq S] in
lemma IsTransition.PE_le_one (hp : IsTransition p) (x y : S) : PE p x y ≤ 1 := by
  rw [← hp.sum_PE x]; exact ENNReal.le_tsum y

omit [DecidableEq S] in
lemma PE_ne_top (x y : S) : PE p x y ≠ ⊤ := ENNReal.ofReal_ne_top

/-- Row sums of `pⁿ` are one. -/
lemma IsTransition.sum_stepE (hp : IsTransition p) (n : ℕ) (x : S) :
    ∑' y, stepE p n x y = 1 := by
  induction n generalizing x with
  | zero =>
    rw [tsum_eq_single x (fun y hy => by rw [stepE_zero, if_neg (Ne.symm hy)])]
    simp [stepE_zero]
  | succ n ih =>
    simp_rw [stepE_succ]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, ih, mul_one]
    exact hp.sum_PE x

lemma IsTransition.stepE_le_one (hp : IsTransition p) (n : ℕ) (x y : S) : stepE p n x y ≤ 1 := by
  rw [← hp.sum_stepE n x]; exact ENNReal.le_tsum y

lemma IsTransition.stepE_ne_top (hp : IsTransition p) (n : ℕ) (x y : S) : stepE p n x y ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (hp.stepE_le_one n x y)

/-- The real `n`-step probabilities are the `ℝ≥0∞` ones. -/
lemma IsTransition.stepProb_spec (hp : IsTransition p) (n : ℕ) (x y : S) :
    0 ≤ stepProb p n x y ∧ ENNReal.ofReal (stepProb p n x y) = stepE p n x y := by
  induction n generalizing x y with
  | zero => by_cases h : x = y <;> simp [stepProb, stepE_zero, h]
  | succ n ih =>
    have hle : ∀ z, stepProb p n z y ≤ 1 := fun z => by
      have := hp.stepE_le_one n z y
      rw [← (ih z y).2] at this
      exact (ENNReal.ofReal_le_one).1 this
    have hnn : ∀ z, 0 ≤ p x z * stepProb p n z y := fun z => mul_nonneg (hp.1 x z) (ih z y).1
    have hsum : Summable (fun z => p x z * stepProb p n z y) :=
      Summable.of_nonneg_of_le hnn (fun z => by
        have := mul_le_mul_of_nonneg_left (hle z) (hp.1 x z); simpa using this) (hp.2.1 x)
    refine ⟨tsum_nonneg hnn, ?_⟩
    show ENNReal.ofReal (∑' z, p x z * stepProb p n z y) = _
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hsum, stepE_succ]
    congr 1; ext z
    rw [ENNReal.ofReal_mul (hp.1 x z), (ih z y).2]; rfl

lemma IsTransition.stepProb_eq (hp : IsTransition p) (n : ℕ) (x y : S) :
    stepProb p n x y = (stepE p n x y).toReal := by
  rw [← (hp.stepProb_spec n x y).2, ENNReal.toReal_ofReal (hp.stepProb_spec n x y).1]

/-- Partial sums of first-passage probabilities are at most one. -/
lemma IsTransition.sum_range_fpE_le_one (hp : IsTransition p) (N : ℕ) (x y : S) :
    ∑ n ∈ Finset.range N, fpE p (n + 1) x y ≤ 1 := by
  induction N generalizing x with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ']
    simp_rw [fpE_succ_succ]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), fpE_one]
    calc (∑' z, ∑ i ∈ Finset.range N,
            (if z = y then 0 else PE p x z * fpE p (i + 1) z y)) + PE p x y
        = (∑' z, if z = y then 0 else PE p x z * ∑ i ∈ Finset.range N, fpE p (i + 1) z y)
            + PE p x y := by
          congr 1; congr 1; ext z
          split_ifs <;> simp [Finset.mul_sum]
      _ ≤ (∑' z, if z = y then 0 else PE p x z) + PE p x y := by
          gcongr with z
          split_ifs
          · exact le_rfl
          · calc PE p x z * ∑ i ∈ Finset.range N, fpE p (i + 1) z y ≤ PE p x z * 1 := by
                  gcongr; exact ih z
              _ = PE p x z := mul_one _
      _ = 1 := by
          rw [add_comm, ← hp.sum_PE x, tsum_split_at (PE p x) y]

lemma IsTransition.rhoE_le_one (hp : IsTransition p) (x y : S) : rhoE p x y ≤ 1 := by
  unfold rhoE
  rw [ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun N => hp.sum_range_fpE_le_one N x y

lemma IsTransition.rhoE_ne_top (hp : IsTransition p) (x y : S) : rhoE p x y ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (hp.rhoE_le_one x y)

lemma fpE_le_rhoE (n : ℕ) (x y : S) : fpE p (n + 1) x y ≤ rhoE p x y :=
  ENNReal.le_tsum (f := fun n => fpE p (n + 1) x y) n

lemma IsTransition.fpE_le_one (hp : IsTransition p) (n : ℕ) (x y : S) : fpE p n x y ≤ 1 := by
  cases n with
  | zero => simp [fpE]
  | succ n => exact (fpE_le_rhoE n x y).trans (hp.rhoE_le_one x y)

lemma IsTransition.fpE_ne_top (hp : IsTransition p) (n : ℕ) (x y : S) : fpE p n x y ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (hp.fpE_le_one n x y)

lemma IsTransition.firstPassage_spec (hp : IsTransition p) (n : ℕ) (x y : S) :
    0 ≤ firstPassage p (n + 1) x y ∧
      ENNReal.ofReal (firstPassage p (n + 1) x y) = fpE p (n + 1) x y := by
  induction n generalizing x with
  | zero => exact ⟨hp.1 x y, rfl⟩
  | succ n ih =>
    have hle : ∀ z, firstPassage p (n + 1) z y ≤ 1 := fun z => by
      have := hp.fpE_le_one (n + 1) z y
      rw [← (ih z).2] at this
      exact (ENNReal.ofReal_le_one).1 this
    have hnn : ∀ z, 0 ≤ (if z = y then 0 else p x z * firstPassage p (n + 1) z y) := fun z => by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (hp.1 x z) (ih z).1
    have hsum : Summable (fun z => if z = y then 0 else p x z * firstPassage p (n + 1) z y) :=
      Summable.of_nonneg_of_le hnn (fun z => by
        split_ifs
        · exact hp.1 x z
        · have := mul_le_mul_of_nonneg_left (hle z) (hp.1 x z); simpa using this) (hp.2.1 x)
    refine ⟨tsum_nonneg hnn, ?_⟩
    show ENNReal.ofReal (∑' z, if z = y then 0 else p x z * firstPassage p (n + 1) z y) = _
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hsum, fpE_succ_succ]
    congr 1; ext z
    split_ifs
    · simp
    · rw [ENNReal.ofReal_mul (hp.1 x z), (ih z).2]; rfl

lemma IsTransition.firstPassage_eq (hp : IsTransition p) (n : ℕ) (x y : S) :
    firstPassage p (n + 1) x y = (fpE p (n + 1) x y).toReal := by
  rw [← (hp.firstPassage_spec n x y).2, ENNReal.toReal_ofReal (hp.firstPassage_spec n x y).1]

lemma IsTransition.hitProb_eq (hp : IsTransition p) (x y : S) :
    hitProb p x y = (rhoE p x y).toReal := by
  unfold hitProb rhoE
  rw [ENNReal.tsum_toReal_eq (fun n => hp.fpE_ne_top (n + 1) x y)]
  simp_rw [hp.firstPassage_eq]

lemma IsTransition.recurrent_iff (hp : IsTransition p) (y : S) :
    Recurrent p y ↔ rhoE p y y = 1 := by
  unfold Recurrent
  rw [hp.hitProb_eq]
  constructor
  · intro h
    have := (ENNReal.toReal_eq_one_iff _).1 h
    exact this
  · intro h; rw [h]; simp

lemma IsTransition.hitProb_pos_iff (hp : IsTransition p) (x y : S) :
    0 < hitProb p x y ↔ 0 < rhoE p x y := by
  rw [hp.hitProb_eq, ENNReal.toReal_pos_iff]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, lt_of_le_of_lt (hp.rhoE_le_one x y) ENNReal.one_lt_top⟩

/-- A series of finite `ℝ≥0∞` terms has summable real parts iff its sum is finite. -/
lemma summable_toReal_iff {ι : Type*} {g : ι → ℝ≥0∞} (hg : ∀ i, g i ≠ ⊤) :
    Summable (fun i => (g i).toReal) ↔ ∑' i, g i ≠ ⊤ := by
  constructor
  · intro h
    have h' : Summable (fun i => (g i).toNNReal) := by
      rw [← NNReal.summable_coe]; exact h.congr (fun i => rfl)
    have := ENNReal.tsum_coe_ne_top_iff_summable.2 h'
    simpa [ENNReal.coe_toNNReal (hg _)] using this
  · exact ENNReal.summable_toReal

/-! ## Chapman–Kolmogorov and the renewal identity -/

lemma stepE_add (n m : ℕ) (x y : S) :
    stepE p (n + m) x y = ∑' z, stepE p n x z * stepE p m z y := by
  induction n generalizing x with
  | zero =>
    simp only [zero_add, stepE_zero]
    rw [tsum_eq_single x (fun z hz => by rw [if_neg (Ne.symm hz), zero_mul])]
    simp
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by ring, stepE_succ]
    simp_rw [ih, stepE_succ, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    congr 1; ext z; congr 1; ext w; ring

lemma stepE_succ' (n : ℕ) (x y : S) :
    stepE p (n + 1) x y = ∑' z, stepE p n x z * PE p z y := by
  rw [stepE_add n 1]
  congr 1; ext z
  congr 1
  rw [stepE_succ]
  rw [tsum_eq_single y (fun w hw => by simp [stepE_zero, hw])]
  simp [stepE_zero]

/-- The renewal identity `pⁿ⁺¹(x,y) = ∑_{m ≤ n} f^{m+1}(x,y) p^{n-m}(y,y)`. -/
lemma stepE_renewal (n : ℕ) (x y : S) :
    stepE p (n + 1) x y =
      ∑ m ∈ Finset.range (n + 1), fpE p (m + 1) x y * stepE p (n - m) y y := by
  induction n generalizing x with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_self, fpE_one]
    rw [stepE_succ, tsum_eq_single y (fun z hz => by simp [stepE_zero, hz])]
  | succ n ih =>
    rw [stepE_succ, tsum_split_at _ y, Finset.sum_range_succ']
    simp only [Nat.sub_zero]
    rw [add_comm]
    congr 1
    have : ∀ z, (if z = y then 0 else PE p x z * stepE p (n + 1) z y) =
        ∑ m ∈ Finset.range (n + 1),
          (if z = y then 0 else PE p x z * fpE p (m + 1) z y) * stepE p (n - m) y y := by
      intro z
      split_ifs
      · simp [*]
      · rw [ih z, Finset.mul_sum]
        congr 1; ext m; ring
    simp_rw [this]
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    congr 1; ext m
    rw [ENNReal.tsum_mul_right, ← fpE_succ_succ]
    congr 2
    omega

lemma fpE_le_stepE (n : ℕ) (x y : S) : fpE p (n + 1) x y ≤ stepE p (n + 1) x y := by
  rw [stepE_renewal]
  have := Finset.single_le_sum (f := fun m => fpE p (m + 1) x y * stepE p (n - m) y y)
    (fun _ _ => by positivity) (Finset.self_mem_range_succ n)
  simpa [stepE_zero] using this

lemma exists_stepE_pos_of_rhoE_pos {x y : S} (h : 0 < rhoE p x y) :
    ∃ n, 0 < stepE p (n + 1) x y := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  have : rhoE p x y = 0 := by
    unfold rhoE
    rw [ENNReal.tsum_eq_zero]
    intro n
    exact le_antisymm ((fpE_le_stepE n x y).trans (hcon n)) (by positivity)
  exact absurd this h.ne'

/-- Summed renewal identity: `G(x,y) = ρ_{xy} (1 + G(y,y))`. -/
lemma tsum_stepE_diag (y : S) : ∑' n, stepE p n y y = 1 + greenE p y y := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp [stepE_zero, greenE]

/-- Summed renewal identity: `G(x,y) = ρ_{xy} (1 + G(y,y))`. -/
lemma greenE_eq (x y : S) : greenE p x y = rhoE p x y * (1 + greenE p y y) := by
  rw [← tsum_stepE_diag, rhoE, ← ennreal_cauchy]
  unfold greenE
  simp_rw [stepE_renewal]

end Transition

end DurrettProbability

-- ===== Recurrence =====

open Filter
open scoped ENNReal

namespace DurrettProbability

variable {S : Type*} [DecidableEq S] {p : S → S → ℝ}

/-! ## Theorem 5.3.1: recurrence iff the return series diverges -/

/-- Truncated Cauchy product bound. -/
lemma cauchy_trunc_le (a b : ℕ → ℝ≥0∞) (N : ℕ) :
    ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range (n + 1), a m * b (n - m) ≤
      (∑ m ∈ Finset.range N, a m) * (∑ k ∈ Finset.range N, b k) := by
  set a' : ℕ → ℝ≥0∞ := fun m => if m < N then a m else 0
  set b' : ℕ → ℝ≥0∞ := fun m => if m < N then b m else 0
  have ha : ∑' m, a' m = ∑ m ∈ Finset.range N, a m := by
    rw [tsum_eq_sum (s := Finset.range N) (fun m hm => by simp_all [a'])]
    exact Finset.sum_congr rfl (fun m hm => by simp_all [a'])
  have hb : ∑' m, b' m = ∑ m ∈ Finset.range N, b m := by
    rw [tsum_eq_sum (s := Finset.range N) (fun m hm => by simp_all [b'])]
    exact Finset.sum_congr rfl (fun m hm => by simp_all [b'])
  rw [← ha, ← hb, ← ennreal_cauchy]
  calc ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range (n + 1), a m * b (n - m)
      = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range (n + 1), a' m * b' (n - m) := by
        refine Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun m hm => ?_))
        simp only [Finset.mem_range] at hn hm
        simp only [a', b']
        rw [if_pos (by omega), if_pos (by omega)]
    _ ≤ _ := ENNReal.sum_le_tsum _

lemma sum_range_stepE_le (N : ℕ) (y : S) :
    ∑ n ∈ Finset.range N, stepE p (n + 1) y y ≤
      rhoE p y y * (1 + ∑ n ∈ Finset.range N, stepE p (n + 1) y y) := by
  have eq : ∑ n ∈ Finset.range N, stepE p (n + 1) y y = ∑ n ∈ Finset.range N,
      ∑ m ∈ Finset.range (n + 1), fpE p (m + 1) y y * stepE p (n - m) y y :=
    Finset.sum_congr rfl (fun n _ => stepE_renewal n y y)
  have h := cauchy_trunc_le (fun m => fpE p (m + 1) y y) (fun k => stepE p k y y) N
  calc ∑ n ∈ Finset.range N, stepE p (n + 1) y y = _ := eq
    _ ≤ _ := h
    _ ≤ _ := by
      gcongr
      · exact ENNReal.sum_le_tsum _
      · calc ∑ k ∈ Finset.range N, stepE p k y y ≤ ∑ k ∈ Finset.range (N + 1), stepE p k y y :=
              Finset.sum_le_sum_of_subset (by simp)
          _ = _ := by rw [Finset.sum_range_succ']; simp [stepE_zero, add_comm]

lemma IsTransition.greenE_ne_top_of_rhoE_lt_one (hp : IsTransition p) {y : S}
    (h : rhoE p y y < 1) : greenE p y y ≠ ⊤ := by
  set r := (rhoE p y y).toReal with hr
  have hr1 : r < 1 := by
    have := ENNReal.toReal_strict_mono ENNReal.one_ne_top h
    simpa [hr] using this
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hbound : ∀ N, ∑ n ∈ Finset.range N, stepE p (n + 1) y y ≤ ENNReal.ofReal (r / (1 - r)) := by
    intro N
    set U := ∑ n ∈ Finset.range N, stepE p (n + 1) y y
    have hU : U ≠ ⊤ := ENNReal.sum_ne_top.2 (fun n _ => hp.stepE_ne_top _ _ _)
    have h1 := sum_range_stepE_le (p := p) N y
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (hp.rhoE_ne_top y y)
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hU⟩)) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_add ENNReal.one_ne_top hU] at h2
    simp only [ENNReal.toReal_one] at h2
    rw [← ENNReal.ofReal_toReal hU]
    apply ENNReal.ofReal_le_ofReal
    rw [le_div_iff₀ (by linarith)]
    rw [← hr] at h2
    nlinarith
  unfold greenE
  rw [ENNReal.tsum_eq_iSup_nat]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le hbound)

lemma greenE_eq_top_of_rhoE_eq_one {y : S} (h : rhoE p y y = 1) : greenE p y y = ⊤ := by
  by_contra hG
  have := greenE_eq (p := p) y y
  rw [h, one_mul] at this
  have h2 := congrArg ENNReal.toReal this
  rw [ENNReal.toReal_add ENNReal.one_ne_top hG] at h2
  simp at h2

lemma IsTransition.rhoE_eq_one_iff (hp : IsTransition p) (y : S) :
    rhoE p y y = 1 ↔ greenE p y y = ⊤ := by
  constructor
  · exact greenE_eq_top_of_rhoE_eq_one
  · intro hG
    by_contra hne
    exact hp.greenE_ne_top_of_rhoE_lt_one (lt_of_le_of_ne (hp.rhoE_le_one y y) hne) hG

lemma IsTransition.recurrent_iff_greenE (hp : IsTransition p) (y : S) :
    Recurrent p y ↔ greenE p y y = ⊤ := by
  rw [hp.recurrent_iff, hp.rhoE_eq_one_iff]

lemma IsTransition.summable_stepProb_iff (hp : IsTransition p) (x y : S) :
    Summable (fun n : ℕ => stepProb p (n + 1) x y) ↔ greenE p x y ≠ ⊤ := by
  simp_rw [hp.stepProb_eq]
  exact summable_toReal_iff (fun n => hp.stepE_ne_top _ _ _)

/-- **Durrett, Theorem 5.3.1.** -/
theorem recurrent_iff_sum_diverges_proof {S : Type*} [Countable S] [DecidableEq S]
    (p : S → S → ℝ) (hp : IsTransition p) (y : S) :
    Recurrent p y ↔ ¬ Summable (fun n : ℕ => stepProb p (n + 1) y y) := by
  rw [hp.recurrent_iff_greenE, hp.summable_stepProb_iff, not_not]

/-! ## Theorem 5.3.2: recurrence is contagious -/

lemma rhoE_first_step (z x : S) :
    rhoE p z x = PE p z x + ∑' w, if w = x then 0 else PE p z w * rhoE p w x := by
  unfold rhoE
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [zero_add, fpE_one]
  congr 1
  simp_rw [fpE_succ_succ]
  rw [ENNReal.tsum_comm]
  congr 1; ext w
  split_ifs
  · simp
  · rw [ENNReal.tsum_mul_left]

/-- `H(w) = P_w(the chain ever visits x at a time ≥ 0)`. -/
noncomputable def hitFromE (p : S → S → ℝ) (x w : S) : ℝ≥0∞ := if w = x then 1 else rhoE p w x

lemma sum_PE_hitFromE (z x : S) : ∑' w, PE p z w * hitFromE p x w = rhoE p z x := by
  rw [tsum_split_at _ x, rhoE_first_step z x]
  congr 1
  · simp [hitFromE]
  · congr 1; ext w; by_cases h : w = x <;> simp [hitFromE, h]

lemma harmonic_iterate {g : S → ℝ≥0∞} (hg : ∀ z, ∑' w, PE p z w * g w = g z) (n : ℕ) (z : S) :
    ∑' w, stepE p n z w * g w = g z := by
  induction n generalizing z with
  | zero =>
    rw [tsum_eq_single z (fun w hw => by rw [stepE_zero, if_neg (Ne.symm hw), zero_mul])]
    simp [stepE_zero]
  | succ n ih =>
    simp_rw [stepE_succ, ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    simp_rw [mul_assoc, ENNReal.tsum_mul_left, ih]
    exact hg z

lemma IsTransition.rhoE_eq_one_of_recurrent (hp : IsTransition p) {x y : S}
    (hx : rhoE p x x = 1) (hxy : 0 < rhoE p x y) : rhoE p y x = 1 := by
  by_cases hyx : y = x
  · subst hyx; exact hx
  have hharm : ∀ z, ∑' w, PE p z w * hitFromE p x w = hitFromE p x z := by
    intro z
    rw [sum_PE_hitFromE]
    by_cases hz : z = x
    · subst hz; simp [hitFromE, hx]
    · simp [hitFromE, hz]
  obtain ⟨n, hn⟩ := exists_stepE_pos_of_rhoE_pos hxy
  have hit : ∑' w, stepE p (n + 1) x w * hitFromE p x w = 1 := by
    rw [harmonic_iterate hharm (n + 1) x]; simp [hitFromE]
  by_contra hne
  have hlt : rhoE p y x < 1 := lt_of_le_of_ne (hp.rhoE_le_one y x) hne
  have hlt' : ∑' w, stepE p (n + 1) x w * hitFromE p x w < ∑' w, stepE p (n + 1) x w := by
    refine ENNReal.tsum_lt_tsum (i := y) ?_ ?_ ?_
    · rw [hit]; exact ENNReal.one_ne_top
    · intro w
      refine mul_le_of_le_one_right' ?_
      unfold hitFromE; split_ifs
      · exact le_rfl
      · exact hp.rhoE_le_one w x
    · simp only [hitFromE, if_neg hyx]
      calc stepE p (n + 1) x y * rhoE p y x < stepE p (n + 1) x y * 1 :=
            ENNReal.mul_lt_mul_right hn.ne' (hp.stepE_ne_top _ _ _) hlt
        _ = _ := mul_one _
  rw [hit, hp.sum_stepE] at hlt'
  exact lt_irrefl _ hlt'

lemma stepE_three_le (A N B : ℕ) (y x : S) :
    stepE p A y x * stepE p N x x * stepE p B x y ≤ stepE p (A + N + B) y y := by
  have h1 : stepE p A y x * stepE p N x x ≤ stepE p (A + N) y x := by
    rw [stepE_add]; exact ENNReal.le_tsum (f := fun z => stepE p A y z * stepE p N z x) x
  have h2 : stepE p (A + N) y x * stepE p B x y ≤ stepE p (A + N + B) y y := by
    rw [stepE_add (A + N) B]
    exact ENNReal.le_tsum (f := fun z => stepE p (A + N) y z * stepE p B z y) x
  calc _ ≤ stepE p (A + N) y x * stepE p B x y := by gcongr
    _ ≤ _ := h2

lemma greenE_eq_top_of {x y : S}
    (hx : greenE p x x = ⊤) (hxy : 0 < rhoE p x y) (hyx : 0 < rhoE p y x) :
    greenE p y y = ⊤ := by
  obtain ⟨a, ha⟩ := exists_stepE_pos_of_rhoE_pos hyx
  obtain ⟨b, hb⟩ := exists_stepE_pos_of_rhoE_pos hxy
  have hc : stepE p (a + 1) y x * stepE p (b + 1) x y ≠ 0 := mul_ne_zero ha.ne' hb.ne'
  have key : stepE p (a + 1) y x * stepE p (b + 1) x y * greenE p x x ≤ greenE p y y := by
    unfold greenE
    rw [← ENNReal.tsum_mul_left]
    calc ∑' n, stepE p (a + 1) y x * stepE p (b + 1) x y * stepE p (n + 1) x x
        ≤ ∑' n, stepE p ((n + (a + b + 2)) + 1) y y := by
          gcongr with n
          have := stepE_three_le (p := p) (a + 1) (n + 1) (b + 1) y x
          rw [show a + 1 + (n + 1) + (b + 1) = n + (a + b + 2) + 1 by ring] at this
          calc _ = stepE p (a + 1) y x * stepE p (n + 1) x x * stepE p (b + 1) x y := by ring
            _ ≤ _ := this
      _ ≤ ∑' n, stepE p (n + 1) y y :=
          ENNReal.tsum_comp_le_tsum_of_injective (f := fun n => n + (a + b + 2))
            (add_left_injective _) (fun n => stepE p (n + 1) y y)
  rw [hx, ENNReal.mul_top hc] at key
  exact top_le_iff.1 key

/-- **Durrett, Theorem 5.3.2.** -/
theorem recurrence_contagious_proof {S : Type*} [Countable S] [DecidableEq S]
    (p : S → S → ℝ) (hp : IsTransition p) (x y : S)
    (hx : Recurrent p x) (hxy : 0 < hitProb p x y) :
    Recurrent p y ∧ hitProb p y x = 1 := by
  rw [hp.hitProb_pos_iff] at hxy
  have hx1 := (hp.recurrent_iff x).1 hx
  have hyx := hp.rhoE_eq_one_of_recurrent hx1 hxy
  refine ⟨?_, ?_⟩
  · rw [hp.recurrent_iff_greenE]
    exact greenE_eq_top_of ((hp.recurrent_iff_greenE x).1 hx) hxy (by rw [hyx]; exact one_pos)
  · rw [hp.hitProb_eq, hyx]; simp

/-! ## Theorem 5.5.10: the support of a stationary distribution is recurrent -/

/-- The stationary distribution as an `ℝ≥0∞`-valued function. -/
noncomputable def piE (π : S → ℝ) (x : S) : ℝ≥0∞ := ENNReal.ofReal (π x)

omit [DecidableEq S] in
lemma StationaryDist.summable {π : S → ℝ} (hπ : StationaryDist p π) : Summable π := by
  by_contra h
  have := hπ.2.1
  rw [tsum_eq_zero_of_not_summable h] at this
  exact zero_ne_one this

omit [DecidableEq S] in
lemma StationaryDist.sum_piE {π : S → ℝ} (hπ : StationaryDist p π) : ∑' x, piE π x = 1 := by
  unfold piE
  rw [← ENNReal.ofReal_tsum_of_nonneg hπ.1 hπ.summable, hπ.2.1, ENNReal.ofReal_one]

omit [DecidableEq S] in
lemma StationaryDist.sum_piE_PE (hp : IsTransition p) {π : S → ℝ} (hπ : StationaryDist p π)
    (y : S) : ∑' x, piE π x * PE p x y = piE π y := by
  unfold piE PE
  have hnn : ∀ x, 0 ≤ π x * p x y := fun x => mul_nonneg (hπ.1 x) (hp.1 x y)
  have hs : Summable (fun x => π x * p x y) :=
    Summable.of_nonneg_of_le hnn (fun x => by
      have := mul_le_mul_of_nonneg_left (hp.le_one x y) (hπ.1 x); simpa using this) hπ.summable
  simp_rw [← ENNReal.ofReal_mul (hπ.1 _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs, hπ.2.2 y]

lemma StationaryDist.sum_piE_stepE (hp : IsTransition p) {π : S → ℝ} (hπ : StationaryDist p π)
    (n : ℕ) (y : S) : ∑' x, piE π x * stepE p n x y = piE π y := by
  induction n generalizing y with
  | zero =>
    rw [tsum_eq_single y (fun w hw => by rw [stepE_zero, if_neg hw, mul_zero])]
    simp [stepE_zero]
  | succ n ih =>
    simp_rw [stepE_succ', ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    simp_rw [← mul_assoc, ENNReal.tsum_mul_right, ih]
    exact hπ.sum_piE_PE hp y

lemma IsTransition.recurrent_of_stationary (hp : IsTransition p) {π : S → ℝ}
    (hπ : StationaryDist p π) {y : S} (hy : 0 < π y) : rhoE p y y = 1 := by
  by_contra hne
  have hG := hp.greenE_ne_top_of_rhoE_lt_one (lt_of_le_of_ne (hp.rhoE_le_one y y) hne)
  have hbound : ∀ x, greenE p x y ≤ 1 + greenE p y y := by
    intro x
    rw [greenE_eq]
    calc rhoE p x y * (1 + greenE p y y) ≤ 1 * (1 + greenE p y y) := by
          gcongr; exact hp.rhoE_le_one x y
      _ = _ := one_mul _
  have hsum : ∑' _n : ℕ, piE π y = ∑' x, piE π x * greenE p x y := by
    unfold greenE
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    congr 1; ext n
    exact (hπ.sum_piE_stepE hp (n + 1) y).symm
  have hle : ∑' x, piE π x * greenE p x y ≤ 1 + greenE p y y := by
    calc ∑' x, piE π x * greenE p x y ≤ ∑' x, piE π x * (1 + greenE p y y) := by
          gcongr with x; exact hbound x
      _ = 1 + greenE p y y := by rw [ENNReal.tsum_mul_right, hπ.sum_piE, one_mul]
  have htop : ∑' _n : ℕ, piE π y = ⊤ :=
    ENNReal.tsum_const_eq_top_of_ne_zero (by simp [piE, hy])
  rw [hsum] at htop
  rw [htop] at hle
  exact (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hG⟩) (top_le_iff.1 hle)

/-- **Durrett, Theorem 5.5.10.** -/
theorem stationary_support_recurrent_proof {S : Type*} [Countable S] [DecidableEq S]
    (p : S → S → ℝ) (hp : IsTransition p) (π : S → ℝ) (hπ : StationaryDist p π)
    (y : S) (hy : 0 < π y) : Recurrent p y :=
  (hp.recurrent_iff y).2 (hp.recurrent_of_stationary hπ hy)

end DurrettProbability

-- ===== MeanReturn =====

open Filter
open scoped ENNReal

namespace DurrettProbability

variable {S : Type*} [DecidableEq S] {p : S → S → ℝ}

/-! ## Theorem 5.5.11: the stationary probability is the reciprocal mean return time -/

/-- The kernel `p` with transitions into the taboo state `x` removed. -/
noncomputable def tabooK (p : S → S → ℝ) (x v w : S) : ℝ≥0∞ := if w = x then 0 else PE p v w

/-- Taboo probabilities `P_v(X_n = w, X_1, …, X_n ≠ x)`, powers of `tabooK`. -/
noncomputable def tabooE (p : S → S → ℝ) (x : S) : ℕ → S → S → ℝ≥0∞
  | 0, v, w => if v = w then 1 else 0
  | (n + 1), v, w => ∑' u, tabooK p x v u * tabooE p x n u w

lemma tabooE_zero (x v w : S) : tabooE p x 0 v w = if v = w then 1 else 0 := rfl

lemma tabooE_succ (x : S) (n : ℕ) (v w : S) :
    tabooE p x (n + 1) v w = ∑' u, tabooK p x v u * tabooE p x n u w := rfl

/-- Last-step form of the taboo recursion. -/
lemma tabooE_succ' (x : S) (n : ℕ) (v w : S) :
    tabooE p x (n + 1) v w = ∑' u, tabooE p x n v u * tabooK p x u w := by
  induction n generalizing v with
  | zero =>
    rw [tabooE_succ, tsum_eq_single w (fun u hu => by rw [tabooE_zero, if_neg hu, mul_zero]),
      tsum_eq_single v (fun u hu => by rw [tabooE_zero, if_neg (Ne.symm hu), zero_mul])]
    simp [tabooE_zero]
  | succ n ih =>
    rw [tabooE_succ]
    simp_rw [ih, tabooE_succ, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    congr 1; ext t; congr 1; ext u; ring

/-- First passage to `x` in `n + 1` steps: survive `n` taboo steps, then jump to `x`. -/
lemma fpE_eq_tabooE (x : S) (n : ℕ) (z : S) :
    fpE p (n + 1) z x = ∑' w, tabooE p x n z w * PE p w x := by
  induction n generalizing z with
  | zero =>
    rw [tsum_eq_single z (fun w hw => by rw [tabooE_zero, if_neg (Ne.symm hw), zero_mul])]
    simp [tabooE_zero, fpE_one]
  | succ n ih =>
    rw [fpE_succ_succ]
    have : ∀ v, (if v = x then 0 else PE p z v * fpE p (n + 1) v x) =
        tabooK p x z v * ∑' w, tabooE p x n v w * PE p w x := by
      intro v; rw [← ih v]; unfold tabooK; split_ifs <;> simp
    simp_rw [this, tabooE_succ, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    congr 1; ext w; congr 1; ext v; ring

lemma tabooE_succ_self (x : S) (n : ℕ) (v : S) : tabooE p x (n + 1) v x = 0 := by
  rw [tabooE_succ']
  simp [tabooK]

/-- The cycle measure `μ_x(w) = ∑_{n ≥ 0} P_x(X_n = w, T_x > n)`. -/
noncomputable def cycleE (p : S → S → ℝ) (x w : S) : ℝ≥0∞ := ∑' n, tabooE p x n x w

lemma cycleE_eq (x w : S) :
    cycleE p x w = (if x = w then 1 else 0) + ∑' n, tabooE p x (n + 1) x w := by
  rw [cycleE, tsum_eq_zero_add' ENNReal.summable, tabooE_zero]

lemma cycleE_self (x : S) : cycleE p x x = 1 := by
  rw [cycleE_eq]; simp [tabooE_succ_self]

lemma sum_tabooK_add (hp : IsTransition p) (x v : S) :
    (∑' w, tabooK p x v w) + PE p v x = 1 := by
  rw [← hp.sum_PE v, tsum_split_at (PE p v) x, add_comm]
  rfl

lemma cycleE_stationary {x : S} (hx : rhoE p x x = 1) (w : S) :
    ∑' v, cycleE p x v * PE p v w = cycleE p x w := by
  unfold cycleE
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  by_cases hw : w = x
  · subst hw
    rw [← cycleE, cycleE_self, ← hx, rhoE]
    congr 1; ext n
    rw [fpE_eq_tabooE]
  · rw [← cycleE, cycleE_eq, if_neg (Ne.symm hw), zero_add]
    congr 1; ext n
    rw [tabooE_succ']
    congr 1; ext v
    simp [tabooK, hw]

/-- Survival probabilities `s_n = P_x(T_x > n)`. -/
noncomputable def survE (p : S → S → ℝ) (x : S) (n : ℕ) : ℝ≥0∞ := ∑' w, tabooE p x n x w

lemma survE_succ_add (hp : IsTransition p) (x : S) (n : ℕ) :
    survE p x (n + 1) + fpE p (n + 1) x x = survE p x n := by
  unfold survE
  simp_rw [tabooE_succ']
  rw [ENNReal.tsum_comm, fpE_eq_tabooE]
  simp_rw [ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_add]
  congr 1; ext v
  rw [← mul_add, sum_tabooK_add hp, mul_one]

lemma survE_add_sum (hp : IsTransition p) (x : S) (n : ℕ) :
    survE p x n + ∑ m ∈ Finset.range n, fpE p (m + 1) x x = 1 := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, survE]
    rw [tsum_eq_single x (fun w hw => by rw [tabooE_zero, if_neg (Ne.symm hw)])]
    simp [tabooE_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, add_assoc (survE p x (n + 1)),
      add_comm (∑ m ∈ Finset.range n, _), ← add_assoc, survE_succ_add hp, ih]

lemma sum_add_tail (f : ℕ → ℝ≥0∞) (n : ℕ) :
    ∑' m, f m = ∑ m ∈ Finset.range n, f m + ∑' m, if n ≤ m then f m else 0 := by
  have h1 : ∑ m ∈ Finset.range n, f m = ∑' m, if m < n then f m else 0 := by
    rw [tsum_eq_sum (s := Finset.range n) (fun m hm => by
      simp only [Finset.mem_range] at hm; rw [if_neg hm])]
    exact Finset.sum_congr rfl (fun m hm => by simp only [Finset.mem_range] at hm; rw [if_pos hm])
  rw [h1, ← ENNReal.tsum_add]
  congr 1; ext m
  by_cases h : m < n
  · rw [if_pos h, if_neg (by omega), add_zero]
  · rw [if_neg h, if_pos (by omega), zero_add]

lemma survE_eq_tail (hp : IsTransition p) {x : S} (hx : rhoE p x x = 1) (n : ℕ) :
    survE p x n = ∑' m, if n ≤ m then fpE p (m + 1) x x else 0 := by
  have h1 := survE_add_sum hp x n
  have h2 := sum_add_tail (fun m => fpE p (m + 1) x x) n
  rw [← rhoE, hx] at h2
  have hA : ∑ m ∈ Finset.range n, fpE p (m + 1) x x ≠ ⊤ :=
    ENNReal.sum_ne_top.2 (fun m _ => hp.fpE_ne_top _ _ _)
  rw [add_comm (∑ m ∈ Finset.range n, fpE p (m + 1) x x)] at h2
  exact (ENNReal.add_left_inj hA).1 (h1.trans h2)

/-- `ℝ≥0∞` mean return time. -/
noncomputable def meanRetE (p : S → S → ℝ) (x : S) : ℝ≥0∞ :=
  ∑' n : ℕ, ((n : ℝ≥0∞) + 1) * fpE p (n + 1) x x

lemma sum_cycleE (hp : IsTransition p) {x : S} (hx : rhoE p x x = 1) :
    ∑' w, cycleE p x w = meanRetE p x := by
  unfold cycleE
  rw [ENNReal.tsum_comm]
  change ∑' n, survE p x n = _
  simp_rw [survE_eq_tail hp hx]
  rw [ENNReal.tsum_comm]
  unfold meanRetE
  congr 1; ext m
  rw [tsum_eq_sum (s := Finset.range (m + 1)) (fun n hn => by
    simp only [Finset.mem_range, not_lt] at hn; rw [if_neg (by omega)])]
  rw [Finset.sum_congr rfl (fun n hn => by
    simp only [Finset.mem_range] at hn; rw [if_pos (by omega : n ≤ m)])]
  simp

/-- Iterating a stationary measure. -/
lemma measure_iterate {m : S → ℝ≥0∞} (hm : ∀ z, ∑' y, m y * PE p y z = m z) (n : ℕ) (z : S) :
    ∑' y, m y * stepE p n y z = m z := by
  induction n generalizing z with
  | zero =>
    rw [tsum_eq_single z (fun w hw => by rw [stepE_zero, if_neg hw, mul_zero])]
    simp [stepE_zero]
  | succ n ih =>
    simp_rw [stepE_succ', ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    simp_rw [← mul_assoc, ENNReal.tsum_mul_right, ih]
    exact hm z

lemma piE_lower_bound (hp : IsTransition p) {π : S → ℝ} (hπ : StationaryDist p π) (x : S)
    (N : ℕ) (z : S) :
    piE π x * ∑ n ∈ Finset.range N, tabooE p x n x z ≤ piE π z := by
  induction N generalizing z with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ']
    by_cases hz : z = x
    · subst hz
      simp [tabooE_succ_self, tabooE_zero]
    · simp only [tabooE_zero, if_neg (Ne.symm hz), add_zero]
      simp_rw [tabooE_succ']
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      simp_rw [tabooK, if_neg hz, ← Finset.sum_mul]
      rw [← ENNReal.tsum_mul_left, ← hπ.sum_piE_PE hp z]
      refine ENNReal.tsum_le_tsum (fun y => ?_)
      rw [← mul_assoc]
      exact mul_le_mul' (ih y) le_rfl

lemma piE_cycle_le (hp : IsTransition p) {π : S → ℝ} (hπ : StationaryDist p π) (x z : S) :
    piE π x * cycleE p x z ≤ piE π z := by
  unfold cycleE
  rw [ENNReal.tsum_eq_iSup_nat, ENNReal.mul_iSup]
  exact iSup_le fun N => piE_lower_bound hp hπ x N z

lemma IsTransition.exists_stepE_pos (hp : IsTransition p) (hirr : Irreducible p) (x y : S) :
    ∃ n, 0 < stepE p (n + 1) x y :=
  exists_stepE_pos_of_rhoE_pos ((hp.hitProb_pos_iff x y).1 (hirr x y))

lemma piE_eq_cycle (hp : IsTransition p) (hirr : Irreducible p) {π : S → ℝ}
    (hπ : StationaryDist p π) {x : S} (hx : rhoE p x x = 1) (z : S) :
    piE π z = piE π x * cycleE p x z := by
  set a : S → ℝ≥0∞ := fun w => piE π x * cycleE p x w
  have hle : ∀ w, a w ≤ piE π w := fun w => piE_cycle_le hp hπ x w
  have ha : ∀ w, ∑' y, a y * PE p y w = a w := by
    intro w
    simp only [a]
    simp_rw [mul_assoc, ENNReal.tsum_mul_left, cycleE_stationary hx w]
  by_contra hne
  have hlt : a z < piE π z := lt_of_le_of_ne (hle z) (Ne.symm hne)
  obtain ⟨n, hn⟩ := hp.exists_stepE_pos hirr z x
  have hsum : ∑' y, a y * stepE p (n + 1) y x < ∑' y, piE π y * stepE p (n + 1) y x := by
    refine ENNReal.tsum_lt_tsum (i := z) ?_ ?_ ?_
    · rw [measure_iterate ha]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle x)
    · intro y; gcongr; exact hle y
    · exact ENNReal.mul_lt_mul_left hn.ne' (hp.stepE_ne_top _ _ _) hlt
  rw [measure_iterate ha, hπ.sum_piE_stepE hp] at hsum
  simp only [a, cycleE_self, mul_one] at hsum
  exact lt_irrefl _ hsum

omit [DecidableEq S] in
lemma StationaryDist.exists_pos {π : S → ℝ} (hπ : StationaryDist p π) : ∃ y, 0 < π y := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have : ∀ y, π y = 0 := fun y => le_antisymm (h y) (hπ.1 y)
  have h1 := hπ.2.1
  simp [this] at h1

/-- **Durrett, Theorem 5.5.11.** -/
theorem stationary_eq_inv_mean_return_proof {S : Type*} [Countable S] [DecidableEq S]
    (p : S → S → ℝ) (hp : IsTransition p) (hirr : Irreducible p)
    (π : S → ℝ) (hπ : StationaryDist p π) (x : S) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * firstPassage p (n + 1) x x)
      ∧ π x * meanReturnTime p x = 1 := by
  obtain ⟨y, hy⟩ := hπ.exists_pos
  have hyrec := stationary_support_recurrent_proof p hp π hπ y hy
  have hxrec := (recurrence_contagious_proof p hp y x hyrec (hirr y x)).1
  have hx : rhoE p x x = 1 := (hp.recurrent_iff x).1 hxrec
  -- total mass identity
  have hmass : piE π x * meanRetE p x = 1 := by
    rw [← sum_cycleE hp hx, ← ENNReal.tsum_mul_left, ← hπ.sum_piE]
    exact tsum_congr (fun z => (piE_eq_cycle hp hirr hπ hx z).symm)
  have hM : meanRetE p x ≠ ⊤ := by
    intro h
    rw [h] at hmass
    have hpos : piE π x ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hmass; exact zero_ne_one hmass
    rw [ENNReal.mul_top hpos] at hmass
    exact ENNReal.top_ne_one hmass
  have hterm : ∀ n : ℕ, ((n : ℝ) + 1) * firstPassage p (n + 1) x x =
      (((n : ℝ≥0∞) + 1) * fpE p (n + 1) x x).toReal := by
    intro n
    rw [ENNReal.toReal_mul, hp.firstPassage_eq, ENNReal.toReal_add (ENNReal.natCast_ne_top n)
      ENNReal.one_ne_top, ENNReal.toReal_natCast, ENNReal.toReal_one]
  have hfin : ∀ n : ℕ, ((n : ℝ≥0∞) + 1) * fpE p (n + 1) x x ≠ ⊤ := fun n =>
    ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩)
      (hp.fpE_ne_top _ _ _)
  refine ⟨?_, ?_⟩
  · simp_rw [hterm]
    exact (summable_toReal_iff hfin).2 hM
  · have hmr : meanReturnTime p x = (meanRetE p x).toReal := by
      unfold meanReturnTime meanRetE
      rw [ENNReal.tsum_toReal_eq hfin]
      exact tsum_congr hterm
    have hpx : π x = (piE π x).toReal := by
      rw [piE, ENNReal.toReal_ofReal (hπ.1 x)]
    rw [hmr, hpx, ← ENNReal.toReal_mul, hmass, ENNReal.toReal_one]

end DurrettProbability

-- ===== Convergence =====

open Filter Topology
open scoped ENNReal

namespace DurrettProbability

variable {S : Type*} [DecidableEq S] {p : S → S → ℝ}

/-! ## The convergence theorem (Durrett, Theorem 5.6.6) -/

/-! ### First-passage decomposition at a fixed state -/

/-- Decomposition of `pⁿ(s,t)` according to the first visit to `c` at a positive time. -/
lemma stepE_decomp (c : S) (n : ℕ) (s t : S) :
    stepE p n s t = ∑ m ∈ Finset.range n, fpE p (m + 1) s c * stepE p (n - 1 - m) c t
      + tabooE p c n s t := by
  induction n generalizing s with
  | zero => simp [stepE_zero, tabooE_zero]
  | succ n ih =>
    rw [stepE_succ, tsum_split_at _ c, Finset.sum_range_succ', tabooE_succ]
    simp only [Nat.sub_zero, Nat.add_sub_cancel]
    have : ∀ u, (if u = c then 0 else PE p s u * stepE p n u t) =
        ∑ m ∈ Finset.range n,
          (if u = c then 0 else PE p s u * fpE p (m + 1) u c) * stepE p (n - 1 - m) c t
        + tabooK p c s u * tabooE p c n u t := by
      intro u
      by_cases hu : u = c
      · simp [hu, tabooK]
      · simp only [if_neg hu, tabooK]
        rw [ih u, mul_add, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl (fun m _ => by ring)
    simp_rw [this]
    rw [ENNReal.tsum_add, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    have h2 : ∀ m ∈ Finset.range n, ∑' u,
        (if u = c then 0 else PE p s u * fpE p (m + 1) u c) * stepE p (n - 1 - m) c t =
        fpE p (m + 1 + 1) s c * stepE p (n - (m + 1)) c t := by
      intro m _
      rw [ENNReal.tsum_mul_right, ← fpE_succ_succ]
      congr 2
      omega
    rw [Finset.sum_congr rfl h2]
    simp only [zero_add, fpE_one]
    ring

/-- Survival probability identity for the taboo chain started anywhere. -/
lemma sum_tabooE_add (hp : IsTransition p) (c : S) (n : ℕ) (s : S) :
    ∑' t, tabooE p c n s t + ∑ m ∈ Finset.range n, fpE p (m + 1) s c = 1 := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    rw [tsum_eq_single s (fun w hw => by rw [tabooE_zero, if_neg (Ne.symm hw)])]
    simp [tabooE_zero]
  | succ n ih =>
    have key : ∑' t, tabooE p c (n + 1) s t + fpE p (n + 1) s c = ∑' t, tabooE p c n s t := by
      simp_rw [tabooE_succ']
      rw [ENNReal.tsum_comm, fpE_eq_tabooE]
      simp_rw [ENNReal.tsum_mul_left]
      rw [← ENNReal.tsum_add]
      congr 1; ext v
      rw [← mul_add, sum_tabooK_add hp, mul_one]
    rw [Finset.sum_range_succ, add_comm (∑ m ∈ Finset.range n, fpE p (m + 1) s c), ← add_assoc,
      key, ih]

lemma rhoE_pos_of_stepE_pos {a b : S} {n : ℕ} (h : 0 < stepE p (n + 1) a b) :
    0 < rhoE p a b := by
  rw [pos_iff_ne_zero] at h ⊢
  intro h0
  apply h
  rw [stepE_renewal]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  have : fpE p (m + 1) a b = 0 := le_antisymm (h0 ▸ fpE_le_rhoE m a b) (by positivity)
  rw [this, zero_mul]

/-! ### Aperiodicity: return probabilities are eventually positive -/

lemma stepE_pos_add {x : S} {m n : ℕ} (hm : 0 < stepE p m x x) (hn : 0 < stepE p n x x) :
    0 < stepE p (m + n) x x := by
  rw [stepE_add]
  exact lt_of_lt_of_le (ENNReal.mul_pos hm.ne' hn.ne')
    (ENNReal.le_tsum (f := fun z => stepE p m x z * stepE p n z x) x)

lemma IsTransition.eventually_stepE_pos_self (hp : IsTransition p) {x : S}
    (hx : Aperiodic p x) : ∃ N, ∀ n ≥ N, 0 < stepE p n x x := by
  set I : Set ℕ := {n | 1 ≤ n ∧ 0 < stepE p n x x}
  have hgcd : Nat.setGcd I = 1 := by
    apply hx
    intro n hn hpos
    apply Nat.setGcd_dvd_of_mem
    refine ⟨hn, ?_⟩
    rw [hp.stepProb_eq] at hpos
    exact (ENNReal.toReal_pos_iff.1 hpos).1
  obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge I
  have hcl : ∀ m ∈ AddSubmonoid.closure I, m = 0 ∨ 0 < stepE p m x x := by
    intro m hm
    induction hm using AddSubmonoid.closure_induction with
    | mem m hm => exact Or.inr hm.2
    | zero => exact Or.inl rfl
    | add a b _ _ ha hb =>
      rcases ha with ha | ha
      · subst ha; simpa using hb
      rcases hb with hb | hb
      · subst hb; simpa using Or.inr ha
      exact Or.inr (stepE_pos_add ha hb)
  refine ⟨max N 1, fun n hn => ?_⟩
  rcases hcl n (hN n (le_trans (le_max_left _ _) hn) (by rw [hgcd]; exact one_dvd n)) with h | h
  · have := le_trans (le_max_right N 1) hn; omega
  · exact h

lemma IsTransition.eventually_stepE_pos (hp : IsTransition p) (hirr : Irreducible p)
    (haper : ∀ x, Aperiodic p x) (x y : S) : ∃ N, ∀ n ≥ N, 0 < stepE p n x y := by
  obtain ⟨k, hk⟩ := hp.exists_stepE_pos hirr x y
  obtain ⟨N, hN⟩ := hp.eventually_stepE_pos_self (haper x)
  refine ⟨N + (k + 1), fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + (k + 1) := ⟨n - (k + 1), by omega⟩
  rw [stepE_add]
  exact lt_of_lt_of_le (ENNReal.mul_pos (hN m (by omega)).ne' hk.ne')
    (ENNReal.le_tsum (f := fun z => stepE p m x z * stepE p (k + 1) z y) x)

/-! ### Transfer from `ℝ≥0∞` sums to real sums -/

lemma real_tsum_of_ofReal {ι : Type*} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) {c : ℝ} (hc : 0 ≤ c)
    (h : ∑' i, ENNReal.ofReal (f i) = ENNReal.ofReal c) : Summable f ∧ ∑' i, f i = c := by
  have hs : Summable f := by
    have := (summable_toReal_iff (g := fun i => ENNReal.ofReal (f i))
      (fun _ => ENNReal.ofReal_ne_top)).2 (by rw [h]; exact ENNReal.ofReal_ne_top)
    exact this.congr (fun i => ENNReal.toReal_ofReal (hf i))
  refine ⟨hs, ?_⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg hf hs] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg hf) hc).1 h

/-! ### The product chain -/

/-- Two independent copies of the chain, run simultaneously. -/
noncomputable def prodK (p : S → S → ℝ) (a b : S × S) : ℝ := p a.1 b.1 * p a.2 b.2

omit [DecidableEq S] in
lemma PE_prodK (hp : IsTransition p) (a b : S × S) :
    PE (prodK p) a b = PE p a.1 b.1 * PE p a.2 b.2 := by
  unfold PE prodK
  rw [ENNReal.ofReal_mul (hp.1 _ _)]

omit [DecidableEq S] in
lemma tsum_prod_mul (f g : S → ℝ≥0∞) :
    ∑' b : S × S, f b.1 * g b.2 = (∑' b, f b) * (∑' b, g b) := by
  rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_right]
  congr 1; ext b1
  show ∑' b, f b1 * g b = f b1 * ∑' b, g b
  exact ENNReal.tsum_mul_left

omit [DecidableEq S] in
lemma IsTransition.prod (hp : IsTransition p) : IsTransition (prodK p) := by
  have h : ∀ a : S × S, ∑' b, ENNReal.ofReal (DurrettProbability.prodK p a b) = ENNReal.ofReal 1 := by
    intro a
    have : ∀ b, ENNReal.ofReal (DurrettProbability.prodK p a b) = PE p a.1 b.1 * PE p a.2 b.2 :=
      PE_prodK hp a
    simp_rw [this]
    rw [tsum_prod_mul (fun b => PE p a.1 b) (fun b => PE p a.2 b), hp.sum_PE, hp.sum_PE, mul_one,
      ENNReal.ofReal_one]
  refine ⟨fun a b => mul_nonneg (hp.1 _ _) (hp.1 _ _), fun a => ?_, fun a => ?_⟩
  · exact (real_tsum_of_ofReal (fun b => mul_nonneg (hp.1 _ _) (hp.1 _ _)) zero_le_one (h a)).1
  · exact (real_tsum_of_ofReal (fun b => mul_nonneg (hp.1 _ _) (hp.1 _ _)) zero_le_one (h a)).2

lemma stepE_prodK (hp : IsTransition p) (n : ℕ) (a b : S × S) :
    stepE (prodK p) n a b = stepE p n a.1 b.1 * stepE p n a.2 b.2 := by
  induction n generalizing a with
  | zero =>
    simp only [stepE_zero]
    by_cases h1 : a.1 = b.1 <;> by_cases h2 : a.2 = b.2 <;> simp [h1, h2, Prod.ext_iff]
  | succ n ih =>
    rw [stepE_succ, stepE_succ, stepE_succ]
    simp_rw [ih, PE_prodK hp]
    rw [← tsum_prod_mul (fun b1 => PE p a.1 b1 * stepE p n b1 b.1)
      (fun b2 => PE p a.2 b2 * stepE p n b2 b.2)]
    congr 1; ext u; ring

omit [DecidableEq S] in
lemma StationaryDist.prod (hp : IsTransition p) {π : S → ℝ} (hπ : StationaryDist p π) :
    StationaryDist (prodK p) (fun a => π a.1 * π a.2) := by
  refine ⟨fun a => mul_nonneg (hπ.1 _) (hπ.1 _), ?_, fun b => ?_⟩
  · refine (real_tsum_of_ofReal (fun a => mul_nonneg (hπ.1 _) (hπ.1 _)) zero_le_one ?_).2
    simp_rw [ENNReal.ofReal_mul (hπ.1 _)]
    rw [tsum_prod_mul (fun a => ENNReal.ofReal (π a)) (fun a => ENNReal.ofReal (π a))]
    have := hπ.sum_piE
    simp only [piE] at this
    rw [this, mul_one, ENNReal.ofReal_one]
  · refine (real_tsum_of_ofReal (fun a => mul_nonneg (mul_nonneg (hπ.1 _) (hπ.1 _))
      (mul_nonneg (hp.1 _ _) (hp.1 _ _))) (mul_nonneg (hπ.1 _) (hπ.1 _)) ?_).2
    have h1 : ∀ a : S × S, ENNReal.ofReal (π a.1 * π a.2 * (p a.1 b.1 * p a.2 b.2)) =
        (piE π a.1 * PE p a.1 b.1) * (piE π a.2 * PE p a.2 b.2) := by
      intro a
      unfold piE PE
      rw [ENNReal.ofReal_mul (mul_nonneg (hπ.1 _) (hπ.1 _)), ENNReal.ofReal_mul (hπ.1 _),
        ENNReal.ofReal_mul (hp.1 _ _)]
      ring
    simp_rw [h1]
    rw [tsum_prod_mul (fun a => piE π a * PE p a b.1) (fun a => piE π a * PE p a b.2),
      hπ.sum_piE_PE hp, hπ.sum_piE_PE hp]
    unfold piE
    rw [ENNReal.ofReal_mul (hπ.1 _)]

lemma IsTransition.irreducible_prodK (hp : IsTransition p) (hirr : Irreducible p)
    (haper : ∀ x, Aperiodic p x) : Irreducible (prodK p) := by
  intro a b
  rw [hp.prod.hitProb_pos_iff]
  obtain ⟨N1, h1⟩ := hp.eventually_stepE_pos hirr haper a.1 b.1
  obtain ⟨N2, h2⟩ := hp.eventually_stepE_pos hirr haper a.2 b.2
  refine rhoE_pos_of_stepE_pos (n := N1 + N2) ?_
  rw [stepE_prodK hp]
  exact ENNReal.mul_pos (h1 _ (by omega)).ne' (h2 _ (by omega)).ne'

/-! ### The coupling inequality -/

omit [DecidableEq S] in
lemma tsum_slice_fst_le (B : S × S → ℝ≥0∞) (y : S) : ∑' y2, B (y, y2) ≤ ∑' t, B t := by
  rw [ENNReal.tsum_prod']
  exact ENNReal.le_tsum (f := fun a => ∑' b, B (a, b)) y

omit [DecidableEq S] in
lemma tsum_slice_snd_le (B : S × S → ℝ≥0∞) (y : S) : ∑' y1, B (y1, y) ≤ ∑' t, B t := by
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  exact ENNReal.le_tsum (f := fun b => ∑' a, B (a, b)) y

/-- The coupling inequality: two copies of the chain agree on the event that the product
chain has visited `(w,w)`. -/
lemma coupling_bound (hp : IsTransition p) (w : S) (n : ℕ) (s : S × S) (y : S) :
    |stepProb p n s.1 y - stepProb p n s.2 y| ≤
      (∑' t, tabooE (prodK p) (w, w) n s t).toReal := by
  set c : S × S := (w, w)
  set G := ∑' t, tabooE (prodK p) c n s t
  set h := ∑ m ∈ Finset.range n, fpE (prodK p) (m + 1) s c * stepE p (n - 1 - m) w y
  have hdec := fun t => stepE_decomp (p := prodK p) c n s t
  have hmarg1 : stepE p n s.1 y = h + ∑' y2, tabooE (prodK p) c n s (y, y2) := by
    have e1 : stepE p n s.1 y = ∑' y2, stepE (prodK p) n s (y, y2) := by
      simp_rw [stepE_prodK hp]
      rw [ENNReal.tsum_mul_left, hp.sum_stepE, mul_one]
    rw [e1]
    simp_rw [hdec]
    rw [ENNReal.tsum_add, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [ENNReal.tsum_mul_left]
    simp_rw [stepE_prodK hp]
    rw [ENNReal.tsum_mul_left, hp.sum_stepE, mul_one]
  have hmarg2 : stepE p n s.2 y = h + ∑' y1, tabooE (prodK p) c n s (y1, y) := by
    have e1 : stepE p n s.2 y = ∑' y1, stepE (prodK p) n s (y1, y) := by
      simp_rw [stepE_prodK hp]
      rw [ENNReal.tsum_mul_right, hp.sum_stepE, one_mul]
    rw [e1]
    simp_rw [hdec]
    rw [ENNReal.tsum_add, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [ENNReal.tsum_mul_left]
    simp_rw [stepE_prodK hp]
    rw [ENNReal.tsum_mul_right, hp.sum_stepE, one_mul]
  have hb1 := tsum_slice_fst_le (tabooE (prodK p) c n s) y
  have hb2 := tsum_slice_snd_le (tabooE (prodK p) c n s) y
  have hG : G ≠ ⊤ := by
    have := sum_tabooE_add hp.prod c n s
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (this ▸ le_self_add)
  have hh : h ≠ ⊤ := ne_top_of_le_ne_top (hp.stepE_ne_top n s.1 y) (hmarg1 ▸ le_self_add)
  have hb1' : ∑' y2, tabooE (prodK p) c n s (y, y2) ≠ ⊤ := ne_top_of_le_ne_top hG hb1
  have hb2' : ∑' y1, tabooE (prodK p) c n s (y1, y) ≠ ⊤ := ne_top_of_le_ne_top hG hb2
  rw [hp.stepProb_eq, hp.stepProb_eq, hmarg1, hmarg2, ENNReal.toReal_add hh hb1',
    ENNReal.toReal_add hh hb2', add_sub_add_left_eq_sub, abs_le]
  have r1 := ENNReal.toReal_mono hG hb1
  have r2 := ENNReal.toReal_mono hG hb2
  have z1 : 0 ≤ (∑' y2, tabooE (prodK p) c n s (y, y2)).toReal := ENNReal.toReal_nonneg
  have z2 : 0 ≤ (∑' y1, tabooE (prodK p) c n s (y1, y)).toReal := ENNReal.toReal_nonneg
  constructor <;> linarith

/-- The taboo mass tends to zero when `c` is hit with probability one. -/
lemma tendsto_taboo_mass (hp : IsTransition p) {c s : S} (hs : rhoE p s c = 1) :
    Tendsto (fun n => (∑' t, tabooE p c n s t).toReal) atTop (𝓝 0) := by
  have h1 : ∀ n, (∑' t, tabooE p c n s t).toReal =
      1 - (∑ m ∈ Finset.range n, fpE p (m + 1) s c).toReal := by
    intro n
    have := sum_tabooE_add hp c n s
    have hA : ∑ m ∈ Finset.range n, fpE p (m + 1) s c ≠ ⊤ :=
      ENNReal.sum_ne_top.2 (fun m _ => hp.fpE_ne_top _ _ _)
    have hB : ∑' t, tabooE p c n s t ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (this ▸ le_self_add)
    have := congrArg ENNReal.toReal this
    rw [ENNReal.toReal_add hB hA, ENNReal.toReal_one] at this
    linarith
  simp_rw [h1]
  have h2 : Tendsto (fun n => (∑ m ∈ Finset.range n, fpE p (m + 1) s c).toReal) atTop (𝓝 1) := by
    have := ENNReal.tendsto_nat_tsum (fun m => fpE p (m + 1) s c)
    rw [← rhoE, hs] at this
    exact (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp this
  have := h2.const_sub 1
  simpa using this

/-! ### The theorem -/

/-- **Durrett, Theorem 5.6.6 (convergence theorem).** -/
theorem markov_convergence_proof {S : Type*} [Countable S] [DecidableEq S]
    (p : S → S → ℝ) (hp : IsTransition p) (hirr : Irreducible p)
    (haper : ∀ x, Aperiodic p x) (π : S → ℝ) (hπ : StationaryDist p π) (x y : S) :
    Tendsto (fun n : ℕ => stepProb p n x y) atTop (nhds (π y)) := by
  obtain ⟨w, hw⟩ := hπ.exists_pos
  have hpp := hp.prod
  have hπpp := hπ.prod hp
  have hirrpp := hp.irreducible_prodK hirr haper
  have hc : rhoE (prodK p) (w, w) (w, w) = 1 :=
    hpp.recurrent_of_stationary hπpp (show 0 < π w * π w from mul_pos hw hw)
  have hs : ∀ s, rhoE (prodK p) s (w, w) = 1 := fun s =>
    hpp.rhoE_eq_one_of_recurrent hc ((hpp.hitProb_pos_iff _ s).1 (hirrpp _ s))
  set g : ℕ → S → ℝ := fun n x2 => (∑' t, tabooE (prodK p) (w, w) n (x, x2) t).toReal with hg
  have hg0 : ∀ x2, Tendsto (fun n => g n x2) atTop (𝓝 0) := fun x2 =>
    tendsto_taboo_mass hpp (hs (x, x2))
  have hg_nn : ∀ n x2, 0 ≤ g n x2 := fun n x2 => ENNReal.toReal_nonneg
  have hg_le : ∀ n x2, g n x2 ≤ 1 := by
    intro n x2
    have := sum_tabooE_add hpp (w, w) n (x, x2)
    have hle : ∑' t, tabooE (prodK p) (w, w) n (x, x2) t ≤ 1 := this ▸ le_self_add
    have := ENNReal.toReal_mono ENNReal.one_ne_top hle
    simpa [hg] using this
  have hdom : Tendsto (fun n => ∑' x2, π x2 * g n x2) atTop (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (f := fun n x2 => π x2 * g n x2)
      (g := fun _ => (0 : ℝ)) (bound := π) hπ.summable
      (fun k => by simpa using (hg0 k).const_mul (π k))
      (Eventually.of_forall fun n k => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hπ.1 k) (hg_nn n k))]
        exact mul_le_of_le_one_right (hπ.1 k) (hg_le n k))
    simpa using this
  have hpiy : ∀ n, Summable (fun x2 => π x2 * stepProb p n x2 y) ∧
      ∑' x2, π x2 * stepProb p n x2 y = π y := by
    intro n
    refine real_tsum_of_ofReal (fun x2 => mul_nonneg (hπ.1 x2) (hp.stepProb_spec n x2 y).1)
      (hπ.1 y) ?_
    have := hπ.sum_piE_stepE hp n y
    simp_rw [ENNReal.ofReal_mul (hπ.1 _), (hp.stepProb_spec n _ y).2]
    exact this
  have hid : ∀ n, stepProb p n x y - π y =
      ∑' x2, π x2 * (stepProb p n x y - stepProb p n x2 y) := by
    intro n
    simp_rw [mul_sub]
    rw [Summable.tsum_sub (hπ.summable.mul_right _) (hpiy n).1, (hpiy n).2, tsum_mul_right,
      hπ.2.1, one_mul]
  have hbound : ∀ n, ‖stepProb p n x y - π y‖ ≤ ∑' x2, π x2 * g n x2 := by
    intro n
    have hterm : ∀ x2, ‖π x2 * (stepProb p n x y - stepProb p n x2 y)‖ ≤ π x2 * g n x2 := by
      intro x2
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ.1 x2)]
      exact mul_le_mul_of_nonneg_left (coupling_bound hp w n (x, x2) y) (hπ.1 x2)
    have hsg : Summable (fun x2 => π x2 * g n x2) :=
      Summable.of_nonneg_of_le (fun x2 => mul_nonneg (hπ.1 x2) (hg_nn n x2))
        (fun x2 => mul_le_of_le_one_right (hπ.1 x2) (hg_le n x2)) hπ.summable
    have hsn : Summable (fun x2 => ‖π x2 * (stepProb p n x y - stepProb p n x2 y)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsg
    rw [hid n]
    exact (norm_tsum_le_tsum_norm hsn).trans (Summable.tsum_le_tsum hterm hsn hsg)
  have := squeeze_zero_norm hbound hdom
  rw [tendsto_sub_nhds_zero_iff] at this
  exact this

end DurrettProbability

open DurrettProbability

theorem solution {S : Type*} [Countable S] [DecidableEq S]
    (p : S → S → ℝ) (hp : IsTransition p) (hirr : DurrettProbability.Irreducible p)
    (haper : ∀ x, Aperiodic p x) (π : S → ℝ) (hπ : StationaryDist p π) (x y : S) :
    Tendsto (fun n : ℕ => stepProb p n x y) atTop (nhds (π y)) :=
  DurrettProbability.markov_convergence_proof p hp hirr haper π hπ x y
