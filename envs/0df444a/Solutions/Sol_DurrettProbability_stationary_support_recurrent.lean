-- Prove2me | solution 1 for DurrettProbability.stationary_support_recurrent
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T07:08:47.559099+00:00
-- url     : https://prove2.me/submissions/de70bc69-1a5e-4ce4-960b-b67b711d8187

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

open DurrettProbability

theorem solution {S : Type*} [Countable S] [DecidableEq S]
    (p : S → S → ℝ) (hp : IsTransition p) (π : S → ℝ) (hπ : StationaryDist p π)
    (y : S) (hy : 0 < π y) : Recurrent p y :=
  DurrettProbability.stationary_support_recurrent_proof p hp π hπ y hy
