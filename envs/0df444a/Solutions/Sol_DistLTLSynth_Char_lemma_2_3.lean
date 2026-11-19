-- Prove2me | solution 1 for DistLTLSynth.Char.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-18T07:16:22.540279+00:00
-- url     : https://prove2.me/submissions/91a51345-dd18-49ae-a616-446f169bc0dc

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_Geometric

open DistLTLSynth DistLTLSynth.Char

/-- Step 1: both `δ(g)` and `2 - δ(g)` are ternary digits. -/
theorem delta_bounds (g : CommGraph) : 0 ≤ delta g ∧ delta g ≤ 2 := by
  cases g <;> decide

namespace P2MHole01_e6f70b52
/- The one-step update of `jIdx`, named for clarity: `step a g = 3 a + δ(g)` if `a` is
even, `3 a + (2 − δ(g))` if `a` is odd. -/
def step (a : ℕ) (g : CommGraph) : ℕ :=
  3 * a + if a % 2 = 0 then delta g else 2 - delta g

/-- `jIdx w` is the fold of `step` from `0`. -/
lemma jIdx_eq (w : List CommGraph) : jIdx w = w.foldl step 0 := by
  induction w with
  | nil =>
    dsimp [jIdx, step]
  | cons _ _ ih =>
    dsimp [jIdx, step]
    rfl

/-- One step of the recursion stays below the next ternary power: from
`a < 3^n` and a ternary digit `d ≤ 2`, the step `3 a + d` is `< 3^(n+1)`. -/
lemma step_bound {n : ℕ} (a : ℕ) (h : a < 3 ^ n) (g : CommGraph) :
    step a g < 3 ^ (n + 1) := by
  have hd : (if a % 2 = 0 then delta g else 2 - delta g) ≤ 2 := by
    split_ifs with hpar
    · exact (delta_bounds g).2
    · have hb := delta_bounds g
      omega
  rw [Nat.pow_succ']
  have h1 : a + 1 ≤ 3 ^ n := by omega
  have h2 : 3 * a + (if a % 2 = 0 then delta g else 2 - delta g) < 3 * (a + 1) := by omega
  have h3 : 3 * (a + 1) ≤ 3 * 3 ^ n := Nat.mul_le_mul_left 3 h1
  exact lt_of_lt_of_le h2 h3

/-- A fold of `step` starting below `3^r` stays below `3^(r + |w|)`. -/
lemma foldl_bound (r : ℕ) (a : ℕ) (ha : a < 3 ^ r) (w : List CommGraph) :
    w.foldl step a < 3 ^ (r + w.length) := by
  induction w generalizing r a ha with
  | nil =>
    simpa [List.length] using ha
  | cons g w ih =>
    rw [List.foldl_cons, List.length_cons]
    have hexp : r + (w.length + 1) = (r + 1) + w.length := by
      rw [Nat.add_comm w.length 1, Nat.add_assoc]
    rw [hexp]
    exact ih (r + 1) (step a g) (step_bound a ha g)

theorem solution (w : List CommGraph) : jIdx w < (3 : ℕ) ^ w.length := by
  simpa [jIdx_eq, Nat.add_zero] using foldl_bound 0 0 (by norm_num) w
end P2MHole01_e6f70b52

/-- Step 2: the Lemma 4.4 index stays in `{0, …, 3^{|w|} - 1}`. -/
theorem j_range (w : List CommGraph) : jIdx w < 3 ^ w.length := by
  (first | exact P2MHole01_e6f70b52.solution w | (apply P2MHole01_e6f70b52.solution <;> assumption))

namespace P2MHole02_38460967
/- Step 2 of lemma_2_3: J(h ++ [g]) ⊆ J h.

  Unfolding the foldl definition of jIdx by one step gives
    jIdx (h ++ [g]) = 3 * jIdx h + d    with    d = (if jIdx h even then δ(g) else 2 - δ(g))
  and d ∈ {0, 1, 2}.  Writing j = jIdx h, n = h.length we have
  J(h ++ [g]) = [ (3j+d)/3^(n+1), (3j+d+1)/3^(n+1) ] and J h = [ j/3^n, (j+1)/3^n ],
  with 3j/3^(n+1) = j/3^n and (3j+3)/3^(n+1) = (j+1)/3^n, and 3j ≤ 3j+d, 3j+d+1 ≤ 3j+3,
  so J(h ++ [g]) ⊆ J h. -/

/-- The one-step map of the `jIdx` recursion (Lemma 4.4), made explicit. -/
def jStep (a : ℕ) (g : CommGraph) : ℕ :=
  3 * a + if a % 2 = 0 then delta g else 2 - delta g

/-- `jIdx` is the foldl of `jStep` from `0`. -/
lemma jIdx_unfold (h : List CommGraph) : jIdx h = List.foldl jStep 0 h := rfl

/-- Folding over a singleton list applies the step once. -/
lemma foldl_single {α β : Type} (f : α → β → α) (a : α) (b : β) :
    List.foldl f a [b] = f a b := rfl

/-- One unfolding step of the `jIdx` recursion: appending `g` multiplies the index by 3 and
adds the ternary digit chosen by the parity of the current index. -/
lemma jIdx_append_one (h : List CommGraph) (g : CommGraph) :
    jIdx (h ++ [g]) = 3 * jIdx h + (if jIdx h % 2 = 0 then delta g else 2 - delta g) := by
  rw [jIdx_unfold]
  rw [List.foldl_append]
  rw [← jIdx_unfold]
  rw [foldl_single]
  unfold jStep
  rfl

/-- The digit added in `jIdx_append_one` is a ternary digit: `0 ≤ d ≤ 2`. -/
lemma jIdx_append_one_digit (h : List CommGraph) (g : CommGraph) :
    0 ≤ (if jIdx h % 2 = 0 then delta g else 2 - delta g) ∧
      (if jIdx h % 2 = 0 then delta g else 2 - delta g) ≤ 2 := by
  have hd : 0 ≤ delta g ∧ delta g ≤ 2 := delta_bounds g
  split_ifs
  · exact hd
  · constructor <;> omega

/-- J(h ++ [g]) ⊆ J h: the length-`|h|+1` interval indexed by `jIdx (h ++ [g])` is one of the
three subintervals of the length-`|h|` interval indexed by `jIdx h`. -/
theorem solution (h : List CommGraph) (g : CommGraph) : J (h ++ [g]) ⊆ J h := by
  intro x hx
  have hstep : jIdx (h ++ [g]) =
      3 * jIdx h + (if jIdx h % 2 = 0 then delta g else 2 - delta g) :=
    jIdx_append_one h g
  have hdig : 0 ≤ (if jIdx h % 2 = 0 then delta g else 2 - delta g) ∧
      (if jIdx h % 2 = 0 then delta g else 2 - delta g) ≤ 2 :=
    jIdx_append_one_digit h g
  set n : ℕ := h.length with hn
  set j : ℝ := (jIdx h : ℝ) with hj
  set d : ℝ := (if jIdx h % 2 = 0 then ↑(delta g) else ↑(2 - delta g)) with hd
  have hd0 : 0 ≤ d := by
    rw [hd]
    split_ifs
    · exact_mod_cast (delta_bounds g).1
    · exact_mod_cast (Nat.zero_le (2 - delta g))
  have hd2 : d ≤ 2 := by
    rw [hd]
    split_ifs
    · exact_mod_cast (delta_bounds g).2
    · exact_mod_cast (Nat.sub_le 2 (delta g))
  simp only [J] at hx ⊢
  rw [hstep] at hx
  have hlen : (h ++ [g]).length = h.length + 1 := by
    simp [List.length_append, List.length_cons]
  rw [hlen] at hx
  push_cast at hx
  rcases hx with ⟨hxl, hxu⟩
  constructor
  · calc
      (j : ℝ) / 3 ^ n = 3 * j / 3 ^ (n + 1) := by
        field_simp [pow_succ]
        ring
      _ ≤ (3 * j + d) / 3 ^ (n + 1) := by
        exact (div_le_div_iff_of_pos_right (by positivity)).mpr (by linarith [hd0])
      _ ≤ x := hxl
  · calc
      x ≤ (3 * j + d + 1) / 3 ^ (n + 1) := hxu
      _ ≤ (3 * j + 3) / 3 ^ (n + 1) := by
        exact (div_le_div_iff_of_pos_right (by positivity)).mpr (by linarith [hd2])
      _ = (j + 1) / 3 ^ n := by
        field_simp [pow_succ]
        ring
end P2MHole02_38460967

/-- Step 3: one round of the ternary subdivision stays inside the parent interval. -/
theorem oneStep_J (h : List CommGraph) (g : CommGraph) : J (h ++ [g]) ⊆ J h := by
  (first | exact P2MHole02_38460967.solution h g | (apply P2MHole02_38460967.solution <;> assumption))

namespace P2MHole03_ff099dd6
/-- The recursion of Lemma 4.4 unfolds one step: appending one graph appends exactly one
ternary digit (0, 1 or 2) to the base-3 index. -/
theorem jIdx_cons (h : List CommGraph) (g : CommGraph) :
    jIdx (h ++ [g]) = 3 * jIdx h + (if jIdx h % 2 = 0 then delta g else 2 - delta g) := by
  unfold jIdx
  simp [List.foldl]

/-- Both endpoints of `J (h ++ [g])` lie in `J h`: appending one letter refines the interval. -/
theorem J_refine (h : List CommGraph) (g : CommGraph) : J (h ++ [g]) ⊆ J h := by
  intro x hx
  simp only [J] at hx ⊢
  let a := (jIdx h : ℝ)
  let A := (jIdx (h ++ [g]) : ℝ)
  have hd : (h ++ [g]).length = h.length + 1 := by simp [List.length_append]
  have hdelta : 0 ≤ delta g ∧ delta g ≤ 2 := delta_bounds g
  let t : ℝ := (if jIdx h % 2 = 0 then (delta g : ℝ) else (2 - delta g : ℝ))
  -- in reals: A = 3 a + t
  have heqR : A = 3 * a + t := by
    unfold t A a
    have hN : jIdx (h ++ [g]) = 3 * jIdx h + (if jIdx h % 2 = 0 then delta g else 2 - delta g) :=
      jIdx_cons h g
    split_ifs
    <;> simp_all
  -- t is a ternary digit: 0 ≤ t ≤ 2
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  have htnn : 0 ≤ t := by
    unfold t
    split_ifs
    · exact Nat.cast_nonneg (delta g : ℕ)
    · have h2 : (delta g : ℝ) ≤ 2 := Nat.cast_le.mpr hdelta.2
      have h0 : 0 ≤ (delta g : ℝ) := Nat.cast_nonneg (delta g : ℕ)
      linarith [h2, h0]
  have htub : t ≤ 2 := by
    unfold t
    split_ifs
    · exact Nat.cast_le.mpr hdelta.2
    · have h2 : (delta g : ℝ) ≤ 2 := Nat.cast_le.mpr hdelta.2
      have h0 : 0 ≤ (delta g : ℝ) := Nat.cast_nonneg (delta g : ℕ)
      linarith [h2, h0]
  -- left endpoint goes up: a/3^|h| ≤ A/3^(|h|+1)  ⟺  a·3^|h| ≤ A·3^|h|·3
  have hL : a / 3 ^ h.length ≤ A / 3 ^ (h ++ [g]).length := by
    unfold a A
    rw [hd, pow_succ]
    refine (div_le_div_iff₀ (pow_pos (by norm_num) _) (mul_pos (pow_pos (by norm_num) _) (by norm_num))).mpr ?_
    have hpos : 0 < (3 : ℝ) ^ h.length := pow_pos (by norm_num) _
    have h1 : a * 3 ≤ A := by linarith [htnn]
    calc
      a * ((3 : ℝ) ^ h.length * 3) = (a * 3) * (3 : ℝ) ^ h.length := by ring
      _ ≤ A * (3 : ℝ) ^ h.length := mul_le_mul_of_nonneg_right h1 hpos.le
  -- right endpoint goes down: (A + 1)/3^(|h|+1) ≤ (a + 1)/3^|h|  ⟺  A + 1 ≤ 3(a + 1)
  have hU : (A + 1) / 3 ^ (h ++ [g]).length ≤ (a + 1) / 3 ^ h.length := by
    unfold a A
    rw [hd, pow_succ]
    refine (div_le_div_iff₀ (mul_pos (pow_pos (by norm_num) _) (by norm_num)) (pow_pos (by norm_num) _)).mpr ?_
    have hpos : 0 < (3 : ℝ) ^ h.length := pow_pos (by norm_num) _
    have hA : A + 1 ≤ (a + 1) * 3 := by linarith [htub]
    calc
      (A + 1) * (3 : ℝ) ^ h.length ≤ ((a + 1) * 3) * (3 : ℝ) ^ h.length :=
        mul_le_mul_of_nonneg_right hA hpos.le
      _ = (a + 1) * ((3 : ℝ) ^ h.length * 3) := by ring
  exact ⟨hL.trans hx.1, hx.2.trans hU⟩

theorem solution (h k : List CommGraph) (hp : h <+: k) : J k ⊆ J h := by
  obtain ⟨s, rfl⟩ := hp
  have H : ∀ (u : List CommGraph), J (u ++ s) ⊆ J u := by
    induction s with
    | nil =>
      intro u
      simp
    | cons a s' ih =>
      intro u
      calc
        J (u ++ a :: s') = J ((u ++ [a]) ++ s') := by rw [List.append_cons]
        _ ⊆ J (u ++ [a]) := ih (u ++ [a])
        _ ⊆ J u := J_refine u a
  exact H h
end P2MHole03_ff099dd6

/-- Step 4: the forward direction of Lemma 2.3, by appending one graph at a time. -/
theorem prefix_J_subset (h k : List CommGraph) (hp : h <+: k) : J k ⊆ J h := by
  (first | exact P2MHole03_ff099dd6.solution h k hp | (apply P2MHole03_ff099dd6.solution <;> assumption))

namespace P2MHole04_4a74d855
/-- Powers of 3 (as real numbers) are strictly increasing in the exponent. -/
theorem pow3_strict_mono {m n : ℕ} (h : m < n) : (3 : ℝ) ^ m < (3 : ℝ) ^ n := by
  have hstep : ∀ m : ℕ, (3 : ℝ) ^ m < (3 : ℝ) ^ (m + 1) := by
    intro m
    rw [pow_succ]
    have hm : 0 < (3 : ℝ) ^ m := pow_pos (by norm_num : 0 < (3 : ℝ)) m
    simp
  induction n with
  | zero =>
      exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
      by_cases hm : m = n
      · rw [hm]
        exact hstep _
      · have hmn : m < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hm
        calc
          (3 : ℝ) ^ m < (3 : ℝ) ^ n := ih hmn
          _ < (3 : ℝ) ^ (n + 1) := hstep _

theorem solution (h k : List CommGraph) (hs : J k ⊆ J h) : h.length ≤ k.length := by
  -- Unfold J so that hs states inclusion between the two Icc intervals
  dsimp [J] at hs
  -- lh, lk, rk, rh: left/right endpoints of J h, J k
  let lh : ℝ := (jIdx h : ℝ) / (3 : ℝ) ^ h.length
  let rh : ℝ := ((jIdx h : ℝ) + 1) / (3 : ℝ) ^ h.length
  let lk : ℝ := (jIdx k : ℝ) / (3 : ℝ) ^ k.length
  let rk : ℝ := ((jIdx k : ℝ) + 1) / (3 : ℝ) ^ k.length
  -- both endpoints of J k lie in J k, hence in J h
  have hd : 0 < (3 : ℝ) ^ k.length := pow_pos (by norm_num : 0 < (3 : ℝ)) k.length
  have hlkr : lk ≤ rk := by
    calc
      lk ≤ lk + 1 / (3 : ℝ) ^ k.length := by
        linarith [div_nonneg zero_le_one (le_of_lt hd)]
      _ = rk := by ring
  have hk_mem_l : lk ∈ Set.Icc lk rk := ⟨le_rfl, hlkr⟩
  have hk_mem_r : rk ∈ Set.Icc lk rk := ⟨hlkr, le_rfl⟩
  have hl : lh ≤ lk := (hs hk_mem_l).1
  have hkr : rk ≤ rh := (hs hk_mem_r).2
  -- J k's length is at most J h's length
  have hlen : 1 / (3 : ℝ) ^ k.length ≤ 1 / (3 : ℝ) ^ h.length := by
    calc
      1 / (3 : ℝ) ^ k.length = rk - lk := by ring
      _ ≤ rh - lk := sub_le_sub_right hkr _
      _ ≤ rh - lh := sub_le_sub_left hl _
      _ = 1 / (3 : ℝ) ^ h.length := by ring
  -- Hence 3^h.length ≤ 3^k.length
  have hpow : (3 : ℝ) ^ h.length ≤ (3 : ℝ) ^ k.length :=
    (one_div_le_one_div (pow_pos (by norm_num : 0 < (3 : ℝ)) k.length)
      (pow_pos (by norm_num : 0 < (3 : ℝ)) h.length)).mp hlen
  -- 3-powers are strictly increasing in the exponent, so h.length ≤ k.length
  by_contra hn
  have hlt : k.length < h.length := Nat.lt_of_not_ge hn
  have hcontra : (3 : ℝ) ^ k.length < (3 : ℝ) ^ h.length := pow3_strict_mono hlt
  exact lt_irrefl _ (lt_of_le_of_lt hpow hcontra)
end P2MHole04_4a74d855

/-- Step 5: a contained interval is no wider, so the parent history is no longer. -/
theorem J_subset_length_le (h k : List CommGraph) (hs : J k ⊆ J h) : h.length ≤ k.length := by
  (first | exact P2MHole04_4a74d855.solution h k hs | (apply P2MHole04_4a74d855.solution <;> assumption))

namespace P2MHole05_d5c825cb
/-- The ternary digit added by the recursion of Lemma 4.4 (`jIdx`) when extending a
history whose current index is `x` by the graph `g`: `3 * x + digit`. -/
def jStepDigit (x : ℕ) (g : CommGraph) : ℕ :=
  if x % 2 = 0 then delta g else 2 - delta g

/-- Every digit added by the recursion of Lemma 4.4 lies in `{0, 1, 2}`: the even
branch contributes `δ(g) ≤ 2` (Lemma `delta_bounds`) and the odd branch `2 - δ(g) ≤ 2`. -/
theorem jStepDigit_le_two (x : ℕ) (g : CommGraph) : jStepDigit x g ≤ 2 := by
  unfold jStepDigit
  split_ifs
  · exact (delta_bounds g).2
  · exact Nat.sub_le _ _

/-- `jIdx` as a fold starting from the current index: `j(h ++ t) = t.foldl (3· + digit) (j h)`. -/
theorem jIdx_foldl (h t : List CommGraph) :
    jIdx (h ++ t) = t.foldl (fun x g => 3 * x + jStepDigit x g) (jIdx h) := by
  simp [jIdx, jStepDigit, List.foldl_append]

/-- Ternary long division for `foldl`: if each step `x ↦ 3 * x + e x u` adds a digit `≤ 2`
(a ternary digit), then `t.foldl (·) a = a * 3^|t| + r` for some `r < 3^|t|`. -/
theorem foldl_digit_decomp {α : Type*} (e : ℕ → α → ℕ) (t : List α) (a : ℕ)
    (he : ∀ x u, e x u ≤ 2) :
    ∃ r, t.foldl (fun x u => 3 * x + e x u) a = a * 3 ^ t.length + r ∧ r < 3 ^ t.length := by
  induction t generalizing a with
  | nil => exact ⟨0, by simp, Nat.zero_lt_one⟩
  | cons u t' ih =>
      obtain ⟨r, hr, hlt⟩ := ih (3 * a + e a u)
      refine ⟨e a u * 3 ^ t'.length + r, ?_, ?_⟩
      · rw [List.foldl_cons, hr, List.length_cons, pow_succ]
        ring
      · rw [List.length_cons]
        have hb : e a u * 3 ^ t'.length + r < 2 * 3 ^ t'.length + 3 ^ t'.length :=
          Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right _ (he a u)) hlt
        have h3 : 2 * 3 ^ t'.length + 3 ^ t'.length = 3 * 3 ^ t'.length := by ring
        have hP : 3 * 3 ^ t'.length = 3 ^ (t'.length + 1) := by
          rw [Nat.pow_succ, Nat.mul_comm]
        exact lt_of_lt_of_le hb (le_of_eq (h3.trans hP))

theorem solution (h t : List CommGraph) :
  ∃ (r : ℕ), jIdx (h ++ t) = jIdx h * (3 : ℕ) ^ t.length + r ∧ r < (3 : ℕ) ^ t.length := by
  obtain ⟨r, hr, hlt⟩ := foldl_digit_decomp jStepDigit t (jIdx h) jStepDigit_le_two
  refine ⟨r, ?_, hlt⟩
  rw [jIdx_foldl, hr]
end P2MHole05_d5c825cb

/-- Step 6: appending `t` to `h` appends `|t|` ternary digits to the index. -/
theorem jIdx_take (h t : List CommGraph) :
    ∃ r, jIdx (h ++ t) = jIdx h * 3 ^ t.length + r ∧ r < 3 ^ t.length := by
  (first | exact P2MHole05_d5c825cb.solution h t | (apply P2MHole05_d5c825cb.solution <;> assumption))

namespace P2MHole06_7701f594
theorem solution (n m : ℕ) (hnle : n ≤ m) (a b c r : ℕ) (hc : c = b * (3 : ℕ) ^ (m - n) + r)
  (hr : r < (3 : ℕ) ^ (m - n)) (h1 : ↑a / (3 : ℝ) ^ n ≤ ↑c / (3 : ℝ) ^ m)
  (h2 : (↑c + (1 : ℝ)) / (3 : ℝ) ^ m ≤ (↑a + (1 : ℝ)) / (3 : ℝ) ^ n) : a = b := by
  set x : ℝ := (3 : ℝ) ^ (m - n) with hx
  have hpow : (3 : ℝ) ^ m = (3 : ℝ) ^ n * x := by
    rw [show (m : ℕ) = n + (m - n) from (Nat.add_sub_of_le hnle).symm, pow_add]
    <;> ring
  have hB : 0 < x := by
    positivity
  have hnn : (3 : ℝ) ^ n ≠ 0 := by
    positivity
  -- First inequality: a ≤ b
  have hab : a ≤ b := by
    have h1' : (↑a : ℝ) ≤ (↑c : ℝ) / x := by
      calc
        (↑a : ℝ) = (↑a : ℝ) / (3 : ℝ) ^ n * (3 : ℝ) ^ n := by field_simp [hnn]
        _ ≤ (↑c : ℝ) / (3 : ℝ) ^ m * (3 : ℝ) ^ n := by gcongr <;> positivity
        _ = (↑c : ℝ) / x := by rw [hpow]; field_simp [hnn, hB]
    have hcR : (↑c : ℝ) = (↑b : ℝ) * x + (↑r : ℝ) := by
      rw [hc, hx]
      norm_cast
    have hb1 : (↑c : ℝ) / x < (↑(b + 1) : ℝ) := by
      rw [hcR]
      have hrr : (↑r : ℝ) < x := by rw [hx]; exact_mod_cast hr
      have hlt1 : (↑r : ℝ) / x < 1 := by rw [div_lt_one hB]; exact hrr
      calc
        ((↑b : ℝ) * x + (↑r : ℝ)) / x = (↑b : ℝ) + (↑r : ℝ) / x := by field_simp [hB]
        _ < (↑b : ℝ) + 1 := by gcongr
        _ = (↑(b + 1) : ℝ) := by norm_cast
    have hlt : (↑a : ℝ) < (↑(b + 1) : ℝ) := lt_of_le_of_lt h1' hb1
    exact Nat.le_of_lt_succ (by exact_mod_cast hlt)
  -- Second inequality: b ≤ a
  have hba : b ≤ a := by
    have h2' : (↑(c + 1) : ℝ) / x ≤ (↑(a + 1) : ℝ) := by
      calc
        (↑(c + 1) : ℝ) / x = (↑(c + 1) : ℝ) / (3 : ℝ) ^ m * (3 : ℝ) ^ n := by
          rw [hpow]
          field_simp [hnn, hB]
        _ ≤ (↑(a + 1) : ℝ) / (3 : ℝ) ^ n * (3 : ℝ) ^ n := by
          apply mul_le_mul
          · simpa using h2
          · exact le_rfl
          · positivity
          · positivity
        _ = (↑(a + 1) : ℝ) := by field_simp [hnn]
    have hcR : (↑(c + 1) : ℝ) = (↑b : ℝ) * x + (↑r : ℝ) + 1 := by
      rw [show (c + 1 : ℕ) = b * (3 : ℕ) ^ (m - n) + r + 1 by rw [hc], hx]
      norm_cast
    have hsplit : (↑(c + 1) : ℝ) / x = (↑b : ℝ) + ((↑r : ℝ) + 1) / x := by
      rw [hcR]
      field_simp [hB]
      ring
    have hpos : 0 < ((↑r : ℝ) + 1) / x := by positivity
    have hlt : (↑b : ℝ) < (↑(a + 1) : ℝ) := by
      calc
        (↑b : ℝ) < (↑b : ℝ) + ((↑r : ℝ) + 1) / x := by
          apply lt_add_of_pos_right
          exact hpos
        _ = (↑(c + 1) : ℝ) / x := by rw [hsplit]
        _ ≤ (↑(a + 1) : ℝ) := h2'
    exact Nat.le_of_lt_succ (by exact_mod_cast hlt)
  exact Nat.le_antisymm hab hba
end P2MHole06_7701f594

/-- Step 7: numerical core of the reverse direction. The two endpoints of `J k` lie in
`J h`, and `jIdx k = b * 3^(m-n) + r` with `r < 3^(m-n)`, forces `a = b`
(where `a = jIdx h`, `b = jIdx (k.take n)`). -/
theorem J_subset_digit (n m : ℕ) (hnle : n ≤ m) (a b c r : ℕ)
    (hc : c = b * 3 ^ (m - n) + r) (hr : r < 3 ^ (m - n))
    (h1 : (a : ℝ) / 3 ^ n ≤ (c : ℝ) / 3 ^ m)
    (h2 : ((c : ℝ) + 1) / 3 ^ m ≤ ((a : ℝ) + 1) / 3 ^ n) : a = b := by
  (first | exact P2MHole06_7701f594.solution n m hnle a b c r hc hr h1 h2 | (apply P2MHole06_7701f594.solution <;> assumption))

namespace P2MHole07_32f4ff27
/-- The ternary digit added by one step of the Lemma 4.4 recursion:
`δ(g)` if the current index is even, `2 - δ(g)` if it is odd. -/
def stepDigit (a : ℕ) (g : CommGraph) : ℕ :=
  if a % 2 = 0 then delta g else 2 - delta g

/-- One step of the recursion: `stepFn a g = 3 a + stepDigit a g`. -/
def stepFn (a : ℕ) (g : CommGraph) : ℕ := 3 * a + stepDigit a g

/-- `δ` is injective: the three graphs carry the three distinct offsets 0, 1, 2. -/
theorem delta_injective (g g' : CommGraph) (h : delta g = delta g') : g = g' := by
  cases g <;> cases g' <;>
    (try exact rfl) <;>
    (try { dsimp [delta] at h; cases h })

/-- The digit added by a step is a ternary digit: `stepDigit a g ≤ 2`. -/
theorem stepDigit_bounds (a : ℕ) (g : CommGraph) : stepDigit a g ≤ 2 := by
  dsimp only [stepDigit]
  split_ifs
  · exact (delta_bounds g).2
  · omega

/-- A step stays in its ternary band: `3 a ≤ stepFn a g < 3 (a + 1)`. -/
theorem stepFn_bounds (a : ℕ) (g : CommGraph) : 3 * a ≤ stepFn a g ∧ stepFn a g < 3 * (a + 1) := by
  have hd : stepDigit a g ≤ 2 := stepDigit_bounds a g
  dsimp only [stepFn]
  constructor
  · omega
  · omega

/-- The last ternary digit of a step is exactly the digit added (it is < 3). -/
theorem stepFn_mod3 (a : ℕ) (g : CommGraph) : stepFn a g % 3 = stepDigit a g := by
  have hd : stepDigit a g ≤ 2 := stepDigit_bounds a g
  dsimp only [stepFn]
  omega

/-- A step is determined by its value: `stepFn a g = stepFn a' g'` gives `a = a'` and `g = g'`.
The bands `3 a ≤ stepFn a g < 3 (a+1)` force `a = a'`; then the last ternary digit, which is
the offset δ(g) read against the parity of `a`, forces `g = g'`. -/
theorem stepFn_surj (a a' : ℕ) (g g' : CommGraph) (h : stepFn a g = stepFn a' g') : a = a' ∧ g = g' := by
  have h1 : 3 * a ≤ stepFn a g := (stepFn_bounds a g).1
  have h2 : stepFn a g < 3 * (a + 1) := (stepFn_bounds a g).2
  have h1' : 3 * a' ≤ stepFn a' g' := (stepFn_bounds a' g').1
  have h2' : stepFn a' g' < 3 * (a' + 1) := (stepFn_bounds a' g').2
  have ha : a = a' := by omega
  subst ha
  have hmod : stepDigit a g = stepDigit a g' := by
    have hmod3 : stepFn a g % 3 = stepFn a g' % 3 := congrArg (fun x => x % 3) h
    have hdg : stepFn a g % 3 = stepDigit a g := stepFn_mod3 a g
    have hdg' : stepFn a g' % 3 = stepDigit a g' := stepFn_mod3 a g'
    simpa [← hdg, ← hdg'] using hmod3
  by_cases heq : a % 2 = 0
  · -- a even: the digit is δ(g) itself
    have hdg : stepDigit a g = delta g := by simpa [stepDigit, if_pos heq]
    have hdg' : stepDigit a g' = delta g' := by simpa [stepDigit, if_pos heq]
    have hdd : delta g = delta g' := by simpa [← hdg, ← hdg'] using hmod
    exact ⟨rfl, delta_injective g g' hdd⟩
  · -- a odd: the digit is 2 - δ(g)
    have hd2 : delta g ≤ 2 := (delta_bounds g).2
    have hd2' : delta g' ≤ 2 := (delta_bounds g').2
    have hsg : stepDigit a g = 2 - delta g := by simpa [stepDigit, if_neg heq]
    have hsg' : stepDigit a g' = 2 - delta g' := by simpa [stepDigit, if_neg heq]
    have hdd : delta g = delta g' := by
      rw [hsg, hsg'] at hmod
      omega
    exact ⟨rfl, delta_injective g g' hdd⟩

/-- Folding `l ++ [a]` from `b` folds `l` from `b`, then steps once with `a`. -/
theorem foldl_snoc {α β} (f : β → α → β) (l : List α) (a : α) :
    ∀ b : β, (l ++ [a]).foldl f b = f (l.foldl f b) a := by
  induction l with
  | nil =>
    intro b
    simp
  | cons x tl ih =>
    intro b
    rw [List.cons_append, List.foldl_cons]
    exact ih (f b x)

/-- The Lemma 4.4 recursion: appending one letter applies one step. -/
theorem jIdx_append (l : List CommGraph) (g : CommGraph) : jIdx (l ++ [g]) = stepFn (jIdx l) g := by
  dsimp only [jIdx, stepFn]
  exact foldl_snoc (fun a g => 3 * a + if a % 2 = 0 then delta g else 2 - delta g) l g 0

/-- Every nonempty list has a last letter: `h = t ++ [a]` for some `t` and `a`. -/
theorem exists_pop (h : List CommGraph) : h = [] ∨ ∃ t a, h = t ++ [a] := by
  induction h with
  | nil => left; rfl
  | cons a tl ih =>
    rcases ih with (hnil | ⟨t, a', htl⟩)
    · right
      use [], a
      simp [hnil]
    · right
      use a :: t, a'
      rw [htl, List.cons_append]

/-- If `t ++ [a]` has length `m + 1`, then `t` has length `m`. -/
theorem pop_len (t : List CommGraph) (a : CommGraph) (m : ℕ) (h : (t ++ [a]).length = m + 1) :
    t.length = m := by
  simp only [List.length_append, List.length_cons, List.length_nil] at h
  omega

/-- The edge index `j` of Lemma 4.4 is injective on histories of equal length:
`jIdx h = jIdx k` and `h.length = k.length` imply `h = k`. Induct on the length,
peeling off the last letter: the last ternary digit recovers it. -/
theorem solution (h k : List CommGraph) (hl : h.length = k.length) (hj : jIdx h = jIdx k) : h = k := by
  have aux : ∀ (n : ℕ) (h k : List CommGraph), h.length = n → k.length = n → jIdx h = jIdx k → h = k := by
    intro n
    induction n with
    | zero =>
      intro h k hh hk hj
      rw [List.length_eq_zero_iff] at hh hk
      subst hh hk
      exact rfl
    | succ m ih =>
      intro h k hh hk hj
      have hne : h ≠ [] := by
        intro he
        subst he
        simp only [List.length_nil] at hh
        omega
      have kne : k ≠ [] := by
        intro he
        subst he
        simp only [List.length_nil] at hk
        omega
      rcases (exists_pop h) with (hnil | ⟨t, a, hdec⟩)
      · contradiction
      rcases (exists_pop k) with (knil | ⟨u, b, kdec⟩)
      · contradiction
      have htl : t.length = m := by
        rw [hdec] at hh
        exact pop_len t a m hh
      have kutl : u.length = m := by
        rw [kdec] at hk
        exact pop_len u b m hk
      have hjstep : stepFn (jIdx t) a = stepFn (jIdx u) b := by
        rw [hdec, kdec, jIdx_append, jIdx_append] at hj
        exact hj
      obtain ⟨hjt, hab⟩ := stepFn_surj (jIdx t) (jIdx u) a b hjstep
      have ht : t = u := ih t u htl kutl hjt
      subst ht hab
      exact hdec.trans kdec.symm
  exact aux h.length h k rfl hl.symm hj
end P2MHole07_32f4ff27

/-- Step 8: `jIdx` is injective on histories of a fixed length (the base-3 digits, read with
the parity-guided rule, recover the graphs). -/
theorem j_idx_inj_same_len (h k : List CommGraph) (hl : h.length = k.length)
    (hj : jIdx h = jIdx k) : h = k := by
  (first | exact P2MHole07_32f4ff27.solution h k hl hj | (apply P2MHole07_32f4ff27.solution <;> assumption))

namespace P2MHole08_d04eb740
/-- The left endpoint of `J(w)` is below its right endpoint:
`j(w)/3^|w| ≤ (j(w)+1)/3^|w|`, since `3^|w| > 0` and `j(w) ≤ j(w) + 1`. -/
theorem j_left_le_right (w : List CommGraph) :
    (↑(jIdx w) : ℝ) / (3 : ℝ) ^ w.length ≤ (↑(jIdx w) + 1) / (3 : ℝ) ^ w.length := by
  gcongr
  nlinarith

theorem solution (h k : List CommGraph) (hs : J k ⊆ J h) :
  ↑(jIdx h) / (3 : ℝ) ^ h.length ≤ ↑(jIdx k) / (3 : ℝ) ^ k.length ∧
    (↑(jIdx k) + (1 : ℝ)) / (3 : ℝ) ^ k.length ≤ (↑(jIdx h) + (1 : ℝ)) / (3 : ℝ) ^ h.length := by
  constructor
  · -- The left endpoint of `J k` is a point of `J k`, hence of `J h`.
    have hx : (↑(jIdx k) : ℝ) / (3 : ℝ) ^ k.length ∈ J k := by
      rw [J]
      exact ⟨le_rfl, j_left_le_right k⟩
    rw [J] at hs
    exact (hs hx).1
  · -- The right endpoint of `J k` is a point of `J k`, hence of `J h`.
    have hx : ((↑(jIdx k) : ℝ) + 1) / (3 : ℝ) ^ k.length ∈ J k := by
      rw [J]
      exact ⟨j_left_le_right k, le_rfl⟩
    rw [J] at hs
    exact (hs hx).2
end P2MHole08_d04eb740

/-- Step 9: `J k ⊆ J h` is exactly the two endpoint inequalities. -/
theorem J_subset_endpoints (h k : List CommGraph) (hs : J k ⊆ J h) :
    (jIdx h : ℝ) / 3 ^ h.length ≤ (jIdx k : ℝ) / 3 ^ k.length ∧
    ((jIdx k : ℝ) + 1) / 3 ^ k.length ≤ ((jIdx h : ℝ) + 1) / 3 ^ h.length := by
  (first | exact P2MHole08_d04eb740.solution h k hs | (apply P2MHole08_d04eb740.solution <;> assumption))

/-- Lemma 2.3: for finite graph histories `h, k`, `h` is a prefix of `k` iff `J(k) ⊆ J(h)`. -/
theorem solution (h k : List CommGraph) : h <+: k ↔ J k ⊆ J h := by
  constructor
  · exact fun hp => prefix_J_subset h k hp
  · intro hs
    have hn : h.length ≤ k.length := J_subset_length_le h k hs
    set u := k.take h.length with hu0
    have hk : k = u ++ k.drop h.length :=
      (List.take_append_drop h.length k).symm
    obtain ⟨r, hr, hr2⟩ := jIdx_take u (k.drop h.length)
    have hr2' : r < 3 ^ (k.length - h.length) := by simpa [List.length_drop] using hr2
    have ⟨h1, h2⟩ := J_subset_endpoints h k hs
    have hc : jIdx k = jIdx u * 3 ^ (k.length - h.length) + r := by
      rw [hk.symm] at hr
      rw [← List.length_drop]
      exact hr
    have hab : jIdx u = jIdx h :=
      (J_subset_digit h.length k.length hn (jIdx h) (jIdx u) (jIdx k) r hc hr2' h1 h2).symm
    have hu : u = h := j_idx_inj_same_len u h (by rw [List.length_take, Nat.min_eq_left hn]) hab
    rw [← hu]
    exact List.take_prefix h.length k
