-- Prove2me | solution 1 for ErschlerZheng.exists_measure_mass_compl_ball_le_and_exp_le_growth_of_satisfiesFr
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T11:37:50.346038+00:00
-- url     : https://prove2.me/submissions/062d94f0-a38c-49da-9f1a-0faa68ea2a7f

import Mathlib
import Definitions.Def_ErschlerZheng_Walks
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_ErschlerZheng_Construction
import Theorems.Thm_ErschlerZheng_hasNontrivialPoissonBoundary_muBeta
import Theorems.Thm_ErschlerZheng_isProbability_and_hasFiniteEntropy_muBeta_and_mass_ball_compl_le
import Theorems.Thm_ErschlerZheng_exp_le_growth_of_hasNontrivialPoissonBoundary
import Theorems.Thm_ErschlerZheng_two_mul_lengthL_le_lengthL_succ
import Theorems.Thm_ErschlerZheng_isNondegenerate_muBeta

section
/-!
# Word balls: word length is subadditive, balls are finite, `v(K r) ⩽ ((2|S|+1) v(r))^K`
-/

namespace ErschlerZheng

namespace WordBallDev

open Pointwise

variable {G : Type*} [Group G]

theorem wordBall_mono (S : Set G) {m n : ℕ} (h : m ≤ n) : Chou.wordBall S m ⊆ Chou.wordBall S n :=
  fun _ ⟨l, hl, hls, he⟩ => ⟨l, le_trans hl h, hls, he⟩

theorem wordBall_mul_subset (S : Set G) (m n : ℕ) :
    Chou.wordBall S m * Chou.wordBall S n ⊆ Chou.wordBall S (m + n) := by
  rintro _ ⟨_, ⟨l, hl, hls, rfl⟩, _, ⟨l', hl', hls', rfl⟩, rfl⟩
  refine ⟨l ++ l', by simp; omega, ?_, by simp⟩
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hls x h
  · exact hls' x h

theorem wordBall_add_subset (S : Set G) (m n : ℕ) :
    Chou.wordBall S (m + n) ⊆ Chou.wordBall S m * Chou.wordBall S n := by
  rintro _ ⟨l, hl, hls, rfl⟩
  refine ⟨(l.take m).prod, ⟨l.take m, by simp, fun x hx => hls x (List.mem_of_mem_take hx), rfl⟩,
    (l.drop m).prod, ⟨l.drop m, by simp; omega, fun x hx => hls x (List.mem_of_mem_drop hx), rfl⟩,
    ?_⟩
  show (l.take m).prod * (l.drop m).prod = l.prod
  rw [← List.prod_append, List.take_append_drop]

theorem one_mem_wordBall (S : Set G) (n : ℕ) : (1 : G) ∈ Chou.wordBall S n :=
  ⟨[], by simp, by simp, rfl⟩

theorem exists_mem_wordBall (S : Set G) (g : G) (hg : g ∈ Subgroup.closure S) :
    ∃ n, g ∈ Chou.wordBall S n := by
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact ⟨1, [s], by simp, by simp [hs], by simp⟩
  | one => exact ⟨0, one_mem_wordBall S 0⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨m, hm⟩ := ihg
    obtain ⟨n, hn⟩ := ihh
    exact ⟨m + n, wordBall_mul_subset S m n ⟨g, hm, h, hn, rfl⟩⟩
  | inv g _ ihg =>
    obtain ⟨m, l, hl, hls, rfl⟩ := ihg
    refine ⟨m, (l.map (·⁻¹)).reverse, by simp; omega, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_reverse, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rcases hls y hy with h | h
      · right; simpa using h
      · left; exact h
    · rw [List.prod_inv_reverse]

theorem mem_wordBall_wordLength (S : Set G) (hS : Subgroup.closure S = ⊤) (g : G) :
    g ∈ Chou.wordBall S (wordLength S g) := by
  obtain ⟨n, hn⟩ := exists_mem_wordBall S g (by rw [hS]; trivial)
  exact Nat.sInf_mem (s := {n | g ∈ Chou.wordBall S n}) ⟨n, hn⟩

/-- The letters: `1`, the elements of `S`, and their inverses. -/
def letters (S : Finset G) : Set G := insert 1 ((S : Set G) ∪ (S : Set G)⁻¹)

theorem letters_finite (S : Finset G) : (letters S).Finite :=
  ((S.finite_toSet.union S.finite_toSet.inv)).insert 1

theorem wordBall_one_subset (S : Finset G) : Chou.wordBall (S : Set G) 1 ⊆ letters S := by
  rintro _ ⟨l, hl, hls, rfl⟩
  rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩
  · simp [letters]
  · simp only [List.prod_cons, List.prod_nil, mul_one]
    rcases hls x (by simp) with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · simp at hl

theorem wordBall_finite (S : Finset G) (n : ℕ) : (Chou.wordBall (S : Set G) n).Finite := by
  induction n with
  | zero =>
    refine Set.Finite.subset (Set.finite_singleton 1) ?_
    rintro _ ⟨l, hl, -, rfl⟩
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)]
    simp
  | succ n ih =>
    exact ((ih.mul (letters_finite S)).subset
      ((wordBall_add_subset _ n 1).trans (Set.mul_subset_mul_left (wordBall_one_subset S))))

end WordBallDev

end ErschlerZheng
end

section
/-!
# Basic facts about sections, `a`, and the generators `b_ω, c_ω, d_ω`

Development helpers for the Grigorchuk part of the Erschler–Zheng mission (not published).
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace GrigBasic

/-! ### Sections -/

/-! ### The root swap -/

/-! ### `a` and the generators -/

theorem grigA_mul_self : grigA * grigA = 1 :=
  Subtype.ext (Equiv.ext fun w => grigAFun_involutive w)

theorem grigA_inv : grigA⁻¹ = grigA := inv_eq_of_mul_eq_one_right grigA_mul_self

theorem vertex_smul_grigA (v : List Bool) : v <• grigA = grigAFun v := by
  rw [vertex_smul_def, grigA_inv]
  rfl

theorem gen_mul_self (ω : ℕ → Fin 3) (γ : BCD) : gen ω γ * gen ω γ = 1 :=
  Subtype.ext (Equiv.ext fun w => genFun_involutive ω γ w)

theorem gen_inv (ω : ℕ → Fin 3) (γ : BCD) : (gen ω γ)⁻¹ = gen ω γ :=
  inv_eq_of_mul_eq_one_right (gen_mul_self ω γ)

/-! ### Words -/

end GrigBasic

end ErschlerZheng
end

section
/-!
# The goal: Theorem 8.3 with `n` replaced by `2^n` (p. 58), as a reduction

`μ = μ_β` with `1 - 1/D < β < 1`, `β > 1 - ε/2`, `k = kLog A` (`A` a large multiple of `D`):
Theorem 7.13 gives the non-trivial boundary, Corollary 8.2 probability, finite entropy and
`μ(B(2^{2k_n}L_n)^c) ⩽ C 2^{-nβ}`; with `L_N ⩾ 2^{N-n}L_n` this is `⩽ C' 2^{-(1-ε/2)N}` at radius
`L_N`. Lemma 2.1 gives `v(mφ(ϱ_m)) ⩾ e^{c m}`; with `m ≈ 2^{(1-ε/2)n}`, `ϱ_m ⩽ L_n + 1` and the shell
bound `φ(L_n + 1) ⩽ L_0 + Σ_{k ⩽ n} L_{k+1} μ(|g| > L_k)`, `mφ(ϱ_m) ⩽ K n L_n ⩽ L_{n + j}`; polynomial
factors are absorbed by `ε/2 < ε`.
-/

open scoped RightActions
open Garrido Filter Topology

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace ErschlerZheng

namespace P3GoalDev

/-! ### `L^ω_n` -/

theorem lengthL_mono_pow (ω : ℕ → Fin 3) {n N : ℕ} (h : n ≤ N) :
    2 ^ (N - n) * lengthL ω n ≤ lengthL ω N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simp
  | succ d ih =>
    have := two_mul_lengthL_le_lengthL_succ ω (n + d)
    rw [show n + (d + 1) - n = (n + d - n) + 1 by omega, pow_succ, show n + (d + 1) = n + d + 1 by
      ring]
    nlinarith [ih (by omega)]

theorem lengthL_zero (ω : ℕ → Fin 3) : lengthL ω 0 = 3 := by
  simp [lengthL, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

theorem mulVec_one_le (i : Fin 3) (j : Fin 3) :
    Matrix.mulVec (substMatrix i) (fun _ => (1 : ℕ)) j ≤ 3 := by
  fin_cases i <;> fin_cases j <;> decide

theorem lengthL_succ_le (ω : ℕ → Fin 3) (n : ℕ) : lengthL ω (n + 1) ≤ 3 * lengthL ω n := by
  unfold lengthL
  rw [List.ofFn_succ', List.prod_concat, ← Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]
  set r := Matrix.vecMul (fun _ => (1 : ℕ)) (List.ofFn fun i : Fin n => substMatrix (ω i)).prod
  have : (fun _ : Fin 3 => (3 : ℕ)) = fun _ => 3 * 1 := by simp
  calc r ⬝ᵥ (Matrix.mulVec (substMatrix (ω n)) fun _ => 1) ≤ r ⬝ᵥ (fun _ => 3) := by
        unfold dotProduct
        exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_left _ (mulVec_one_le _ j)
    _ = 3 * (r ⬝ᵥ fun _ => 1) := by
        unfold dotProduct
        rw [Finset.mul_sum]
        congr 1; funext j; ring

theorem one_le_lengthL (ω : ℕ → Fin 3) (n : ℕ) : 1 ≤ lengthL ω n := by
  have := lengthL_mono_pow ω (Nat.zero_le n)
  rw [lengthL_zero] at this
  have : 1 ≤ 2 ^ (n - 0) := Nat.one_le_two_pow
  nlinarith

/-! ### Balls, masses, `φ` -/

section Gen

variable {Γ : Type*} [Group Γ]

theorem mass_mono {μ : Γ → ℝ} (hμ : IsProbability μ) {s t : Set Γ} (h : s ⊆ t) :
    mass μ s ≤ mass μ t := by
  unfold mass
  have hs : ∀ u : Set Γ, Summable (u.indicator μ) := fun u =>
    Summable.of_nonneg_of_le (fun x => Set.indicator_nonneg (fun x _ => hμ.1 x) x)
      (fun x => Set.indicator_le_self' (fun x _ => hμ.1 x) x) hμ.2.summable
  exact (hs s).tsum_le_tsum (fun x => Set.indicator_le_indicator_of_subset h (fun x => hμ.1 x) x)
    (hs t)

theorem mass_le_one {μ : Γ → ℝ} (hμ : IsProbability μ) (s : Set Γ) : mass μ s ≤ 1 := by
  have := mass_mono hμ (Set.subset_univ s)
  unfold mass at this ⊢
  simpa [hμ.2.tsum_eq] using this

theorem ball_mono (S : Set Γ) {r r' : ℝ} (h : r ≤ r') : ball S r ⊆ ball S r' :=
  fun g hg => le_trans hg h

theorem growth_mono (S : Finset Γ) {r r' : ℝ} (h : r ≤ r') :
    growth (S : Set Γ) r ≤ growth (S : Set Γ) r' := by
  unfold growth
  exact Nat.card_mono (WordBallDev.wordBall_finite S _)
    (WordBallDev.wordBall_mono _ (Nat.floor_mono h))

/-- `φ(r) = Σ_{|g| ⩽ r} |g| μ(g)` as a series over `Γ`. -/
theorem phi_eq (S : Finset Γ) (μ : Γ → ℝ) (r : ℝ) :
    ∑' g : ball (S : Set Γ) r, (wordLength (S : Set Γ) g : ℝ) * μ g =
      ∑' g, (ball (S : Set Γ) r).indicator (fun g => (wordLength (S : Set Γ) g : ℝ) * μ g) g :=
  tsum_subtype (ball (S : Set Γ) r) (fun g => (wordLength (S : Set Γ) g : ℝ) * μ g)

/-- Shells: `|g| ⩽ L_0 + Σ_{k ⩽ n} L_{k+1} [|g| > L_k]` when `|g| ⩽ L_{n+1}`. -/
theorem shell (S : Set Γ) (L : ℕ → ℕ) (hL : Monotone L) :
    ∀ (n : ℕ) (g : Γ), (wordLength S g : ℝ) ≤ L (n + 1) →
      (wordLength S g : ℝ) ≤ L 0 + ∑ k ∈ Finset.range (n + 1),
        (L (k + 1) : ℝ) * (ball S (L k))ᶜ.indicator (fun _ => (1 : ℝ)) g
  | 0, g, hg => by
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    by_cases h : g ∈ ball S (L 0)
    · rw [Set.indicator_of_notMem (by simpa using h), mul_zero, add_zero]; exact h
    · rw [Set.indicator_of_mem (by simpa using h), mul_one]
      have : (0 : ℝ) ≤ L 0 := Nat.cast_nonneg _
      linarith
  | n + 1, g, hg => by
    rw [Finset.sum_range_succ]
    have hnn : 0 ≤ (L (n + 1 + 1) : ℝ) * (ball S (L (n + 1)))ᶜ.indicator (fun _ => (1 : ℝ)) g :=
      mul_nonneg (Nat.cast_nonneg _) (Set.indicator_nonneg (fun _ _ => zero_le_one) g)
    by_cases h : g ∈ ball S (L (n + 1))
    · have := shell S L hL n g h
      linarith
    · rw [Set.indicator_of_mem (by simpa using h), mul_one]
      have h0 : (0 : ℝ) ≤ L 0 := Nat.cast_nonneg _
      have hs : 0 ≤ ∑ k ∈ Finset.range (n + 1),
          (L (k + 1) : ℝ) * (ball S (L k))ᶜ.indicator (fun _ => (1 : ℝ)) g :=
        Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _)
          (Set.indicator_nonneg (fun _ _ => zero_le_one) g)
      linarith

theorem phi_le (S : Finset Γ) {μ : Γ → ℝ} (hμ : IsProbability μ) (L : ℕ → ℕ) (hL : Monotone L)
    (n : ℕ) {r : ℝ} (hr : r ≤ L (n + 1)) :
    ∑' g : ball (S : Set Γ) r, (wordLength (S : Set Γ) g : ℝ) * μ g ≤
      L 0 + ∑ k ∈ Finset.range (n + 1), (L (k + 1) : ℝ) * mass μ (ball (S : Set Γ) (L k))ᶜ := by
  rw [phi_eq]
  have hind : ∀ k, Summable fun g => μ g * (ball (S : Set Γ) (L k))ᶜ.indicator (fun _ => (1:ℝ)) g :=
    fun k => Summable.of_nonneg_of_le
      (fun g => mul_nonneg (hμ.1 g) (Set.indicator_nonneg (fun _ _ => zero_le_one) g))
      (fun g => by
        calc μ g * _ ≤ μ g * 1 := mul_le_mul_of_nonneg_left
              (Set.indicator_le_self' (fun _ _ => zero_le_one) g |>.trans le_rfl |>.trans
                (by simp)) (hμ.1 g)
          _ = μ g := mul_one _) hμ.2.summable
  have hbound : ∀ g, (ball (S : Set Γ) r).indicator
      (fun g => (wordLength (S : Set Γ) g : ℝ) * μ g) g ≤
      μ g * L 0 + ∑ k ∈ Finset.range (n + 1),
        (L (k + 1) : ℝ) * (μ g * (ball (S : Set Γ) (L k))ᶜ.indicator (fun _ => (1 : ℝ)) g) := by
    intro g
    by_cases hg : g ∈ ball (S : Set Γ) r
    · rw [Set.indicator_of_mem hg]
      have := shell (S : Set Γ) L hL n g (le_trans hg hr)
      have e : μ g * L 0 + ∑ k ∈ Finset.range (n + 1),
          (L (k + 1) : ℝ) * (μ g * (ball (S : Set Γ) (L k))ᶜ.indicator (fun _ => (1 : ℝ)) g) =
          μ g * (L 0 + ∑ k ∈ Finset.range (n + 1),
            (L (k + 1) : ℝ) * (ball (S : Set Γ) (L k))ᶜ.indicator (fun _ => (1 : ℝ)) g) := by
        rw [mul_add, Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intro k _; ring
      rw [e, mul_comm]
      exact mul_le_mul_of_nonneg_left this (hμ.1 g)
    · rw [Set.indicator_of_notMem hg]
      exact add_nonneg (mul_nonneg (hμ.1 g) (Nat.cast_nonneg _)) (Finset.sum_nonneg fun k _ =>
        mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hμ.1 g)
          (Set.indicator_nonneg (fun _ _ => zero_le_one) g)))
  have hsum : Summable fun g => μ g * L 0 + ∑ k ∈ Finset.range (n + 1),
      (L (k + 1) : ℝ) * (μ g * (ball (S : Set Γ) (L k))ᶜ.indicator (fun _ => (1 : ℝ)) g) :=
    (hμ.2.summable.mul_right _).add (summable_sum fun k _ => (hind k).mul_left _)
  have hφs : Summable fun g => (ball (S : Set Γ) r).indicator
      (fun g => (wordLength (S : Set Γ) g : ℝ) * μ g) g :=
    Summable.of_nonneg_of_le (fun g => Set.indicator_nonneg (fun g _ => mul_nonneg
      (Nat.cast_nonneg _) (hμ.1 g)) g) hbound hsum
  refine (hφs.tsum_le_tsum hbound hsum).trans (le_of_eq ?_)
  rw [(hμ.2.summable.mul_right _).tsum_add (summable_sum fun k _ => (hind k).mul_left _),
    tsum_mul_right, hμ.2.tsum_eq, one_mul,
    Summable.tsum_finsetSum fun k _ => (hind k).mul_left _]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [tsum_mul_left]
  congr 1
  unfold mass
  congr 1; funext g
  simp only [Set.indicator]
  split_ifs <;> simp

end Gen

/-! ### Real-analysis helpers -/

theorem poly_le_exp (p : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K > (0 : ℝ), ∀ N : ℕ, (N : ℝ) ^ p ≤ K * (2 : ℝ) ^ (δ * N) := by
  have hr : |(2 : ℝ) ^ (-δ)| < 1 := by
    rw [abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one p hr
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp ((tendsto_order.1 ht).2 1 (by norm_num))
  set K := 1 + ∑ N ∈ Finset.range N₂, (N : ℝ) ^ p * ((2 : ℝ) ^ (-δ)) ^ N
  have hf0 : ∀ N : ℕ, 0 ≤ (N : ℝ) ^ p * ((2 : ℝ) ^ (-δ)) ^ N := fun N =>
    mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le _)
  have hK : ∀ N : ℕ, (N : ℝ) ^ p * ((2 : ℝ) ^ (-δ)) ^ N ≤ K := by
    intro N
    by_cases hN : N₂ ≤ N
    · have := hN₂ N hN
      have : (0 : ℝ) ≤ ∑ N ∈ Finset.range N₂, (N : ℝ) ^ p * ((2 : ℝ) ^ (-δ)) ^ N :=
        Finset.sum_nonneg fun N _ => hf0 N
      linarith
    · have := Finset.single_le_sum (fun N _ => hf0 N) (Finset.mem_range.mpr (not_le.mp hN))
      linarith
  have hKpos : 0 < K := by
    have : (0 : ℝ) ≤ ∑ N ∈ Finset.range N₂, (N : ℝ) ^ p * ((2 : ℝ) ^ (-δ)) ^ N :=
      Finset.sum_nonneg fun N _ => hf0 N
    show 0 < 1 + _
    linarith
  refine ⟨K, hKpos, fun N => ?_⟩
  have e : ((2 : ℝ) ^ (-δ)) ^ N * (2 : ℝ) ^ (δ * N) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    simp
  have h2 : 0 < (2 : ℝ) ^ (δ * N) := Real.rpow_pos_of_pos (by norm_num) _
  calc (N : ℝ) ^ p = (N : ℝ) ^ p * ((2 : ℝ) ^ (-δ)) ^ N * (2 : ℝ) ^ (δ * N) := by
        rw [mul_assoc, e, mul_one]
    _ ≤ K * (2 : ℝ) ^ (δ * N) := mul_le_mul_of_nonneg_right (hK N) h2.le

theorem two_rpow_nat (x : ℝ) (n : ℕ) : (2 : ℝ) ^ (x * n) = ((2 : ℝ) ^ x) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

theorem two_mul_le_two_pow_add_one : ∀ k : ℕ, 2 * k ≤ 2 ^ k + 1
  | 0 => by norm_num
  | 1 => by norm_num
  | k + 2 => by
    have := two_mul_le_two_pow_add_one (k + 1)
    rw [pow_succ]
    have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    omega

theorem two_mul_log_le (N : ℕ) : 2 * Nat.log 2 N ≤ N + 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have h1 := Nat.pow_log_le_self 2 hN.ne'
    have h2 := two_mul_le_two_pow_add_one (Nat.log 2 N)
    omega

section GrowthPart

variable {Γ : Type*} [Group Γ]

theorem ball_subset_wordBall (S : Finset Γ) (hS : Subgroup.closure (S : Set Γ) = ⊤) (r : ℝ) :
    ball (S : Set Γ) r ⊆ Chou.wordBall (S : Set Γ) ⌊r⌋₊ := by
  intro g hg
  exact WordBallDev.wordBall_mono _ (Nat.le_floor hg)
    (WordBallDev.mem_wordBall_wordLength (S : Set Γ) hS g)

theorem phi_mono (S : Finset Γ) (hS : Subgroup.closure (S : Set Γ) = ⊤) {μ : Γ → ℝ}
    (hμ : IsProbability μ) {r r' : ℝ} (h : r ≤ r') :
    ∑' g : ball (S : Set Γ) r, (wordLength (S : Set Γ) g : ℝ) * μ g ≤
      ∑' g : ball (S : Set Γ) r', (wordLength (S : Set Γ) g : ℝ) * μ g := by
  rw [phi_eq, phi_eq]
  have hfin : ∀ t : ℝ, Summable fun g => (ball (S : Set Γ) t).indicator
      (fun g => (wordLength (S : Set Γ) g : ℝ) * μ g) g := fun t => by
    apply summable_of_hasFiniteSupport
    refine ((WordBallDev.wordBall_finite S ⌊t⌋₊).subset (ball_subset_wordBall S hS t)).subset ?_
    intro g hg
    by_contra hb
    exact hg (Set.indicator_of_notMem hb _)
  exact (hfin r).tsum_le_tsum (fun g => Set.indicator_le_indicator_of_subset (ball_mono _ h)
    (fun g => mul_nonneg (Nat.cast_nonneg _) (hμ.1 g)) g) (hfin r')

/-- The growth half of the goal from Lemma 2.1 and the tail bounds at the radii `L_k`. -/
theorem growth_part (S : Finset Γ) (hS : Subgroup.closure (S : Set Γ) = ⊤) {μ : Γ → ℝ}
    (hμ : IsProbability μ) (L : ℕ → ℕ) (hLm : Monotone L)
    (hL2 : ∀ n N, n ≤ N → 2 ^ (N - n) * L n ≤ L N) (hL3 : ∀ n, L (n + 1) ≤ 3 * L n)
    (hL0 : L 0 = 3) {ε₁ ε : ℝ} (h0 : 0 < ε₁) (h1 : ε₁ < ε) (h2 : ε₁ ≤ 1 / 2) {C' : ℝ}
    (hC' : 1 ≤ C')
    (htail : ∀ k : ℕ, 1 ≤ k →
      mass μ (ball (S : Set Γ) (L k))ᶜ ≤ C' * (2 : ℝ) ^ (-((1 - ε₁) * k)))
    (ϱ : ℕ → ℝ)
    (hϱ : ∀ n : ℕ, ϱ n =
      sInf {r : ℝ | 0 < r ∧ mass μ {g | r ≤ (wordLength (S : Set Γ) g : ℝ)} < 1 / n})
    (φ : ℝ → ℝ)
    (hφ : ∀ r : ℝ, φ r = ∑' g : ball (S : Set Γ) r, (wordLength (S : Set Γ) g : ℝ) * μ g)
    {c₀ : ℝ} (hc₀ : 0 < c₀) {N₀ : ℕ}
    (hlem : ∀ m ≥ N₀, Real.exp (c₀ * m) ≤ growth (S : Set Γ) (m * φ (ϱ m)))
    (hv2 : ∀ N : ℕ, 1 ≤ N → 2 ≤ growth (S : Set Γ) (L N)) :
    ∃ c > 0, ∀ N : ℕ, 1 ≤ N →
      Real.exp (c * (2 : ℝ) ^ ((1 - ε) * N)) ≤ growth (S : Set Γ) (L N) := by
  set a := 1 - ε₁ with ha
  have ha1 : a ≤ 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hC'0 : 0 < C' := by linarith
  have hLpos : ∀ n, (1 : ℝ) ≤ L n := fun n => by
    have := hL2 0 n (Nat.zero_le n); rw [hL0] at this
    have : 1 ≤ L n := by have : 1 ≤ 2 ^ (n - 0) := Nat.one_le_two_pow; nlinarith
    exact_mod_cast this
  have hL2r : ∀ n N, n ≤ N → (2 : ℝ) ^ (N - n) * L n ≤ L N := fun n N h => by
    exact_mod_cast hL2 n N h
  have hpow_le : ∀ n : ℕ, (2 : ℝ) ^ (a * n) ≤ L n := fun n => by
    calc (2 : ℝ) ^ (a * n) ≤ (2 : ℝ) ^ ((n : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
      _ = (2 : ℝ) ^ (n - 0) * 1 := by rw [Real.rpow_natCast]; simp
      _ ≤ (2 : ℝ) ^ (n - 0) * L 0 := by
          apply mul_le_mul_of_nonneg_left (by rw [hL0]; norm_num) (by positivity)
      _ ≤ L n := hL2r 0 n (Nat.zero_le n)
  -- the per-`n` bound
  have key : ∀ n : ℕ, 1 ≤ n → 2 ≤ (2 : ℝ) ^ (a * n) / C' →
      N₀ ≤ ⌈(2 : ℝ) ^ (a * n) / C' / 2⌉₊ →
      Real.exp (c₀ * ((2 : ℝ) ^ (a * n) / C' / 2)) ≤
        growth (S : Set Γ) (L (n + (Nat.log 2 n + 5))) := by
    intro n hn hx hN
    set x := (2 : ℝ) ^ (a * n) / C' with hxdef
    set m := ⌈x / 2⌉₊ with hmdef
    have hm1 : x / 2 ≤ m := Nat.le_ceil _
    have hm2 : (m : ℝ) < x / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
    have hmx : (m : ℝ) < x := by linarith
    have hmpos : (0 : ℝ) < m := by linarith
    have h2an : 0 < (2 : ℝ) ^ (a * n) := Real.rpow_pos_of_pos (by norm_num) _
    have hxinv : C' * (2 : ℝ) ^ (-(a * n)) = 1 / x := by
      rw [hxdef, Real.rpow_neg (by norm_num)]; field_simp
    -- `ϱ_m ⩽ L_n + 1`
    have hϱm : ϱ m ≤ L n + 1 := by
      rw [hϱ m]
      apply csInf_le ⟨0, fun r hr => hr.1.le⟩
      refine ⟨by linarith [hLpos n], ?_⟩
      calc mass μ {g | (L n : ℝ) + 1 ≤ (wordLength (S : Set Γ) g : ℝ)}
          ≤ mass μ (ball (S : Set Γ) (L n))ᶜ := mass_mono hμ (fun g hg => by
            simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, ball] at hg ⊢; linarith)
        _ ≤ C' * (2 : ℝ) ^ (-(a * n)) := htail n hn
        _ = 1 / x := hxinv
        _ < 1 / m := one_div_lt_one_div_of_lt hmpos hmx
    -- the shell bound
    have hLn1 : (L n : ℝ) + 1 ≤ L (n + 1) := by
      have := hL2r n (n + 1) (by omega)
      rw [show n + 1 - n = 1 by omega, pow_one] at this
      linarith [hLpos n]
    have hφ2 := phi_le S hμ L hLm n hLn1
    have hterm : ∀ k ∈ Finset.range n, (L (k + 1 + 1) : ℝ) * mass μ (ball (S : Set Γ) (L (k + 1)))ᶜ
        ≤ 3 * C' * L n * (2 : ℝ) ^ (-(a * n)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hL3k : (L (k + 1 + 1) : ℝ) ≤ 3 * L (k + 1) := by exact_mod_cast hL3 (k + 1)
      have ht := htail (k + 1) (by omega)
      have hLk := hL2r (k + 1) n (by omega)
      have hd : (2 : ℝ) ^ (-(a * ((k + 1 : ℕ) : ℝ))) =
          (2 : ℝ) ^ (-(a * n)) * (2 : ℝ) ^ (a * ((n - (k + 1) : ℕ) : ℝ)) := by
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        push_cast [show k + 1 ≤ n by omega]
        ring
      have hd2 : (2 : ℝ) ^ (a * ((n - (k + 1) : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (n - (k + 1)) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by nlinarith [Nat.cast_nonneg (α := ℝ) (n - (k + 1))])
      have hm0 : 0 ≤ mass μ (ball (S : Set Γ) (L (k + 1)))ᶜ := by
        unfold mass; exact tsum_nonneg fun g => Set.indicator_nonneg (fun g _ => hμ.1 g) g
      have h2n : 0 < (2 : ℝ) ^ (-(a * n)) := Real.rpow_pos_of_pos (by norm_num) _
      calc (L (k + 1 + 1) : ℝ) * mass μ (ball (S : Set Γ) (L (k + 1)))ᶜ
          ≤ (3 * L (k + 1)) * (C' * (2 : ℝ) ^ (-((1 - ε₁) * ((k + 1 : ℕ) : ℝ)))) :=
            mul_le_mul hL3k ht hm0 (by positivity)
        _ = 3 * C' * (2 : ℝ) ^ (-(a * n)) * ((2 : ℝ) ^ (a * ((n - (k + 1) : ℕ) : ℝ)) * L (k + 1)) := by
            rw [← ha, hd]; ring
        _ ≤ 3 * C' * (2 : ℝ) ^ (-(a * n)) * ((2 : ℝ) ^ (n - (k + 1)) * L (k + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right hd2 (by positivity)
        _ ≤ 3 * C' * (2 : ℝ) ^ (-(a * n)) * L n :=
            mul_le_mul_of_nonneg_left hLk (by positivity)
        _ = 3 * C' * L n * (2 : ℝ) ^ (-(a * n)) := by ring
    have hsum : ∑ k ∈ Finset.range (n + 1), (L (k + 1) : ℝ) * mass μ (ball (S : Set Γ) (L k))ᶜ ≤
        9 + n * (3 * C' * L n * (2 : ℝ) ^ (-(a * n))) := by
      rw [Finset.sum_range_succ']
      have h0' : (L (0 + 1) : ℝ) * mass μ (ball (S : Set Γ) (L 0))ᶜ ≤ 9 := by
        have : (L 1 : ℝ) ≤ 9 := by have := hL3 0; rw [hL0] at this; exact_mod_cast this
        have hm1' := mass_le_one hμ (ball (S : Set Γ) (L 0))ᶜ
        have hm0 : 0 ≤ mass μ (ball (S : Set Γ) (L 0))ᶜ := by
          unfold mass; exact tsum_nonneg fun g => Set.indicator_nonneg (fun g _ => hμ.1 g) g
        calc (L (0 + 1) : ℝ) * mass μ (ball (S : Set Γ) (L 0))ᶜ ≤ 9 * 1 :=
              mul_le_mul this hm1' hm0 (by norm_num)
          _ = 9 := by norm_num
      have := Finset.sum_le_sum hterm
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
      linarith
    have hφ3 : φ (ϱ m) ≤ 12 + n * (3 * C' * L n * (2 : ℝ) ^ (-(a * n))) := by
      rw [hφ]
      calc _ ≤ ∑' g : ball (S : Set Γ) ((L n : ℝ) + 1), (wordLength (S : Set Γ) g : ℝ) * μ g :=
            phi_mono S hS hμ hϱm
        _ ≤ _ := hφ2
        _ ≤ _ := by rw [hL0]; push_cast; linarith
    have hY : 0 ≤ 12 + n * (3 * C' * L n * (2 : ℝ) ^ (-(a * n))) := by
      have := Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (-(a * n))
      have := hLpos n
      positivity
    have hmφ : (m : ℝ) * φ (ϱ m) ≤ 15 * n * L n := by
      calc (m : ℝ) * φ (ϱ m) ≤ m * (12 + n * (3 * C' * L n * (2 : ℝ) ^ (-(a * n)))) :=
            mul_le_mul_of_nonneg_left hφ3 hmpos.le
        _ ≤ x * (12 + n * (3 * C' * L n * (2 : ℝ) ^ (-(a * n)))) :=
            mul_le_mul_of_nonneg_right hmx.le hY
        _ = 12 * x + 3 * n * L n * (x * C' * (2 : ℝ) ^ (-(a * n))) := by ring
        _ = 12 * x + 3 * n * L n := by
            rw [show x * C' * (2 : ℝ) ^ (-(a * n)) = 1 by
              rw [mul_assoc, hxinv]; field_simp]
            ring
        _ ≤ 12 * L n + 3 * n * L n := by
            have : x ≤ L n := by
              rw [hxdef, div_le_iff₀ hC'0]
              nlinarith [hpow_le n, hLpos n]
            linarith
        _ ≤ 15 * n * L n := by
            have : (1 : ℝ) ≤ n := by exact_mod_cast hn
            nlinarith [hLpos n]
    have hj : (15 * n * L n : ℝ) ≤ L (n + (Nat.log 2 n + 5)) := by
      have h1' := hL2r n (n + (Nat.log 2 n + 5)) (by omega)
      rw [show n + (Nat.log 2 n + 5) - n = Nat.log 2 n + 5 by omega] at h1'
      have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
      have : (16 * n : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 n + 5) := by
        have : 16 * n ≤ 2 ^ (Nat.log 2 n + 5) := by
          rw [show Nat.log 2 n + 5 = (Nat.log 2 n + 1) + 4 by ring, pow_add]; omega
        exact_mod_cast this
      nlinarith [hLpos n]
    calc Real.exp (c₀ * (x / 2)) ≤ Real.exp (c₀ * m) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hm1 hc₀.le)
      _ ≤ growth (S : Set Γ) (m * φ (ϱ m)) := hlem m hN
      _ ≤ growth (S : Set Γ) (15 * n * L n) := by exact_mod_cast growth_mono S hmφ
      _ ≤ growth (S : Set Γ) (L (n + (Nat.log 2 n + 5))) := by exact_mod_cast growth_mono S hj
  -- thresholds
  have htend : Tendsto (fun n : ℕ => (2 : ℝ) ^ (a * n) / C') atTop atTop := by
    have : (fun n : ℕ => (2 : ℝ) ^ (a * n) / C') = fun n : ℕ => ((2 : ℝ) ^ a) ^ n / C' := by
      funext n; rw [two_rpow_nat]
    rw [this]
    exact Tendsto.atTop_div_const hC'0
      (tendsto_pow_atTop_atTop_of_one_lt (Real.one_lt_rpow (by norm_num) ha0))
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp
    (htend.eventually_ge_atTop (max 2 (2 * (N₀ : ℝ))))
  set n₂ := max n₁ 1
  obtain ⟨K₂, hK₂, hK₂b⟩ := poly_le_exp 1 (show 0 < ε - ε₁ by linarith)
  set c₁ := c₀ / (64 * C' * K₂) with hc₁
  set N₁ := 2 * n₂ + 12
  have hc₁0 : 0 < c₁ := by positivity
  refine ⟨min c₁ (Real.log 2 / (2 : ℝ) ^ N₁), lt_min hc₁0 (by positivity), fun N hN => ?_⟩
  by_cases hNl : N < N₁
  · have hv := hv2 N hN
    calc Real.exp (min c₁ (Real.log 2 / 2 ^ N₁) * (2 : ℝ) ^ ((1 - ε) * N))
        ≤ Real.exp (Real.log 2) := by
          apply Real.exp_le_exp.mpr
          have hpos : 0 ≤ (2 : ℝ) ^ ((1 - ε) * N) := (Real.rpow_pos_of_pos (by norm_num) _).le
          have hle : (2 : ℝ) ^ ((1 - ε) * N) ≤ 2 ^ N₁ := by
            calc (2 : ℝ) ^ ((1 - ε) * N) ≤ (2 : ℝ) ^ ((N₁ : ℕ) : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
                    have : (N : ℝ) ≤ N₁ := by exact_mod_cast hNl.le
                    nlinarith [Nat.cast_nonneg (α := ℝ) N])
              _ = 2 ^ N₁ := Real.rpow_natCast _ _
          calc min c₁ (Real.log 2 / 2 ^ N₁) * (2 : ℝ) ^ ((1 - ε) * N)
              ≤ (Real.log 2 / 2 ^ N₁) * 2 ^ N₁ :=
                mul_le_mul (min_le_right _ _) hle hpos (by positivity)
            _ = Real.log 2 := by field_simp
      _ = 2 := Real.exp_log (by norm_num)
      _ ≤ growth (S : Set Γ) (L N) := by exact_mod_cast hv
  · push Not at hNl
    have hlog := two_mul_log_le N
    set n := N - (Nat.log 2 N + 5) with hndef
    have hn2 : n₂ ≤ n := by omega
    have hn1' : n₁ ≤ n := le_trans (le_max_left _ _) hn2
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn2
    have hx := hn₁ n hn1'
    have hx2 : 2 ≤ (2 : ℝ) ^ (a * n) / C' := le_trans (le_max_left _ _) hx
    have hxN : N₀ ≤ ⌈(2 : ℝ) ^ (a * n) / C' / 2⌉₊ := by
      have : (N₀ : ℝ) ≤ (2 : ℝ) ^ (a * n) / C' / 2 := by
        have := le_trans (le_max_right _ _) hx; linarith
      exact_mod_cast this.trans (Nat.le_ceil _)
    have hk := key n hn1 hx2 hxN
    have hlogn : Nat.log 2 n ≤ Nat.log 2 N := Nat.log_mono_right (by omega)
    have hmono : growth (S : Set Γ) (L (n + (Nat.log 2 n + 5))) ≤ growth (S : Set Γ) (L N) :=
      growth_mono S (by exact_mod_cast hLm (show n + (Nat.log 2 n + 5) ≤ N by omega))
    -- the exponent
    set P := (2 : ℝ) ^ ((1 - ε) * N)
    set Q := (2 : ℝ) ^ ((ε - ε₁) * N)
    set R := (2 : ℝ) ^ (a * ((Nat.log 2 N + 5 : ℕ) : ℝ))
    set X := (2 : ℝ) ^ (a * n)
    have hP : 0 < P := Real.rpow_pos_of_pos (by norm_num) _
    have hQ : 0 < Q := Real.rpow_pos_of_pos (by norm_num) _
    have hR : 0 < R := Real.rpow_pos_of_pos (by norm_num) _
    have hX : 0 < X := Real.rpow_pos_of_pos (by norm_num) _
    have e1 : X * R = P * Q := by
      simp only [X, R, P, Q]
      rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
      congr 1
      rw [hndef]
      push_cast [show Nat.log 2 N + 5 ≤ N by omega]
      ring
    have e2 : R ≤ 32 * N := by
      have hN1 : 1 ≤ N := hN
      calc R ≤ (2 : ℝ) ^ (((Nat.log 2 N + 5 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num)
              (by nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 N + 5)])
        _ = 2 ^ (Nat.log 2 N + 5) := Real.rpow_natCast _ _
        _ = 32 * 2 ^ Nat.log 2 N := by ring
        _ ≤ 32 * N := by
            have := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
            have : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ N := by exact_mod_cast this
            push_cast at this
            linarith
    have e4 : (N : ℝ) ≤ K₂ * Q := by simpa using hK₂b N
    have hPX : P ≤ 32 * K₂ * X := by
      have : P * Q ≤ 32 * K₂ * X * Q := by
        rw [← e1]
        nlinarith
      exact le_of_mul_le_mul_right this hQ
    have hexp : min c₁ (Real.log 2 / 2 ^ N₁) * P ≤ c₀ * (X / C' / 2) := by
      calc min c₁ (Real.log 2 / 2 ^ N₁) * P ≤ c₁ * P :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hP.le
        _ ≤ c₁ * (32 * K₂ * X) := mul_le_mul_of_nonneg_left hPX hc₁0.le
        _ = c₀ * (X / C' / 2) := by rw [hc₁]; field_simp; ring
    calc Real.exp (min c₁ (Real.log 2 / 2 ^ N₁) * P) ≤ Real.exp (c₀ * (X / C' / 2)) :=
          Real.exp_le_exp.mpr hexp
      _ ≤ growth (S : Set Γ) (L (n + (Nat.log 2 n + 5))) := hk
      _ ≤ growth (S : Set Γ) (L N) := by exact_mod_cast hmono

end GrowthPart

/-! ### The tail at the radii `L_N` -/

theorem tail_part {Γ : Type*} [Group Γ] (S : Set Γ) {μ : Γ → ℝ} (hμ : IsProbability μ)
    (L : ℕ → ℕ) (hL2 : ∀ n N, n ≤ N → 2 ^ (N - n) * L n ≤ L N) (A : ℕ) {β ε₁ : ℝ}
    (hβ1 : β ≤ 1) (hβε : 1 - ε₁ + ε₁ / 2 ≤ β) (hε₁1 : ε₁ ≤ 1) {C₂ K : ℝ} (hC₂ : 0 < C₂) (hK : 0 < K)
    (hKb : ∀ N : ℕ, (N : ℝ) ^ (2 * A) ≤ K * (2 : ℝ) ^ (ε₁ / 2 * N))
    (hJ : ∀ n : ℕ, mass μ (ball S (2 ^ (2 * kLog A n) * L n))ᶜ ≤ C₂ / (2 : ℝ) ^ ((n : ℝ) * β))
    (N : ℕ) (hN : 1 ≤ N) :
    mass μ (ball S (L N))ᶜ ≤ C₂ * K * (2 : ℝ) ^ (-((1 - ε₁) * N)) := by
  set M := Nat.log 2 N
  set n := N - 2 * A * M with hndef
  have hkn : kLog A n ≤ A * M := Nat.mul_le_mul_left A (Nat.log_mono_right (by omega))
  have hk0 : kLog A 0 = 0 := by simp [kLog]
  have hsum : n + 2 * kLog A n ≤ N := by
    by_cases h : 2 * A * M ≤ N
    · have : 2 * kLog A n ≤ 2 * A * M := by nlinarith
      omega
    · have : n = 0 := by omega
      rw [this, hk0]; omega
  have hrad : (2 : ℝ) ^ (2 * kLog A n) * L n ≤ L N := by
    have h1 := hL2 n N (by omega)
    have h2 : 2 ^ (2 * kLog A n) * L n ≤ 2 ^ (N - n) * L n :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact_mod_cast h2.trans h1
  have hmass := (mass_mono hμ (Set.compl_subset_compl.mpr (ball_mono S hrad))).trans (hJ n)
  refine hmass.trans ?_
  -- exponents
  have hβ0 : 0 ≤ β := by linarith
  have hnr : (N : ℝ) - 2 * A * M ≤ n := by
    rw [hndef]
    rcases le_total (2 * A * M) N with h | h
    · push_cast [h]; linarith
    · have : N - 2 * A * M = 0 := by omega
      rw [this]; push_cast
      have : (N : ℝ) ≤ 2 * A * M := by exact_mod_cast h
      linarith
  have hM : (2 : ℝ) ^ M ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
  have h2M : (2 : ℝ) ^ ((2 * A * M : ℕ) : ℝ) ≤ K * (2 : ℝ) ^ (ε₁ / 2 * N) := by
    rw [Real.rpow_natCast]
    calc (2 : ℝ) ^ (2 * A * M) = ((2 : ℝ) ^ M) ^ (2 * A) := by rw [← pow_mul]; ring_nf
      _ ≤ (N : ℝ) ^ (2 * A) := pow_le_pow_left₀ (by positivity) hM _
      _ ≤ _ := hKb N
  have e1 : (2 : ℝ) ^ (-((n : ℝ) * β)) ≤ (2 : ℝ) ^ (-(β * N) + ((2 * A * M : ℕ) : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    have : (0 : ℝ) ≤ 2 * A * M := by positivity
    nlinarith
  have e2 : (2 : ℝ) ^ (-(β * N) + ((2 * A * M : ℕ) : ℝ)) ≤
      K * (2 : ℝ) ^ (-((1 - ε₁) * N)) := by
    rw [Real.rpow_add (by norm_num)]
    calc (2 : ℝ) ^ (-(β * N)) * (2 : ℝ) ^ ((2 * A * M : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ (-(β * N)) * (K * (2 : ℝ) ^ (ε₁ / 2 * N)) :=
          mul_le_mul_of_nonneg_left h2M (by positivity)
      _ = K * (2 : ℝ) ^ (-(β * N) + ε₁ / 2 * N) := by
          rw [Real.rpow_add (by norm_num)]; ring
      _ ≤ K * (2 : ℝ) ^ (-((1 - ε₁) * N)) := by
          apply mul_le_mul_of_nonneg_left _ hK.le
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          nlinarith [Nat.cast_nonneg (α := ℝ) N]
  rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
  calc C₂ * (2 : ℝ) ^ (-((n : ℝ) * β)) ≤ C₂ * (K * (2 : ℝ) ^ (-((1 - ε₁) * N))) :=
        mul_le_mul_of_nonneg_left (e1.trans e2) hC₂.le
    _ = C₂ * K * (2 : ℝ) ^ (-((1 - ε₁) * N)) := by ring

/-! ### `μ_β` is symmetric and non-degenerate; `v(L_N) ⩾ 2` -/

theorem gens_inv {ω : ℕ → Fin 3} {x : BinaryTreeAut} (hx : x ∈ gens ω) : x⁻¹ = x := by
  simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact GrigBasic.grigA_inv
  all_goals exact GrigBasic.gen_inv _ _

theorem genSet_inv {ω : ℕ → Fin 3} {g : grigorchuk ω} (hg : g ∈ genSet ω) : g⁻¹ = g :=
  Subtype.ext (by rw [InvMemClass.coe_inv]; exact gens_inv hg)

theorem mem_genSet_inv {ω : ℕ → Fin 3} (g : grigorchuk ω) : g⁻¹ ∈ genSet ω ↔ g ∈ genSet ω := by
  constructor
  · intro h; have := genSet_inv h; rw [inv_inv] at this; rw [this]; exact h
  · intro h; rw [genSet_inv h]; exact h

theorem isSymmetric_muBeta (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (β : ℝ) :
    IsSymmetric (muBeta D ω k β) := by
  intro g
  have hu : uniformMeasure (genSet ω) g⁻¹ = uniformMeasure (genSet ω) g := by
    unfold uniformMeasure
    by_cases h : g ∈ genSet ω
    · rw [if_pos h, if_pos ((mem_genSet_inv g).mpr h)]
    · rw [if_neg h, if_neg (fun h' => h ((mem_genSet_inv g).mp h'))]
  have hs : ∀ n, upsilon D ω k n ((g⁻¹ : grigorchuk ω) : BinaryTreeAut) +
      upsilonCheck D ω k n ((g⁻¹ : grigorchuk ω) : BinaryTreeAut) =
      upsilon D ω k n (g : BinaryTreeAut) + upsilonCheck D ω k n (g : BinaryTreeAut) := by
    intro n
    simp only [upsilonCheck, InvMemClass.coe_inv, inv_inv]
    ring
  simp only [muBeta, hu, hs]

theorem genSet_finite (ω : ℕ → Fin 3) : (genSet ω).Finite :=
  (show (gens ω).Finite by unfold gens; exact Set.toFinite _).preimage
    Subtype.val_injective.injOn

theorem grigA_mem_genSet (ω : ℕ → Fin 3) :
    (⟨grigA, Subgroup.subset_closure (by simp [gens])⟩ : grigorchuk ω) ∈ genSet ω := by
  simp [genSet, gens]

theorem two_le_growth (ω : ℕ → Fin 3) (S : Finset (grigorchuk ω))
    (hSc : (S : Set (grigorchuk ω)) = genSet ω) {r : ℝ} (hr : 1 ≤ r) :
    2 ≤ growth (S : Set (grigorchuk ω)) r := by
  unfold growth
  set a : grigorchuk ω := ⟨grigA, Subgroup.subset_closure (by simp [gens])⟩
  have ha : a ∈ (S : Set (grigorchuk ω)) := by rw [hSc]; exact grigA_mem_genSet ω
  have hne : (1 : grigorchuk ω) ≠ a := by
    intro h
    have := congrArg (fun g : grigorchuk ω => [false] <• (g : BinaryTreeAut)) h
    simp only [OneMemClass.coe_one, a] at this
    rw [MulOpposite.op_one, one_smul, GrigBasic.vertex_smul_grigA] at this
    simp [grigAFun] at this
  have hfl : 1 ≤ ⌊r⌋₊ := Nat.le_floor (by exact_mod_cast hr)
  have hsub : ({1, a} : Set (grigorchuk ω)) ⊆ Chou.wordBall (S : Set (grigorchuk ω)) ⌊r⌋₊ := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact WordBallDev.one_mem_wordBall _ _
    · refine WordBallDev.wordBall_mono _ hfl ⟨[a], by simp, ?_, by simp⟩
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      left; exact_mod_cast ha
  have := Nat.card_mono (WordBallDev.wordBall_finite S _) hsub
  rwa [Nat.card_coe_set_eq, Set.ncard_pair hne] at this

theorem eventually_kLog_le (A : ℕ) : ∀ᶠ n : ℕ in atTop, kLog A n ≤ n := by
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · exact Eventually.of_forall fun n => by simp [kLog]
  have hc : (0 : ℝ) < Real.log 2 / A := by positivity
  have h1 := (Real.isLittleO_log_id_atTop.bound hc)
  have h2 := tendsto_natCast_atTop_atTop.eventually h1
  filter_upwards [h2, eventually_ge_atTop 1] with n hn hn1
  simp only [Real.norm_eq_abs, id] at hn
  have hlogn : Real.log n ≤ Real.log 2 / A * n := by
    rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hn1)),
      abs_of_nonneg (Nat.cast_nonneg n)] at hn
    exact hn
  have hb := Real.natLog_le_logb n 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : ((A * Nat.log 2 n : ℕ) : ℝ) ≤ n := by
    push_cast
    calc (A : ℝ) * Nat.log 2 n ≤ A * Real.logb 2 n := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg A); exact_mod_cast hb
      _ = A * (Real.log n / Real.log 2) := by rw [Real.logb]
      _ ≤ A * (Real.log 2 / A * n / Real.log 2) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg A)
          exact div_le_div_of_nonneg_right hlogn hlog2.le
      _ = n := by field_simp
  exact_mod_cast this

end P3GoalDev

end ErschlerZheng
end

section
open scoped RightActions
open Garrido Filter Topology
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open ErschlerZheng
open P3GoalDev in
theorem solution (D : ℕ) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ ω : ℕ → Fin 3, SatisfiesFr D ω →
      ∃ μ : grigorchuk ω → ℝ, IsNondegenerate μ ∧ IsSymmetric μ ∧ IsProbability μ ∧
        HasFiniteEntropy μ ∧ HasNontrivialPoissonBoundary μ ∧
        (∀ n : ℕ, 1 ≤ n →
          mass μ (ball (genSet ω) (lengthL ω n))ᶜ ≤ C * (2 : ℝ) ^ (-((1 - ε) * n))) ∧
        ∃ c > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
          Real.exp (c * (2 : ℝ) ^ ((1 - ε) * n)) ≤ growth (genSet ω) (lengthL ω n) := by
  by_cases hD : D < 3
  · refine ⟨1, one_pos, fun ω hω => ?_⟩
    obtain ⟨m, hm, -⟩ := hω 0
    omega
  push Not at hD
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  set ε₁ := min ε 1 / 2 with hε₁
  have hm0 : 0 < min ε 1 := lt_min hε one_pos
  have hε₁0 : 0 < ε₁ := by positivity
  have hε₁ε : ε₁ < ε := by have := min_le_left ε 1; linarith
  have hε₁h : ε₁ ≤ 1 / 2 := by have := min_le_right ε 1; linarith
  set δ₀ : ℝ := min (1 / (2 * (D : ℝ))) (ε₁ / 2) with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min (by positivity) (by positivity)
  have hδ₀1 : δ₀ ≤ 1 / (2 * (D : ℝ)) := min_le_left _ _
  have hδ₀2 : δ₀ ≤ ε₁ / 2 := min_le_right _ _
  set β := 1 - δ₀ with hβdef
  have hβ1 : 1 - 1 / (D : ℝ) < β := by
    have : 1 / (2 * (D : ℝ)) < 1 / D := by
      apply one_div_lt_one_div_of_lt hD0; linarith
    linarith
  have hβ2 : β < 1 := by linarith
  have hβε : 1 - ε₁ + ε₁ / 2 ≤ β := by linarith
  have hβ0 : 0 < β := by linarith
  set A := D * (⌈(D : ℝ) * (1 + β) / (2 * (1 - β))⌉₊ + 1) with hAdef
  have hDA : D ∣ A := dvd_mul_right D _
  have hA : (D : ℝ) * (1 + β) / (2 * (1 - β)) < A := by
    have h1 := Nat.le_ceil ((D : ℝ) * (1 + β) / (2 * (1 - β)))
    rw [hAdef]; push_cast
    have : (0 : ℝ) ≤ ⌈(D : ℝ) * (1 + β) / (2 * (1 - β))⌉₊ := Nat.cast_nonneg _
    nlinarith
  have hApos : 0 < A := Nat.mul_pos (by omega) (by omega)
  obtain ⟨C₂, hC₂, hJ2⟩ := isProbability_and_hasFiniteEntropy_muBeta_and_mass_ball_compl_le D β hβ0
  obtain ⟨K, hK, hKb⟩ := poly_le_exp (2 * A) (show 0 < ε₁ / 2 by positivity)
  set C := max 1 (C₂ * K) with hCdef
  refine ⟨C, lt_of_lt_of_le one_pos (le_max_left _ _), fun ω hω => ?_⟩
  have hadm : IsAdmissibleSeq D (kLog A) := by
    refine ⟨fun a b hab => Nat.mul_le_mul_left A (Nat.log_mono_right hab), fun n hn hDn => ?_⟩
    have hnD : D ≤ n := Nat.le_of_dvd (by omega) hDn
    refine ⟨Nat.mul_pos hApos (Nat.log_pos (by norm_num) (by omega)), ?_⟩
    exact Dvd.dvd.mul_right hDA _
  obtain ⟨hprob, hent, htail⟩ := hJ2 ω hω (kLog A) hadm (eventually_kLog_le A)
  have hP := hasNontrivialPoissonBoundary_muBeta D ω hω β hβ1 hβ2 A hA hDA
  have hL2 : ∀ n N, n ≤ N → 2 ^ (N - n) * lengthL ω n ≤ lengthL ω N :=
    fun n N h => lengthL_mono_pow ω h
  have hLm : Monotone (lengthL ω) := fun a b hab => by
    have := hL2 a b hab
    have : 1 ≤ 2 ^ (b - a) := Nat.one_le_two_pow
    nlinarith
  have htail1 : ∀ N, 1 ≤ N → mass (muBeta D ω (kLog A) β) (ball (genSet ω) (lengthL ω N))ᶜ ≤
      C * (2 : ℝ) ^ (-((1 - ε₁) * N)) := fun N hN => by
    refine (tail_part (genSet ω) hprob (lengthL ω) hL2 A hβ2.le hβε (by linarith) hC₂ hK hKb
      htail N hN).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_pos_of_pos (by norm_num) _).le
  refine ⟨muBeta D ω (kLog A) β, isNondegenerate_muBeta D ω (kLog A) β,
    isSymmetric_muBeta D ω (kLog A) β, hprob, hent, hP, fun n hn => ?_, ?_⟩
  · refine (htail1 n hn).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · set Sfin := (genSet_finite ω).toFinset
    have hSc : (Sfin : Set (grigorchuk ω)) = genSet ω := Set.Finite.coe_toFinset _
    have hS : Subgroup.closure (Sfin : Set (grigorchuk ω)) = ⊤ := by
      rw [hSc]; exact Subgroup.closure_closure_coe_preimage
    obtain ⟨c₀, hc₀, hev0⟩ := exp_le_growth_of_hasNontrivialPoissonBoundary Sfin hS
      (muBeta D ω (kLog A) β) hprob hent hP
      (fun n => sInf {r : ℝ | 0 < r ∧ mass (muBeta D ω (kLog A) β)
        {g | r ≤ (wordLength (Sfin : Set (grigorchuk ω)) g : ℝ)} < 1 / n}) (fun n => rfl)
      (fun r => ∑' g : ball (Sfin : Set (grigorchuk ω)) r,
        (wordLength (Sfin : Set (grigorchuk ω)) g : ℝ) * muBeta D ω (kLog A) β g) (fun r => rfl)
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev0
    have hg := growth_part Sfin hS hprob (lengthL ω) hLm hL2 (lengthL_succ_le ω) (lengthL_zero ω)
      hε₁0 hε₁ε hε₁h (le_max_left 1 _ : (1 : ℝ) ≤ C) (fun k hk => by rw [hSc]; exact htail1 k hk)
      _ (fun n => rfl) _ (fun r => rfl) hc₀ hN₀
      (fun N hN => two_le_growth ω Sfin hSc (by exact_mod_cast one_le_lengthL ω N))
    rw [hSc] at hg
    exact hg
end
