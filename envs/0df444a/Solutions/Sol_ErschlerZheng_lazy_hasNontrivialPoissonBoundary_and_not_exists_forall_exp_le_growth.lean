-- Prove2me | solution 1 for ErschlerZheng.lazy_hasNontrivialPoissonBoundary_and_not_exists_forall_exp_le_growth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T11:44:25.431161+00:00
-- url     : https://prove2.me/submissions/9bac84fc-843e-430c-a112-e40b9cfc45de

import Mathlib
import Definitions.Def_ErschlerZheng_Walks

section
/-!
# Lemma 2.1 read for every `n ⩾ 1` fails: the lazy walk `ν = ½δ_id + ½μ`

`ν` is a probability of finite entropy (`-(t/2)log(t/2) = ½(-t log t) + (log 2/2)t`, and
`-(a+b)log(a+b) ⩽ -a log a - b log b`), every bounded `μ`-harmonic function is `ν`-harmonic, and the
support of `ν` contains that of `μ`. At `n = 1`: `ν{|g| ⩾ r} ⩽ ½ < 1` for every `r > 0`, so
`ϱ_1 = 0`, `φ(0) = 0`, `R_1 = 0`, and `v(0) = 1 < e^c`.
-/

set_option linter.unusedVariables false

namespace ErschlerZheng

namespace P3LazyDev

variable {Γ : Type*} [Group Γ]

theorem negMulLog_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog (a + b) ≤ Real.negMulLog a + Real.negMulLog b := by
  rcases ha.lt_or_eq with ha' | rfl
  · rcases hb.lt_or_eq with hb' | rfl
    · simp only [Real.negMulLog]
      have h1 : Real.log a ≤ Real.log (a + b) := Real.log_le_log ha' (by linarith)
      have h2 : Real.log b ≤ Real.log (a + b) := Real.log_le_log hb' (by linarith)
      nlinarith
    · simp
  · simp

theorem wordLength_one (S : Set Γ) : wordLength S (1 : Γ) = 0 := by
  unfold wordLength
  apply Nat.sInf_eq_zero.mpr
  left
  exact ⟨[], by simp, by simp, by simp⟩

theorem wordBall_zero (S : Set Γ) : Chou.wordBall S 0 = {1} := by
  ext g
  simp only [Chou.wordBall, Set.mem_ofPred_eq, Set.mem_singleton_iff, nonpos_iff_eq_zero,
    List.length_eq_zero_iff]
  constructor
  · rintro ⟨l, rfl, -, rfl⟩; rfl
  · rintro rfl; exact ⟨[], rfl, by simp, rfl⟩

end P3LazyDev

end ErschlerZheng
end

section
set_option linter.unusedVariables false
open ErschlerZheng
open P3LazyDev in
theorem solution {Γ : Type*}
    [Group Γ] [DecidableEq Γ] (S : Finset Γ) (hS : Subgroup.closure (S : Set Γ) = ⊤) (μ : Γ → ℝ)
    (hμ : IsProbability μ) (hH : HasFiniteEntropy μ) (hP : HasNontrivialPoissonBoundary μ)
    (ν : Γ → ℝ) (hν : ∀ g, ν g = (if g = 1 then 1 / 2 else 0) + μ g / 2)
    (ϱ : ℕ → ℝ)
    (hϱ : ∀ n : ℕ, ϱ n =
      sInf {r : ℝ | 0 < r ∧ mass ν {g | r ≤ (wordLength (S : Set Γ) g : ℝ)} < 1 / n})
    (φ : ℝ → ℝ)
    (hφ : ∀ r : ℝ, φ r = ∑' g : ball (S : Set Γ) r, (wordLength (S : Set Γ) g : ℝ) * ν g) :
    IsProbability ν ∧ HasFiniteEntropy ν ∧ HasNontrivialPoissonBoundary ν ∧
      ¬ ∃ c > 0, ∀ n : ℕ, 1 ≤ n → Real.exp (c * n) ≤ growth (S : Set Γ) (n * φ (ϱ n)) := by
  have hνfun : ν = fun g => (if g = 1 then (1 : ℝ) / 2 else 0) + μ g / 2 := funext hν
  have hδ : HasSum (fun g : Γ => if g = 1 then (1 : ℝ) / 2 else 0) (1 / 2) := hasSum_ite_eq 1 _
  have hδs : Summable (fun g : Γ => if g = 1 then (1 : ℝ) / 2 else 0) := hδ.summable
  have hμ2 : HasSum (fun g => μ g / 2) (1 / 2) := hμ.2.div_const 2
  have hν0 : ∀ g, 0 ≤ ν g := fun g => by
    rw [hν]; have := hμ.1 g; split_ifs <;> positivity
  have hprob : IsProbability ν := by
    refine ⟨hν0, ?_⟩
    rw [hνfun]
    convert hδ.add hμ2 using 1; norm_num
  have hν1 : ∀ g, ν g ≤ 1 := fun g => by
    have := hprob.2.summable.le_tsum g (fun h _ => hν0 h)
    rwa [hprob.2.tsum_eq] at this
  refine ⟨hprob, ?_, ?_, ?_⟩
  · -- finite entropy
    unfold HasFiniteEntropy
    have hb : Summable fun g => Real.negMulLog (if g = 1 then (1 : ℝ) / 2 else 0) +
        ((1 / 2) * Real.negMulLog (μ g) + μ g * Real.negMulLog (1 / 2)) := by
      refine Summable.add ?_ ((hH.mul_left _).add (hμ.2.summable.mul_right _))
      apply summable_of_ne_finset_zero (s := {1})
      intro g hg
      simp only [Finset.mem_singleton] at hg
      simp [hg]
    refine Summable.of_nonneg_of_le (fun g => Real.negMulLog_nonneg (hν0 g) (hν1 g))
      (fun g => ?_) hb
    rw [hν, show μ g / 2 = μ g * (1 / 2) by ring, ← Real.negMulLog_mul]
    exact negMulLog_add_le (by split_ifs <;> norm_num) (by have := hμ.1 g; positivity)
  · -- non-trivial boundary
    obtain ⟨f, ⟨C, hC⟩, hf, x, hx, y, hy, hne⟩ := hP
    refine ⟨f, ⟨C, hC⟩, fun z => ?_, x, ?_, y, ?_, hne⟩
    · have hs1 : Summable fun w => f (z * w) * (if w = 1 then (1 : ℝ) / 2 else 0) := by
        apply summable_of_ne_finset_zero (s := {1})
        intro g hg; simp only [Finset.mem_singleton] at hg; simp [hg]
      have hs2 : Summable fun w => f (z * w) * μ w := by
        refine Summable.of_norm_bounded (g := fun w => C * μ w) (hμ.2.summable.mul_left C) ?_
        intro w
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hμ.1 w)]
        exact mul_le_mul_of_nonneg_right (hC _) (hμ.1 w)
      have e : (fun w => f (z * w) * ν w) = fun w => f (z * w) *
          (if w = 1 then (1 : ℝ) / 2 else 0) + (1 / 2) * (f (z * w) * μ w) := by
        funext w; rw [hν]; ring
      rw [e, hs1.tsum_add (hs2.mul_left _), tsum_mul_left, ← hf z]
      rw [tsum_eq_single 1 (fun w hw => by simp [hw])]
      simp; ring
    all_goals
      refine Submonoid.closure_mono (fun g hg => ?_) ‹_›
      have hg' : μ g ≠ 0 := hg
      have hpos : 0 < μ g := lt_of_le_of_ne (hμ.1 g) (Ne.symm hg')
      show ν g ≠ 0
      rw [hν]
      have : 0 ≤ (if g = 1 then (1 : ℝ) / 2 else 0) := by split_ifs <;> norm_num
      linarith
  · -- `R_1 = 0`
    rintro ⟨c, hc, hall⟩
    have h1 := hall 1 le_rfl
    have hϱ1 : ϱ 1 = 0 := by
      rw [hϱ 1]
      have : {r : ℝ | 0 < r ∧ mass ν {g | r ≤ (wordLength (S : Set Γ) g : ℝ)} < 1 / (1 : ℕ)} =
          Set.Ioi 0 := by
        ext r
        simp only [Set.mem_ofPred_eq, Set.mem_Ioi, Nat.cast_one, div_one, and_iff_left_iff_imp]
        intro hr
        unfold mass
        have hle : ∀ g, {g | r ≤ (wordLength (S : Set Γ) g : ℝ)}.indicator ν g ≤ μ g / 2 := by
          intro g
          by_cases hg : g = 1
          · subst hg
            rw [Set.indicator_of_notMem (by simp [wordLength_one]; linarith)]
            have := hμ.1 1; positivity
          · have hνg : ν g = μ g / 2 := by rw [hν g, if_neg hg, zero_add]
            exact (Set.indicator_le_self' (fun g _ => hν0 g) g).trans hνg.le
        have hsum : Summable fun g => {g | r ≤ (wordLength (S : Set Γ) g : ℝ)}.indicator ν g :=
          Summable.of_nonneg_of_le (fun g => Set.indicator_nonneg (fun g _ => hν0 g) g) hle
            hμ2.summable
        calc ∑' g, {g | r ≤ (wordLength (S : Set Γ) g : ℝ)}.indicator ν g
            ≤ ∑' g, μ g / 2 := hsum.tsum_le_tsum hle hμ2.summable
          _ = 1 / 2 := hμ2.tsum_eq
          _ < 1 := by norm_num
      rw [this, csInf_Ioi]
    have hφ0 : φ 0 = 0 := by
      rw [hφ 0]
      have hz : ∀ g : ball (S : Set Γ) 0, (wordLength (S : Set Γ) g : ℝ) * ν g = 0 := fun g => by
        have hg := g.2
        simp only [ball, Set.mem_ofPred_eq] at hg
        have h0 : (wordLength (S : Set Γ) g : ℝ) = 0 := le_antisymm hg (Nat.cast_nonneg _)
        rw [h0, zero_mul]
      rw [show (fun g : ball (S : Set Γ) 0 => (wordLength (S : Set Γ) g : ℝ) * ν g) =
        fun _ => 0 from funext hz, tsum_zero]
    rw [hϱ1, hφ0, mul_zero] at h1
    have hg0 : growth (S : Set Γ) 0 = 1 := by
      unfold growth
      rw [Nat.floor_zero, wordBall_zero]
      simp
    rw [hg0] at h1
    simp only [Nat.cast_one, mul_one] at h1
    have := Real.add_one_le_exp c
    have := Real.exp_pos c
    nlinarith [Real.add_one_lt_exp (ne_of_gt hc)]
end
