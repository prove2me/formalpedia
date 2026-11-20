-- Prove2me | solution 1 for BinarySketchTruncation.Opposite.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:50:30.802181+00:00
-- url     : https://prove2.me/submissions/e3755ec4-b988-4355-8b2c-2026c0e641ad

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_ExplicitKernel
import Definitions.Def_BinarySketchTruncation_Opposite_Model

section
namespace BinarySketchTruncation.Dev.Lemma2

open BinarySketchTruncation.Opposite


/-! ### General facts about experiments on finite additive groups -/

lemma map_add_apply {S : Type} [Fintype S] [AddCommGroup S] [DecidableEq S]
    (P : PMF S) (c t : S) : (P.map (fun u => u + c)) t = P (t - c) := by
  rw [PMF.map_apply, tsum_fintype]
  have : ∀ a : S, (t = a + c) ↔ (a = t - c) := by
    intro a; constructor <;> intro h <;> [rw [h]; rw [h]] <;> abel
  simp_rw [this]
  simp

lemma shift_apply {S : Type} [Fintype S] [AddCommGroup S] [DecidableEq S]
    (P : Experiment S) (v : S) (h : Bool) (t : S) :
    (shiftUnderOne P v h t) = P h (t - if h then v else 0) :=
  map_add_apply _ _ _

lemma independentSum_toReal {S : Type} [Fintype S] [AddCommGroup S] [DecidableEq S]
    (P Q : Experiment S) (h : Bool) (t : S) :
    (independentSum P Q h t).toReal =
      ∑ u, (P h u).toReal * ∑ v, if t = u + v then (Q h v).toReal else 0 := by
  unfold independentSum
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [ENNReal.toReal_mul]
    congr 1
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl (fun v _ => ?_)
      split_ifs <;> simp
    · intro v _
      split_ifs
      · exact PMF.apply_ne_top _ _
      · simp
  · intro u _
    refine ENNReal.mul_ne_top (PMF.apply_ne_top _ _) ?_
    rw [PMF.map_apply, tsum_fintype]
    refine ENNReal.sum_ne_top.2 (fun v _ => ?_)
    split_ifs
    · exact PMF.apply_ne_top _ _
    · simp


/-! ### The single-bit kernel -/

end BinarySketchTruncation.Dev.Lemma2

namespace BinarySketchTruncation.Opposite

open BinarySketchTruncation.Dev.Lemma2

end BinarySketchTruncation.Opposite
end

section
namespace BinarySketchTruncation.Dev.Lemma1

open BinarySketchTruncation.Opposite BinarySketchTruncation.Dev.Lemma2

section general

variable {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]

lemma pmf_toReal_sum_one (P : PMF G) : ∑ v, (P v).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun v _ => PMF.apply_ne_top _ _)]
  have := P.tsum_coe
  rw [tsum_fintype] at this
  rw [this]; simp

lemma indep_formula (h2 : ∀ x : G, x + x = 0) (P Q : Experiment G) (h : Bool) (t : G) :
    (independentSum P Q h t).toReal = ∑ v, (Q h v).toReal * (P h (t + v)).toReal := by
  rw [independentSum_toReal]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.sum_eq_single (t + v)]
  · have : t = t + v + v := by rw [add_assoc, h2, add_zero]
    simp only [← this, if_true]; ring
  · intro u _ hu
    have : ¬ t = u + v := by
      intro h'; apply hu; rw [h', add_assoc, h2, add_zero]
    simp [this]
  · simp

/-- Averaging the deterministic-shift kernels over independent `v₀ ~ ν₀`, `v₁ ~ ν₁`. -/
noncomputable def avgKernel (Kf : G → G → G → ℝ) (ν : Experiment G) (u s : G) : ℝ :=
  ∑ v₀, ∑ v₁, (ν false v₀).toReal * (ν true v₁).toReal * Kf (v₀ + v₁) u (s + v₀)

lemma avgKernel_simulates (h2 : ∀ x : G, x + x = 0) (U : Experiment G) (Kf : G → G → G → ℝ)
    (hKf : ∀ w, Simulates U (shiftUnderOne U w) (Kf w)) (ν : Experiment G) :
    Simulates U (independentSum U ν) (avgKernel Kf ν) := by
  have hneg : ∀ x y : G, x - y = x + y := by
    intro x y
    have : -y = y := neg_eq_of_add_eq_zero_right (h2 y)
    rw [sub_eq_add_neg, this]
  have n0 := pmf_toReal_sum_one (ν false)
  have n1 := pmf_toReal_sum_one (ν true)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro u s
    refine Finset.sum_nonneg (fun v₀ _ => Finset.sum_nonneg (fun v₁ _ => ?_))
    exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      ((hKf _).1.1 _ _)
  · intro u
    unfold avgKernel
    rw [Finset.sum_comm]
    have : ∀ v₀ : G, ∑ s, ∑ v₁, (ν false v₀).toReal * (ν true v₁).toReal *
        Kf (v₀ + v₁) u (s + v₀) = ∑ v₁, (ν false v₀).toReal * (ν true v₁).toReal := by
      intro v₀
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v₁ _ => ?_)
      rw [← Finset.mul_sum]
      have e : ∑ s, Kf (v₀ + v₁) u (s + v₀) = 1 := by
        have e := Equiv.sum_comp (Equiv.addRight v₀) (fun s => Kf (v₀ + v₁) u s)
        simp only [Equiv.coe_addRight] at e
        rw [e]
        exact (hKf _).1.2 u
      rw [e, mul_one]
    simp_rw [this]
    rw [← Finset.sum_mul_sum, n0, n1, mul_one]
  · intro h t
    rw [indep_formula h2]
    have step : ∑ u, (U h u).toReal * avgKernel Kf ν u t =
        ∑ v₀, ∑ v₁, (ν false v₀).toReal * (ν true v₁).toReal *
          (U h (t + v₀ - if h then v₀ + v₁ else 0)).toReal := by
      unfold avgKernel
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v₀ _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v₁ _ => ?_)
      have := (hKf (v₀ + v₁)).2 h (t + v₀)
      rw [shift_apply] at this
      rw [this, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [step]
    cases h
    · simp only [Bool.false_eq_true, ↓reduceIte, sub_zero]
      refine Finset.sum_congr rfl (fun v₀ _ => ?_)
      have : ∑ v₁, (ν false v₀).toReal * (ν true v₁).toReal * (U false (t + v₀)).toReal =
          (ν false v₀).toReal * (U false (t + v₀)).toReal * ∑ v₁, (ν true v₁).toReal := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [this, n1, mul_one]
    · simp only [↓reduceIte]
      have key : ∀ v₀ v₁ : G, t + v₀ - (v₀ + v₁) = t + v₁ := by
        intro v₀ v₁
        rw [hneg]
        calc t + v₀ + (v₀ + v₁) = t + (v₀ + v₀) + v₁ := by abel
          _ = t + v₁ := by rw [h2, add_zero]
      simp_rw [key]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v₁ _ => ?_)
      have : ∑ v₀, (ν false v₀).toReal * (ν true v₁).toReal * (U true (t + v₁)).toReal =
          (ν true v₁).toReal * (U true (t + v₁)).toReal * ∑ v₀, (ν false v₀).toReal := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [this, n0, mul_one]

end general

lemma vec_add_self (k : ℕ) (x : Vec k) : x + x = 0 := by
  funext i
  have : ∀ a : Bit, a + a = 0 := by decide
  exact this (x i)

end BinarySketchTruncation.Dev.Lemma1

namespace BinarySketchTruncation.Opposite

open BinarySketchTruncation.Dev.Lemma1

theorem chk_lemma_1 (k : ℕ) (U : Experiment (Vec k))
    (hdet : ∀ v : Vec k, Dominates U (shiftUnderOne U v)) :
    ∀ ν : Experiment (Vec k), Dominates U (independentSum U ν) := by
  intro ν
  choose Kf hKf using hdet
  exact ⟨_, avgKernel_simulates (vec_add_self k) U Kf hKf ν⟩

end BinarySketchTruncation.Opposite
end

theorem solution : type_of% @BinarySketchTruncation.Opposite.chk_lemma_1 := @BinarySketchTruncation.Opposite.chk_lemma_1
