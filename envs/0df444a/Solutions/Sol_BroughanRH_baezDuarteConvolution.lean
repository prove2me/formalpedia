-- Prove2me | solution 1 for BroughanRH.baezDuarteConvolution
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T20:04:53.731634+00:00
-- url     : https://prove2.me/submissions/d7bf6cdd-76f5-4c99-858c-167a5161577a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Theorems.Thm_NymanBeurling_moebius_dirichlet_abel_limit
import Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_moebius_bound
import Mathlib

open Finset Filter MeasureTheory

namespace IntegralsAux

/-- `e^{-y} ≤ K y^{-α}` -/
lemma exp_neg_le_rpow (α : ℝ) (hα : 0 ≤ α) :
    ∃ K : ℝ, 0 < K ∧ ∀ y : ℝ, 0 < y → Real.exp (-y) ≤ K * y ^ (-α) := by
  set m := ⌈α⌉₊
  refine ⟨1 + (m.factorial : ℝ), by positivity, fun y hy => ?_⟩
  have h1 : y ^ α ≤ 1 + y ^ m := by
    rcases le_or_gt y 1 with h | h
    · have : y ^ α ≤ 1 := Real.rpow_le_one hy.le h hα
      linarith [pow_nonneg hy.le m]
    · have : y ^ α ≤ y ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le (Nat.le_ceil α)
      rw [Real.rpow_natCast] at this
      linarith
  have h2 : y ^ m ≤ m.factorial * Real.exp y := by
    have := Real.pow_div_factorial_le_exp (x := y) hy.le m
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h3 : y ^ α ≤ (1 + m.factorial) * Real.exp y := by
    have : (1 : ℝ) ≤ Real.exp y := Real.one_le_exp hy.le
    nlinarith
  rw [Real.rpow_neg hy.le, Real.exp_neg]
  have hpos : 0 < y ^ α := Real.rpow_pos_of_pos hy α
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  calc (Real.exp y)⁻¹ * y ^ α ≤ (Real.exp y)⁻¹ * ((1 + m.factorial) * Real.exp y) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by field_simp

/-- kernel bound: `e^{-x/t^2} (t^{θ-3} + x t^{θ-5}) ≤ K x^{-α} t^{θ-3+2α}` -/
lemma kernel_bound (α : ℝ) (hα : 0 ≤ α) :
    ∃ K : ℝ, 0 < K ∧ ∀ θ x t : ℝ, 0 < x → 0 < t →
      Real.exp (-(x / t ^ 2)) * (t ^ (θ - 3) + x * t ^ (θ - 5)) ≤
        K * (x ^ (-α) * t ^ (θ - 3 + 2 * α)) := by
  obtain ⟨K1, hK1, h1⟩ := exp_neg_le_rpow α hα
  obtain ⟨K2, hK2, h2⟩ := exp_neg_le_rpow (α + 1) (by linarith)
  refine ⟨K1 + K2, by positivity, fun θ x t hx ht => ?_⟩
  have hu : 0 < x / t ^ 2 := by positivity
  have e1 := h1 _ hu
  have e2 := h2 _ hu
  have ht2 : (t ^ 2 : ℝ) = t ^ (2 : ℝ) := by rw [Real.rpow_two]
  have hpow : ∀ β : ℝ, (x / t ^ 2) ^ (-β) = x ^ (-β) * t ^ (2 * β) := by
    intro β
    rw [Real.div_rpow hx.le (by positivity), ht2, ← Real.rpow_mul ht.le, Real.rpow_neg hx.le,
      div_eq_mul_inv, ← Real.rpow_neg ht.le]
    ring_nf
  rw [hpow] at e1 e2
  have a1 : t ^ (θ - 3) * (x ^ (-α) * t ^ (2 * α)) = x ^ (-α) * t ^ (θ - 3 + 2 * α) := by
    rw [Real.rpow_add ht]; ring
  have a2 : x * t ^ (θ - 5) * (x ^ (-(α + 1)) * t ^ (2 * (α + 1))) =
      x ^ (-α) * t ^ (θ - 3 + 2 * α) := by
    have : x ^ (-(α + 1)) = x ^ (-α) * x⁻¹ := by
      rw [neg_add, Real.rpow_add hx, Real.rpow_neg_one]
    rw [this]
    have : t ^ (θ - 5) * t ^ (2 * (α + 1)) = t ^ (θ - 3 + 2 * α) := by
      rw [← Real.rpow_add ht]; congr 1; ring
    calc x * t ^ (θ - 5) * (x ^ (-α) * x⁻¹ * t ^ (2 * (α + 1)))
        = x ^ (-α) * (t ^ (θ - 5) * t ^ (2 * (α + 1))) * (x * x⁻¹) := by ring
      _ = _ := by rw [this, mul_inv_cancel₀ hx.ne']; ring
  have p1 : 0 ≤ t ^ (θ - 3) := by positivity
  have p2 : 0 ≤ x * t ^ (θ - 5) := by positivity
  calc Real.exp (-(x / t ^ 2)) * (t ^ (θ - 3) + x * t ^ (θ - 5))
      = t ^ (θ - 3) * Real.exp (-(x / t ^ 2)) + x * t ^ (θ - 5) * Real.exp (-(x / t ^ 2)) := by
        ring
    _ ≤ t ^ (θ - 3) * (K1 * (x ^ (-α) * t ^ (2 * α))) +
        x * t ^ (θ - 5) * (K2 * (x ^ (-(α + 1)) * t ^ (2 * (α + 1)))) := by
        gcongr
    _ = K1 * (t ^ (θ - 3) * (x ^ (-α) * t ^ (2 * α))) +
        K2 * (x * t ^ (θ - 5) * (x ^ (-(α + 1)) * t ^ (2 * (α + 1)))) := by ring
    _ = (K1 + K2) * (x ^ (-α) * t ^ (θ - 3 + 2 * α)) := by
        rw [a1, a2]; ring

/-- The Mertens function bound in the form needed for Abel summation. -/
lemma mertens_bound (θ : ℝ) (hθ : 1 / 2 < θ)
    (hM : ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε))) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      |∑ k ∈ Icc 0 ⌊t⌋₊, (ArithmeticFunction.moebius k : ℝ)| ≤ C * t ^ θ := by
  obtain ⟨C, hC⟩ := (hM (θ - 1/2) (by linarith)).bound
  rw [eventually_atTop] at hC
  obtain ⟨N0, hN0⟩ := hC
  refine ⟨max C 0 + N0 + 1, by positivity, fun t ht => ?_⟩
  set N := ⌊t⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff _ |>.mpr ht
  have hNt : (N : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsum : ∑ k ∈ Icc 0 N, (ArithmeticFunction.moebius k : ℝ) =
      ∑ k ∈ Icc 1 N, (ArithmeticFunction.moebius k : ℝ) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, ← Finset.Icc_add_one_left_eq_Ioc]
    simp
  have hpowN : (N : ℝ) ^ θ ≤ t ^ θ := Real.rpow_le_rpow hNpos.le hNt (by linarith)
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ θ := Real.one_le_rpow (by exact_mod_cast hN1) (by linarith)
  rw [hsum]
  rcases le_or_gt N0 N with h | h
  · have hb := hN0 N h
    have e : ‖∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ)‖ =
        |∑ k ∈ Icc 1 N, (ArithmeticFunction.moebius k : ℝ)| := by
      have : (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ)) =
          ((∑ k ∈ Icc 1 N, (ArithmeticFunction.moebius k : ℝ) : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    have eθ : (1:ℝ)/2 + (θ - 1/2) = θ := by ring
    rw [e, eθ, Real.norm_of_nonneg (by positivity)] at hb
    calc _ ≤ C * (N : ℝ) ^ θ := hb
      _ ≤ max C 0 * (N : ℝ) ^ θ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ (max C 0 + N0 + 1) * t ^ θ := by
        apply mul_le_mul (by linarith) hpowN (by positivity) (by positivity)
  · have hb : |∑ k ∈ Icc 1 N, (ArithmeticFunction.moebius k : ℝ)| ≤ N := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k ∈ Icc 1 N, |(ArithmeticFunction.moebius k : ℝ)| ≤ ∑ k ∈ Icc 1 N, (1 : ℝ) := by
            apply Finset.sum_le_sum; intro k _
            have := ArithmeticFunction.abs_moebius_le_one (n := k)
            exact_mod_cast this
        _ = N := by simp
    have : (N : ℝ) ≤ N0 := by exact_mod_cast h.le
    calc _ ≤ (N0 : ℝ) := hb.trans this
      _ ≤ (max C 0 + N0 + 1) * 1 := by nlinarith [le_max_right C 0]
      _ ≤ (max C 0 + N0 + 1) * t ^ θ := by
        apply mul_le_mul_of_nonneg_left (h1.trans hpowN) (by positivity)


lemma integral_rpow_neg_le (p : ℝ) (hp : 1 < p) (N : ℕ) (hN : 1 ≤ N) :
    ∫ t in Set.Ioc (1 : ℝ) N, t ^ (-p) ≤ 1 / (p - 1) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [← intervalIntegral.integral_of_le hN']
  rw [integral_rpow (Or.inr ⟨by linarith, by
    rw [Set.uIcc_of_le hN']; intro h; exact absurd h.1 (by norm_num)⟩)]
  have h1 : (0 : ℝ) ≤ (N : ℝ) ^ (-p + 1) := by positivity
  rw [Real.one_rpow]
  have : -p + 1 < 0 := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have e : ((N : ℝ) ^ (-p + 1) - 1) / (-p + 1) = (1 - (N : ℝ) ^ (-p + 1)) / (p - 1) := by
    rw [← neg_div_neg_eq]; congr 1 <;> ring
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith) hp1.le
  
lemma abel_bound (θ C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 1 ≤ t → |∑ k ∈ Icc 0 ⌊t⌋₊, (ArithmeticFunction.moebius k : ℝ)| ≤ C * t ^ θ)
    (f f' : ℝ → ℝ) (hf : ∀ t : ℝ, 1 ≤ t → HasDerivAt f (f' t) t)
    (hf'c : ContinuousOn f' (Set.Ici 1))
    (B p : ℝ) (hp : 1 < p) (hB : ∀ t : ℝ, 1 ≤ t → t ^ θ * |f' t| ≤ B * t ^ (-p))
    (N : ℕ) (hN : 1 ≤ N) :
    |∑ k ∈ Icc 0 N, f k * (ArithmeticFunction.moebius k : ℝ)| ≤
      C * (N : ℝ) ^ θ * |f N| + C * B / (p - 1) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hderiv : ∀ t ∈ Set.Icc (1 : ℝ) N, deriv f t = f' t := fun t ht => (hf t ht.1).deriv
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) N, DifferentiableAt ℝ f t :=
    fun t ht => (hf t ht.1).differentiableAt
  have hint : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) N) := by
    have : IntegrableOn f' (Set.Icc (1 : ℝ) N) :=
      (hf'c.mono (Set.Icc_subset_Ici_self)).integrableOn_Icc
    exact this.congr_fun (fun t ht => (hderiv t ht).symm) measurableSet_Icc
  rw [sum_mul_eq_sub_integral_mul₀' (c := fun k => (ArithmeticFunction.moebius k : ℝ))
    (by simp) N hdiff hint]
  have hB0 : 0 ≤ B := by
    have := hB 1 le_rfl
    simp at this
    linarith [abs_nonneg (f' 1)]
  have h1 : |f N * ∑ k ∈ Icc 0 N, (ArithmeticFunction.moebius k : ℝ)| ≤ C * (N : ℝ) ^ θ * |f N| := by
    rw [abs_mul]
    have := hC N hN'
    rw [Nat.floor_natCast] at this
    nlinarith [abs_nonneg (f N)]
  have h2 : |∫ t in Set.Ioc (1 : ℝ) N, deriv f t *
      ∑ k ∈ Icc 0 ⌊t⌋₊, (ArithmeticFunction.moebius k : ℝ)| ≤ C * B / (p - 1) := by
    have hg : IntegrableOn (fun t : ℝ => C * B * t ^ (-p)) (Set.Ioc (1 : ℝ) N) := by
      refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
      exact continuousOn_const.mul (continuousOn_id.rpow_const fun t ht =>
        Or.inl (ne_of_gt (lt_of_lt_of_le one_pos ht.1)))
    have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 : ℝ) N)), ‖deriv f t *
        ∑ k ∈ Icc 0 ⌊t⌋₊, (ArithmeticFunction.moebius k : ℝ)‖ ≤ C * B * t ^ (-p) := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have ht1 : 1 ≤ t := ht.1.le
      rw [hderiv t ⟨ht1, ht.2⟩, Real.norm_eq_abs, abs_mul]
      have a := hC t ht1
      have b := hB t ht1
      calc |f' t| * |∑ k ∈ Icc 0 ⌊t⌋₊, (ArithmeticFunction.moebius k : ℝ)|
          ≤ |f' t| * (C * t ^ θ) := mul_le_mul_of_nonneg_left a (abs_nonneg _)
        _ = C * (t ^ θ * |f' t|) := by ring
        _ ≤ C * (B * t ^ (-p)) := mul_le_mul_of_nonneg_left b hC0
        _ = C * B * t ^ (-p) := by ring
    have := norm_integral_le_of_norm_le hg hae
    rw [← Real.norm_eq_abs]
    refine this.trans ?_
    rw [integral_const_mul]
    have := integral_rpow_neg_le p hp N hN
    calc C * B * ∫ t in Set.Ioc (1 : ℝ) N, t ^ (-p) ≤ C * B * (1 / (p - 1)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  calc _ ≤ |f N * ∑ k ∈ Icc 0 N, (ArithmeticFunction.moebius k : ℝ)| +
        |∫ t in Set.Ioc (1 : ℝ) N, deriv f t *
          ∑ k ∈ Icc 0 ⌊t⌋₊, (ArithmeticFunction.moebius k : ℝ)| := abs_sub _ _
    _ ≤ _ := add_le_add h1 h2


lemma rpow_sub_nat' {t : ℝ} (ht : 0 < t) (θ : ℝ) (k : ℕ) : t ^ θ / t ^ k = t ^ (θ - k) := by
  rw [Real.rpow_sub ht, Real.rpow_natCast]

end IntegralsAux

namespace IntegralsAux

open ArithmeticFunction

lemma range_succ_eq_Icc (N : ℕ) : Finset.range (N + 1) = Finset.Icc 0 N := by
  ext k; simp

/-- If all partial sums over `Icc 0 N` (`N ≥ 1`) are bounded by `B` and the series has sum `S`,
then `|S| ≤ B`. -/
lemma moebius_real_hasSum (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, HasSum (fun n : ℕ => (n : ℝ) ^ (-(1 + ε)) * (moebius n : ℝ)) r ∧
      LSeries (fun n => (moebius n : ℂ)) (1 + (ε : ℂ)) = (r : ℂ) := by
  have hs : 1 < (1 + (ε : ℂ)).re := by simp; linarith
  have hterm : ∀ n : ℕ, LSeries.term (fun n => (moebius n : ℂ)) (1 + (ε : ℂ)) n =
      (((n : ℝ) ^ (-(1 + ε)) * (moebius n : ℝ) : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn.ne']
      have : (n : ℂ) ^ (1 + (ε : ℂ)) = (((n : ℝ) ^ (1 + ε) : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; push_cast; ring_nf
      rw [this, Real.rpow_neg (Nat.cast_nonneg n)]
      push_cast
      ring
  have hsumC : LSeriesSummable (fun n => (moebius n : ℂ)) (1 + (ε : ℂ)) :=
    LSeriesSummable_moebius_iff.mpr hs
  have h2 : LSeries.term (fun n => (moebius n : ℂ)) (1 + (ε : ℂ)) =
      fun n : ℕ => (((n : ℝ) ^ (-(1 + ε)) * (moebius n : ℝ) : ℝ) : ℂ) := funext hterm
  rw [LSeriesSummable, h2] at hsumC
  have hsumR := Complex.summable_ofReal.mp hsumC
  refine ⟨_, hsumR.hasSum, ?_⟩
  rw [LSeries, h2, Complex.ofReal_tsum]

lemma moebius_div_tendsto_zero (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 1 ≤ t → |∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (moebius k : ℝ)| ≤ C * t ^ (5/8 : ℝ))
    (L : ℝ) (hL : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 0 N, (k : ℝ)⁻¹ * (moebius k : ℝ)) atTop (nhds L)) :
    L = 0 := by
  -- step 1: |r(ε) - L| ≤ 40 C ε
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ r : ℝ,
      HasSum (fun n : ℕ => (n : ℝ) ^ (-(1 + ε)) * (moebius n : ℝ)) r → |r - L| ≤ C * (40 * ε) := by
    intro ε hε hε1 r hr
    set f : ℝ → ℝ := fun t => t ^ (-(1 + ε)) - t⁻¹ with hf
    set f' : ℝ → ℝ := fun t => (-(1 + ε)) * t ^ (-(1 + ε) - 1) + (t ^ 2)⁻¹ with hf'
    have hderiv : ∀ t : ℝ, 1 ≤ t → HasDerivAt f (f' t) t := by
      intro t ht
      have ht0 : t ≠ 0 := by positivity
      have h1 := Real.hasDerivAt_rpow_const (x := t) (p := -(1 + ε)) (Or.inl ht0)
      have h2 := hasDerivAt_inv ht0
      have h3 : HasDerivAt (fun t : ℝ => t ^ (-(1 + ε)) - t⁻¹)
          ((-(1 + ε)) * t ^ (-(1 + ε) - 1) - -(t ^ 2)⁻¹) t := h1.sub h2
      have e : f' t = (-(1 + ε)) * t ^ (-(1 + ε) - 1) - -(t ^ 2)⁻¹ := by
        simp only [hf']; ring
      rw [e]; exact h3
    have hcont : ContinuousOn f' (Set.Ici 1) := by
      have : ∀ t ∈ Set.Ici (1 : ℝ), t ≠ 0 := fun t ht => by
        have : (1 : ℝ) ≤ t := ht; positivity
      apply ContinuousOn.add
      · exact continuousOn_const.mul (continuousOn_id.rpow_const fun t ht => Or.inl (this t ht))
      · exact (continuousOn_id.pow 2).inv₀ fun t ht => pow_ne_zero _ (this t ht)
    have hB : ∀ t : ℝ, 1 ≤ t → t ^ (5/8 : ℝ) * |f' t| ≤ (5 * ε) * t ^ (-(9/8 : ℝ)) := by
      intro t ht
      have ht0 : 0 < t := by linarith
      have e1 : t ^ (-(1 + ε) - 1) = t ^ (-(2:ℝ)) * t ^ (-ε) := by
        rw [← Real.rpow_add ht0]; ring_nf
      have e2 : (t ^ 2)⁻¹ = t ^ (-(2:ℝ)) := by
        rw [Real.rpow_neg ht0.le, Real.rpow_two]
      have hte : t ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith)
      have hte0 : 0 < t ^ (-ε) := Real.rpow_pos_of_pos ht0 _
      have hlog : 1 - t ^ (-ε) ≤ ε * (4 * t ^ (1/4 : ℝ)) := by
        have a1 : t ^ (-ε) = Real.exp (-ε * Real.log t) := by
          rw [Real.rpow_def_of_pos ht0]; ring_nf
        have a2 : 1 - ε * Real.log t ≤ Real.exp (-ε * Real.log t) := by
          linarith [Real.add_one_le_exp (-ε * Real.log t)]
        have a3 : Real.log t ≤ t ^ (1/4 : ℝ) / (1/4) := Real.log_le_rpow_div ht0.le (by norm_num)
        rw [a1]
        nlinarith
      have hfabs : |f' t| ≤ t ^ (-(2:ℝ)) * (5 * ε * t ^ (1/4 : ℝ)) := by
        simp only [hf']
        rw [e1, e2]
        have : (-(1 + ε)) * (t ^ (-(2:ℝ)) * t ^ (-ε)) + t ^ (-(2:ℝ)) =
            t ^ (-(2:ℝ)) * ((1 - t ^ (-ε)) - ε * t ^ (-ε)) := by ring
        rw [this, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos ht0 _).le
        have h14 : 1 ≤ t ^ (1/4 : ℝ) := Real.one_le_rpow ht (by norm_num)
        rw [abs_le]
        constructor <;> nlinarith
      calc t ^ (5/8 : ℝ) * |f' t| ≤ t ^ (5/8 : ℝ) * (t ^ (-(2:ℝ)) * (5 * ε * t ^ (1/4 : ℝ))) :=
            mul_le_mul_of_nonneg_left hfabs (Real.rpow_pos_of_pos ht0 _).le
        _ = (5 * ε) * (t ^ (5/8 : ℝ) * t ^ (-(2:ℝ)) * t ^ (1/4 : ℝ)) := by ring
        _ = (5 * ε) * t ^ (-(9/8 : ℝ)) := by
            rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]; norm_num
    have hbdN : ∀ N : ℕ, 1 ≤ N →
        |∑ k ∈ Finset.Icc 0 N, f k * (moebius k : ℝ)| ≤ C * (N : ℝ) ^ (-(3/8 : ℝ)) + C * (40 * ε) := by
      intro N hN
      have h := abel_bound (5/8) C hC0 hC f f' hderiv hcont (5 * ε) (9/8) (by norm_num) hB N hN
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hN0 : (0 : ℝ) < N := by linarith
      have hfN : (N : ℝ) ^ (5/8 : ℝ) * |f N| ≤ (N : ℝ) ^ (-(3/8 : ℝ)) := by
        simp only [hf]
        have a1 : (N : ℝ) ^ (-(1 + ε)) ≤ (N : ℝ)⁻¹ := by
          rw [← Real.rpow_neg_one]
          exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        have a2 : 0 ≤ (N : ℝ) ^ (-(1 + ε)) := (Real.rpow_pos_of_pos hN0 _).le
        rw [abs_of_nonpos (by linarith)]
        calc (N : ℝ) ^ (5/8 : ℝ) * -((N : ℝ) ^ (-(1 + ε)) - (N : ℝ)⁻¹)
            ≤ (N : ℝ) ^ (5/8 : ℝ) * (N : ℝ)⁻¹ := by
              apply mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_pos_of_pos hN0 _).le
          _ = (N : ℝ) ^ (-(3/8 : ℝ)) := by
              rw [← Real.rpow_neg_one, ← Real.rpow_add hN0]; norm_num
      calc _ ≤ C * (N : ℝ) ^ (5/8 : ℝ) * |f N| + C * (5 * ε) / (9/8 - 1) := h
        _ ≤ C * (N : ℝ) ^ (-(3/8 : ℝ)) + C * (40 * ε) := by
          rw [mul_assoc]
          have := mul_le_mul_of_nonneg_left hfN hC0
          have e : C * (5 * ε) / (9/8 - 1) = C * (40 * ε) := by ring
          linarith
    -- pass to the limit
    have hsumdiff : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 0 N, f k * (moebius k : ℝ)) atTop
        (nhds (r - L)) := by
      have hr' : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 0 N, (k : ℝ) ^ (-(1 + ε)) * (moebius k : ℝ))
          atTop (nhds r) := by
        have := hr.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
        refine this.congr fun N => ?_
        simp only [Function.comp, range_succ_eq_Icc]
      refine (hr'.sub hL).congr fun N => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hf]; ring
    have hlim : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-(3/8 : ℝ)) + C * (40 * ε)) atTop
        (nhds (C * 0 + C * (40 * ε))) := by
      refine ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 3/8)).comp
        tendsto_natCast_atTop_atTop |>.const_mul C).add_const _
    rw [mul_zero, zero_add] at hlim
    exact le_of_tendsto_of_tendsto ((continuous_abs.tendsto _).comp hsumdiff) hlim
      (Filter.eventually_atTop.mpr ⟨1, fun N hN => hbdN N hN⟩)
  by_contra hL0
  have hd : 0 < |L| := abs_pos.mpr hL0
  have hlim := NymanBeurling.moebius_dirichlet_abel_limit
  have ev1 : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ‖LSeries (fun n => (moebius n : ℂ)) (1 + (ε : ℂ))‖ < |L| / 2 := by
    have := hlim.norm
    rw [norm_zero] at this
    exact this.eventually (gt_mem_nhds (by linarith))
  have ev2 : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε := self_mem_nhdsWithin
  have ev3 : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < min 1 (|L| / (80 * C + 1)) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (lt_min one_pos (by positivity)))
  obtain ⟨ε, h1, h2, h3⟩ := (ev1.and (ev2.and ev3)).exists
  obtain ⟨r, hr, hrL⟩ := moebius_real_hasSum ε h2
  have hk := key ε h2 (lt_of_lt_of_le h3 (min_le_left _ _)) r hr
  rw [hrL, Complex.norm_real, Real.norm_eq_abs] at h1
  have h4 : ε * (80 * C + 1) < |L| := by
    have := lt_of_lt_of_le h3 (min_le_right _ _)
    rwa [lt_div_iff₀ (by positivity)] at this
  have h5 : |L| ≤ |r - L| + |r| := by
    calc |L| = |r - (r - L)| := by ring_nf
      _ ≤ |r| + |r - L| := abs_sub _ _
      _ = _ := by ring
  nlinarith



lemma integral_Ioc_rpow_le (r : ℝ) (hr : r < -1) (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    ∫ t in Set.Ioc (N : ℝ) M, t ^ r ≤ (N : ℝ) ^ (r + 1) / (-(r + 1)) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
  rw [← intervalIntegral.integral_of_le hNM']
  rw [integral_rpow (Or.inr ⟨by linarith, by
    rw [Set.uIcc_of_le hNM']; intro h; linarith [h.1]⟩)]
  have h1 : (0 : ℝ) ≤ (M : ℝ) ^ (r + 1) := by positivity
  have hp1 : 0 < -(r + 1) := by linarith
  have e : ((M : ℝ) ^ (r + 1) - (N : ℝ) ^ (r + 1)) / (r + 1) =
      ((N : ℝ) ^ (r + 1) - (M : ℝ) ^ (r + 1)) / (-(r + 1)) := by
    rw [← neg_div_neg_eq]; congr 1; ring
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith) hp1.le

/-- Tail bound: `|∑_{n ≤ N} μ(n)/n| ≤ D N^{θ-1}`. -/
lemma moebius_div_tail (θ C : ℝ) (hθ1 : θ < 1) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 1 ≤ t → |∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (moebius k : ℝ)| ≤ C * t ^ θ)
    (hQ : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 0 N, (k : ℝ)⁻¹ * (moebius k : ℝ)) atTop (nhds 0))
    (N : ℕ) (hN : 1 ≤ N) :
    |∑ k ∈ Finset.Icc 0 N, (k : ℝ)⁻¹ * (moebius k : ℝ)| ≤ C * (1 + 1 / (1 - θ)) * (N : ℝ) ^ (θ - 1) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have key : ∀ M : ℕ, N ≤ M →
      |∑ k ∈ Finset.Icc 0 M, (k : ℝ)⁻¹ * (moebius k : ℝ) - ∑ k ∈ Finset.Icc 0 N, (k : ℝ)⁻¹ * (moebius k : ℝ)|
        ≤ C * (M : ℝ) ^ (θ - 1) + C * (1 + 1 / (1 - θ)) * (N : ℝ) ^ (θ - 1) := by
    intro M hM
    have hM' : (N : ℝ) ≤ M := by exact_mod_cast hM
    have hM1 : (1 : ℝ) ≤ M := le_trans hN' hM'
    have hsplit : ∑ k ∈ Finset.Icc 0 M, (k : ℝ)⁻¹ * (moebius k : ℝ) -
        ∑ k ∈ Finset.Icc 0 N, (k : ℝ)⁻¹ * (moebius k : ℝ) =
        ∑ k ∈ Finset.Ioc N M, (k : ℝ)⁻¹ * (moebius k : ℝ) := by
      rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le M), Finset.Icc_eq_cons_Ioc (Nat.zero_le N),
        Finset.sum_cons, Finset.sum_cons, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le N) hM]
      ring
    have hdiff : ∀ t ∈ Set.Icc (N : ℝ) M, DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t := fun t ht =>
      differentiableAt_inv (ne_of_gt (lt_of_lt_of_le (by linarith) ht.1))
    have hderiv : ∀ t ∈ Set.Icc (N : ℝ) M, deriv (fun t : ℝ => t⁻¹) t = -(t ^ 2)⁻¹ := fun t _ => by
      simp [deriv_inv]
    have hint : IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc (N : ℝ) M) := by
      have : IntegrableOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc (N : ℝ) M) := by
        refine ContinuousOn.integrableOn_Icc ?_
        exact ((continuousOn_id.pow 2).inv₀ fun t ht =>
          pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le (by linarith) ht.1))).neg
      exact this.congr_fun (fun t ht => (hderiv t ht).symm) measurableSet_Icc
    have habel := sum_mul_eq_sub_sub_integral_mul' (c := fun k => (moebius k : ℝ)) hM hdiff hint
    rw [hsplit, habel]
    have hA : ∀ m : ℕ, 1 ≤ m → |(m : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 0 m, (moebius k : ℝ)| ≤ C * (m : ℝ) ^ (θ - 1) := by
      intro m hm
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hm0 : (0 : ℝ) < m := by linarith
      have := hC m hm'
      rw [Nat.floor_natCast] at this
      rw [abs_mul, abs_inv, abs_of_pos hm0, Real.rpow_sub_one hm0.ne']
      rw [inv_mul_le_iff₀ hm0]
      calc _ ≤ C * (m : ℝ) ^ θ := this
        _ = _ := by field_simp
    have hI : |∫ t in Set.Ioc (N : ℝ) M, deriv (fun t : ℝ => t⁻¹) t *
        ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (moebius k : ℝ)| ≤ C * (1 / (1 - θ)) * (N : ℝ) ^ (θ - 1) := by
      have hg : IntegrableOn (fun t : ℝ => C * t ^ (θ - 2)) (Set.Ioc (N : ℝ) M) := by
        refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
        exact continuousOn_const.mul (continuousOn_id.rpow_const fun t ht =>
          Or.inl (ne_of_gt (lt_of_lt_of_le one_pos (le_trans hN' ht.1))))
      have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc (N : ℝ) M)), ‖deriv (fun t : ℝ => t⁻¹) t *
          ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (moebius k : ℝ)‖ ≤ C * t ^ (θ - 2) := by
        rw [ae_restrict_iff' measurableSet_Ioc]
        refine Filter.Eventually.of_forall fun t ht => ?_
        have ht1 : 1 ≤ t := le_trans hN' ht.1.le
        have ht0 : 0 < t := by linarith
        rw [hderiv t ⟨ht.1.le, ht.2⟩, Real.norm_eq_abs, abs_mul, abs_neg, abs_inv,
          abs_of_pos (by positivity : 0 < t ^ 2)]
        have a := hC t ht1
        have e : t ^ (θ - 2) = (t ^ 2)⁻¹ * t ^ θ := by
          rw [show θ - 2 = θ - ((2 : ℕ) : ℝ) by norm_num, ← rpow_sub_nat' ht0]; ring
        rw [e]
        calc (t ^ 2)⁻¹ * |∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (moebius k : ℝ)| ≤ (t ^ 2)⁻¹ * (C * t ^ θ) :=
              mul_le_mul_of_nonneg_left a (by positivity)
          _ = _ := by ring
      have := norm_integral_le_of_norm_le hg hae
      rw [← Real.norm_eq_abs]
      refine this.trans ?_
      rw [integral_const_mul]
      have h2 := integral_Ioc_rpow_le (θ - 2) (by linarith) N M hN hM
      rw [show θ - 2 + 1 = θ - 1 by ring, show -(θ - 1) = 1 - θ by ring] at h2
      calc C * ∫ t in Set.Ioc (N : ℝ) M, t ^ (θ - 2) ≤ C * ((N : ℝ) ^ (θ - 1) / (1 - θ)) :=
            mul_le_mul_of_nonneg_left h2 hC0
        _ = _ := by ring
    have h1 := hA M (le_trans hN hM)
    have h2 := hA N hN
    calc |(M : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 0 M, (moebius k : ℝ) - (N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 0 N, (moebius k : ℝ) -
          ∫ t in Set.Ioc (N : ℝ) M, deriv (fun t : ℝ => t⁻¹) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (moebius k : ℝ)|
        ≤ |(M : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 0 M, (moebius k : ℝ)| + |(N : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 0 N, (moebius k : ℝ)| +
          |∫ t in Set.Ioc (N : ℝ) M, deriv (fun t : ℝ => t⁻¹) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (moebius k : ℝ)| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_sub _ _
      _ ≤ C * (M : ℝ) ^ (θ - 1) + C * (N : ℝ) ^ (θ - 1) + C * (1 / (1 - θ)) * (N : ℝ) ^ (θ - 1) := by
          gcongr
      _ = _ := by ring
  -- let M → ∞
  have hlimL : Tendsto (fun M : ℕ => |∑ k ∈ Finset.Icc 0 M, (k : ℝ)⁻¹ * (moebius k : ℝ) -
      ∑ k ∈ Finset.Icc 0 N, (k : ℝ)⁻¹ * (moebius k : ℝ)|) atTop
      (nhds |0 - ∑ k ∈ Finset.Icc 0 N, (k : ℝ)⁻¹ * (moebius k : ℝ)|) :=
    (continuous_abs.tendsto _).comp (hQ.sub_const _)
  have hlimR : Tendsto (fun M : ℕ => C * (M : ℝ) ^ (θ - 1) + C * (1 + 1 / (1 - θ)) * (N : ℝ) ^ (θ - 1))
      atTop (nhds (C * 0 + C * (1 + 1 / (1 - θ)) * (N : ℝ) ^ (θ - 1))) := by
    refine Tendsto.add_const _ (Tendsto.const_mul _ ?_)
    have := (tendsto_rpow_neg_atTop (by linarith : (0:ℝ) < 1 - θ)).comp tendsto_natCast_atTop_atTop
    refine this.congr fun M => ?_
    simp only [Function.comp]; congr 1; ring
  have := le_of_tendsto_of_tendsto hlimL hlimR (Filter.eventually_atTop.mpr ⟨N, key⟩)
  rw [zero_sub, abs_neg, mul_zero, zero_add] at this
  exact this

end IntegralsAux

open IntegralsAux ArithmeticFunction

theorem solution :
    let g (t : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.moebius n : ℝ) / n
    ∀ f : ℝ → ℂ, ContinuousOn f (Set.Ioi 0) →
      (∀ σ : ℝ, -(1/2) < σ → σ ≤ 0 → MeasureTheory.IntegrableOn (fun t : ℝ => t^(-σ-1)*‖f t‖) (Set.Ioi 0)) →
      (∀ s : ℂ, -(1/2) < s.re → s.re < 0 → (∫ t in Set.Ioi (0 : ℝ), (t : ℂ)^(-s-1)*f t) ≠ 0) →
      ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop
        (fun x : ℝ => ∫ t in Set.Ioi (0 : ℝ), ((g (x*t) / t : ℝ) : ℂ) * f (1/t))
        (fun x : ℝ => x^(-(1/2)+ε)) := by
  intro g f _ hint _ ε hε
  have hM := moebius_summatory_rpow_bound_of_riemannHypothesis riemann_hypothesis
  obtain ⟨L, hL⟩ := moebius_dirichlet_partialSum_tendsto_of_moebius_bound 1 (by norm_num) hM
  have hL' : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 0 N, (k : ℝ)⁻¹ * (moebius k : ℝ)) atTop (nhds L) := by
    refine hL.congr fun N => ?_
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, ← Finset.Icc_add_one_left_eq_Ioc]
    simp only [Nat.cast_zero, inv_zero, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Real.rpow_neg_one]; ring
  obtain ⟨C0, hC00, hC0⟩ := mertens_bound (5/8) (by norm_num) hM
  have hL0 : L = 0 := moebius_div_tendsto_zero C0 hC00.le hC0 L hL'
  rw [hL0] at hL'
  set δ := min ε (1/2) with hδ
  have hδ0 : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ ≤ 1/2 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  set θ := 1 / 2 + δ / 2 with hθ
  obtain ⟨C, hC0', hC⟩ := mertens_bound θ (by rw [hθ]; linarith) hM
  set D := C * (1 + 1 / (1 - θ)) with hD
  have hθ1 : θ < 1 := by rw [hθ]; linarith
  have hD0 : 0 ≤ D := by
    have : 0 < 1 - θ := by linarith
    rw [hD]; positivity
  -- bound on g
  have hgb : ∀ y : ℝ, 0 < y → |g y| ≤ 2 * D * y ^ (θ - 1) := by
    intro y hy
    rcases lt_or_ge y 1 with h | h
    · have : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr h
      simp only [g, this]
      simp only [Finset.Icc_eq_empty_of_lt, zero_lt_one, Finset.sum_empty, abs_zero]
      positivity
    · set N := ⌊y⌋₊
      have hN1 : 1 ≤ N := Nat.one_le_floor_iff _ |>.mpr h
      have hgN : g y = ∑ k ∈ Finset.Icc 0 N, (k : ℝ)⁻¹ * (moebius k : ℝ) := by
        simp only [g]
        rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, ← Finset.Icc_add_one_left_eq_Ioc]
        simp only [Nat.cast_zero, inv_zero, zero_mul, zero_add]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [hgN]
      have ht := moebius_div_tail θ C hθ1 hC0'.le hC hL' N hN1
      have hNy : (N : ℝ) ≤ y := Nat.floor_le hy.le
      have hyN : y ≤ 2 * N := by
        have := Nat.lt_floor_add_one y
        have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
        linarith
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
      have hpow : (N : ℝ) ^ (θ - 1) ≤ 2 * y ^ (θ - 1) := by
        have a : (N : ℝ) ^ (θ - 1) ≤ (y / 2) ^ (θ - 1) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
        have b : (y / 2) ^ (θ - 1) = y ^ (θ - 1) * 2 ^ (1 - θ) := by
          rw [Real.div_rpow hy.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
          ring_nf
        have c : (2 : ℝ) ^ (1 - θ) ≤ 2 := by
          calc (2 : ℝ) ^ (1 - θ) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 2 := Real.rpow_one 2
        have d : 0 ≤ y ^ (θ - 1) := (Real.rpow_pos_of_pos hy _).le
        nlinarith
      calc _ ≤ D * (N : ℝ) ^ (θ - 1) := ht
        _ ≤ D * (2 * y ^ (θ - 1)) := mul_le_mul_of_nonneg_left hpow hD0
        _ = _ := by ring
  -- integrability of the comparison function
  have hI : IntegrableOn (fun t : ℝ => t ^ (θ - 2) * ‖f (1 / t)‖) (Set.Ioi 0) := by
    have h1 := hint (θ - 1) (by rw [hθ]; linarith) (by linarith)
    have h2 := (integrableOn_Ioi_comp_rpow_iff (fun t : ℝ => t ^ (-(θ - 1) - 1) * ‖f t‖)
      (p := -1) (by norm_num)).mpr h1
    refine h2.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := ht
    simp only [smul_eq_mul]
    rw [Real.rpow_neg_one, one_div, abs_neg, abs_one, one_mul, Real.inv_rpow ht0.le,
      ← Real.rpow_neg ht0.le]
    rw [← mul_assoc, ← Real.rpow_add ht0]
    congr 2; ring
  set I := ∫ t in Set.Ioi (0 : ℝ), t ^ (θ - 2) * ‖f (1 / t)‖ with hIdef
  refine Asymptotics.IsBigO.of_bound (2 * D * I) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), ‖((g (x * t) / t : ℝ) : ℂ) * f (1 / t)‖ ≤
      (2 * D * x ^ (θ - 1)) * (t ^ (θ - 2) * ‖f (1 / t)‖) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht0 : 0 < t := ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos ht0]
    have := hgb (x * t) (by positivity)
    have e : (x * t) ^ (θ - 1) / t = x ^ (θ - 1) * t ^ (θ - 2) := by
      rw [Real.mul_rpow hx0.le ht0.le, show θ - 2 = θ - 1 - ((1 : ℕ) : ℝ) by push_cast; ring,
        ← rpow_sub_nat' ht0]
      ring
    calc |g (x * t)| / t * ‖f (1 / t)‖ ≤ (2 * D * (x * t) ^ (θ - 1)) / t * ‖f (1 / t)‖ := by
          gcongr
      _ = (2 * D * x ^ (θ - 1)) * (t ^ (θ - 2) * ‖f (1 / t)‖) := by
          rw [mul_div_assoc, e]; ring
  have := norm_integral_le_of_norm_le (hI.const_mul (2 * D * x ^ (θ - 1))) hb
  rw [integral_const_mul] at this
  refine this.trans ?_
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi fun t ht => by
    have : 0 < t := ht; positivity
  rw [Real.norm_of_nonneg (Real.rpow_pos_of_pos hx0 _).le]
  have hxp : x ^ (θ - 1) ≤ x ^ (-(1/2) + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx (by rw [hθ]; linarith)
  calc 2 * D * x ^ (θ - 1) * I = 2 * D * I * x ^ (θ - 1) := by ring
    _ ≤ 2 * D * I * x ^ (-(1/2) + ε) := mul_le_mul_of_nonneg_left hxp (by positivity)
