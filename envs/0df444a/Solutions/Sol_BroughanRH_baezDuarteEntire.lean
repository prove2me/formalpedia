-- Prove2me | solution 1 for BroughanRH.baezDuarteEntire
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T20:12:29.54199+00:00
-- url     : https://prove2.me/submissions/5103f45d-b275-4400-85db-23b2cf34e2f6
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


lemma g_bound_RH (θ : ℝ) (hθ : 1 / 2 < θ) (hθ1 : θ < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y : ℝ, 0 < y →
      |∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (moebius n : ℝ) / n| ≤ D * y ^ (θ - 1) := by
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
  obtain ⟨C, hC0', hC⟩ := mertens_bound θ hθ hM
  set D := C * (1 + 1 / (1 - θ)) with hD
  have hD0 : 0 ≤ D := by
    have : 0 < 1 - θ := by linarith
    rw [hD]; positivity
  refine ⟨2 * D, by positivity, fun y hy => ?_⟩
  rcases lt_or_ge y 1 with h | h
  · have : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr h
    simp only [this]
    simp only [Finset.Icc_eq_empty_of_lt, zero_lt_one, Finset.sum_empty, abs_zero]
    have := Real.rpow_pos_of_pos hy (θ - 1)
    positivity
  · set N := ⌊y⌋₊
    have hN1 : 1 ≤ N := Nat.one_le_floor_iff _ |>.mpr h
    have hgN : ∑ n ∈ Finset.Icc 1 N, (moebius n : ℝ) / n =
        ∑ k ∈ Finset.Icc 0 N, (k : ℝ)⁻¹ * (moebius k : ℝ) := by
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

end IntegralsAux

namespace EntireAux

open Complex

/-- Taylor coefficients -/
noncomputable def dc (f : ℂ → ℂ) (m : ℕ) : ℂ := iteratedDeriv m f 0 / (m.factorial : ℂ)

lemma taylor (f : ℂ → ℂ) (hf : Differentiable ℂ f) (z : ℂ) :
    HasSum (fun m => dc f m * z ^ m) (f z) := by
  have h := Complex.hasSum_taylorSeries_of_entire hf 0 z
  refine h.congr_fun fun m => ?_
  simp only [dc, sub_zero, smul_eq_mul]
  field_simp

lemma coef_summable (f : ℂ → ℂ) (hf : Differentiable ℂ f) (r : ℝ) (hr : 0 ≤ r) :
    Summable (fun m => ‖dc f m‖ * r ^ m) := by
  set R : ℝ := 2 * r + 1 with hR
  have hR0 : 0 < R := by positivity
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn hf.continuous.continuousOn
  have hcau : ∀ m, ‖iteratedDeriv m f 0‖ ≤ m.factorial * C / R ^ m := fun m =>
    norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m hR0 hf.diffContOnCl hC
  have hq : r / R < 1 := by rw [div_lt_one hR0]; linarith
  have hgeo : Summable (fun m : ℕ => C * (r / R) ^ m) :=
    (summable_geometric_of_lt_one (by positivity) hq).mul_left C
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hgeo
  simp only [dc, norm_div, Complex.norm_natCast]
  have hf' : (0 : ℝ) < m.factorial := by positivity
  rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ hf']
  calc ‖iteratedDeriv m f 0‖ * r ^ m ≤ (m.factorial * C / R ^ m) * r ^ m :=
        mul_le_mul_of_nonneg_right (hcau m) (by positivity)
    _ = _ := by field_simp

lemma dc_zero (f : ℂ → ℂ) (hf0 : f 0 = 0) : dc f 0 = 0 := by simp [dc, hf0]

/-- `f(u)/u = ∑ d_{k+1} u^k` -/
lemma taylor_div (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf0 : f 0 = 0) (z : ℂ) (hz : z ≠ 0) :
    HasSum (fun k : ℕ => dc f (k + 1) * z ^ k) (f z / z) := by
  have h := (hasSum_nat_add_iff' 1).mpr (taylor f hf z)
  simp only [Finset.range_one, Finset.sum_singleton, dc_zero f hf0, zero_mul, sub_zero] at h
  have := h.div_const z
  refine this.congr_fun fun k => ?_
  rw [pow_succ]; field_simp

lemma norm_div_le (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf0 : f 0 = 0) (x : ℝ) (hx : 0 ≤ x)
    (u : ℝ) (hu : 0 < u) (hux : u ≤ x) :
    ‖f u / u‖ ≤ ∑' k : ℕ, ‖dc f (k + 1)‖ * x ^ k := by
  have hs := (summable_nat_add_iff 1).mpr (coef_summable f hf x hx)
  have hs' : Summable (fun k : ℕ => ‖dc f (k + 1)‖ * x ^ k) := by
    have := hs.mul_left (1 / (x + 1))
    by_cases hx0 : x = 0
    · subst hx0
      exact summable_of_ne_finset_zero (s := {0}) fun k hk => by
        simp at hk; simp [hk]
    · refine (hs.div_const x).congr fun k => ?_
      rw [pow_succ]; field_simp
  refine (taylor_div f hf hf0 u (by exact_mod_cast hu.ne')).norm_le_of_bounded hs'.hasSum fun k => ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu.le hux k) (norm_nonneg _)

lemma shifted_summable (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ) (hx : 0 ≤ x) :
    Summable (fun k : ℕ => ‖dc f (k + 1)‖ * x ^ k) := by
  have hs := (summable_nat_add_iff 1).mpr (coef_summable f hf x hx)
  by_cases hx0 : x = 0
  · subst hx0
    exact summable_of_ne_finset_zero (s := {0}) fun k hk => by
      simp at hk; simp [hk]
  · refine (hs.div_const x).congr fun k => ?_
    rw [pow_succ]; field_simp

lemma phi_hasSum (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf0 : f 0 = 0) (y : ℝ) (hy : 0 < y) :
    HasSum (fun k : ℕ => dc f (k + 1) * (y : ℂ) ^ (k + 1) / ((k + 1 : ℕ) : ℂ))
      (∫ u in (0 : ℝ)..y, f u / u) := by
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := 0) (b := y) (F := fun (k : ℕ) (t : ℝ) => dc f (k + 1) * (t : ℂ) ^ k)
    (f := fun t : ℝ => f t / t)
    (fun k _ => ‖dc f (k + 1)‖ * y ^ k)
    (fun k => (Continuous.aestronglyMeasurable (by fun_prop)))
    (fun k => MeasureTheory.ae_of_all _ fun t ht => by
      rw [Set.uIoc_of_le hy.le] at ht
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1.le ht.2 k) (norm_nonneg _))
    (MeasureTheory.ae_of_all _ fun t _ => shifted_summable f hf y hy.le)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun t ht => by
      rw [Set.uIoc_of_le hy.le] at ht
      exact taylor_div f hf hf0 t (by exact_mod_cast ht.1.ne'))
  refine h.congr_fun fun k => ?_
  rw [intervalIntegral.integral_const_mul]
  have : (fun t : ℝ => (t : ℂ) ^ k) = fun t : ℝ => ((t ^ k : ℝ) : ℂ) := by
    funext t; push_cast; rfl
  rw [this, intervalIntegral.integral_ofReal, integral_pow]
  push_cast
  ring

open ArithmeticFunction in
lemma inv_zeta_nat_complex (m : ℕ) (hm : 2 ≤ m) :
    Summable (fun n : ℕ => (moebius n : ℂ) / (n : ℂ) ^ m) ∧
    (riemannZeta (m : ℂ))⁻¹ = ∑' n : ℕ, (moebius n : ℂ) / (n : ℂ) ^ m := by
  have hs : 1 < (m : ℂ).re := by simp; exact_mod_cast hm
  have hterm : LSeries.term (fun n => (moebius n : ℂ)) (m : ℂ) =
      fun n : ℕ => (moebius n : ℂ) / (n : ℂ) ^ m := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn.ne', Complex.cpow_natCast]
  have hsumC : LSeriesSummable (fun n => (moebius n : ℂ)) (m : ℂ) :=
    LSeriesSummable_moebius_iff.mpr hs
  rw [LSeriesSummable, hterm] at hsumC
  refine ⟨hsumC, ?_⟩
  have h1 := LSeries_zeta_mul_Lseries_moebius hs
  rw [LSeries_zeta_eq_riemannZeta hs, LSeries, hterm] at h1
  exact inv_eq_of_mul_eq_one_right h1

open ArithmeticFunction in
lemma S_hasSum (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf0 : f 0 = 0) (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℕ => ((moebius n : ℂ) / (n : ℂ)) * ∫ u in (0 : ℝ)..(x / n), f u / u)
      (∑' k : ℕ, (iteratedDeriv (k+1) f 0 / ((k+1).factorial : ℂ)) *
          (x : ℂ)^(k+1) / (((k+1 : ℕ) : ℂ) * riemannZeta ((k : ℂ)+2))) := by
  set a : ℕ → ℕ → ℂ := fun k n =>
    (dc f (k + 1) * (x : ℂ) ^ (k + 1) / ((k + 1 : ℕ) : ℂ)) * ((moebius n : ℂ) / (n : ℂ) ^ (k + 2))
    with ha
  have hterm : ∀ k : ℕ, (iteratedDeriv (k+1) f 0 / ((k+1).factorial : ℂ)) *
      (x : ℂ)^(k+1) / (((k+1 : ℕ) : ℂ) * riemannZeta ((k : ℂ)+2)) = ∑' n : ℕ, a k n := by
    intro k
    have hz : ((k : ℂ) + 2) = ((k + 2 : ℕ) : ℂ) := by push_cast; ring
    obtain ⟨_, h2⟩ := inv_zeta_nat_complex (k + 2) (by omega)
    rw [hz, ha, tsum_mul_left, ← h2]
    simp only [dc]
    field_simp
  have hbound : ∀ p : ℕ × ℕ, ‖Function.uncurry a p‖ ≤
      (‖dc f (p.1 + 1)‖ * x ^ (p.1 + 1)) * (1 / (p.2 : ℝ) ^ 2) := by
    rintro ⟨k, n⟩
    simp only [Function.uncurry, ha, norm_mul, norm_div, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hx.le, Complex.norm_natCast]
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hmu : ‖(moebius n : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
      have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (k + 2) := pow_le_pow_right₀ hn1 (by omega)
      have h1 : ‖dc f (k + 1)‖ * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ) ≤ ‖dc f (k + 1)‖ * x ^ (k + 1) :=
        div_le_self (by positivity) hk1
      have h2 : ‖(moebius n : ℂ)‖ / (n : ℝ) ^ (k + 2) ≤ 1 / (n : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [norm_nonneg (moebius n : ℂ)]
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hsum2 : Summable (fun p : ℕ × ℕ => (‖dc f (p.1 + 1)‖ * x ^ (p.1 + 1)) * (1 / (p.2 : ℝ) ^ 2)) := by
    refine Summable.mul_of_nonneg (f := fun k : ℕ => ‖dc f (k + 1)‖ * x ^ (k + 1))
      (g := fun n : ℕ => 1 / (n : ℝ) ^ 2) ?_ ?_ ?_ ?_
    · exact (summable_nat_add_iff 1).mpr (coef_summable f hf x hx.le)
    · exact Real.summable_one_div_nat_pow.mpr (by norm_num)
    · intro k; positivity
    · intro n; positivity
  have hsum : Summable (Function.uncurry a) := Summable.of_norm_bounded hsum2 hbound
  have hcomm := hsum.tsum_comm
  have hinner : ∀ n : ℕ, ∑' k : ℕ, a k n =
      ((moebius n : ℂ) / (n : ℂ)) * ∫ u in (0 : ℝ)..(x / n), f u / u := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha]
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      have hxn : 0 < x / n := by positivity
      rw [← (phi_hasSum f hf hf0 (x / n) hxn).tsum_eq, ← tsum_mul_left]
      refine tsum_congr fun k => ?_
      simp only [ha]
      push_cast
      rw [div_pow]
      field_simp
      ring
  have hcol : Summable (fun n : ℕ => ∑' k : ℕ, a k n) := hsum.prod_symm.prod
  rw [tsum_congr hterm, ← hcomm]
  simp_rw [← hinner]
  exact hcol.hasSum

open MeasureTheory ArithmeticFunction in
lemma S_integral (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf0 : f 0 = 0) (x : ℝ) (hx : 0 < x) :
    ∑' n : ℕ, ((moebius n : ℂ) / (n : ℂ)) * (∫ u in (0 : ℝ)..(x / n), f u / u) =
      ∫ u in Set.Ioi (0 : ℝ), (((∑ n ∈ Finset.Icc 1 ⌊x / u⌋₊, (moebius n : ℝ) / n : ℝ) : ℂ) * (f u / u)) := by
  set K := ∑' k : ℕ, ‖dc f (k + 1)‖ * x ^ k with hK
  set g : ℕ → ℝ → ℂ := fun n u => ((moebius n : ℂ) / (n : ℂ)) * (f u / u) with hg
  set F : ℕ → ℝ → ℂ := fun n => (Set.Ioc 0 (x / n)).indicator (g n) with hF
  have hsub : ∀ n : ℕ, Set.Ioc (0 : ℝ) (x / n) ⊆ Set.Ioi 0 := fun n => Set.Ioc_subset_Ioi_self
  have hres : ∀ n : ℕ, (volume.restrict (Set.Ioi (0 : ℝ))).restrict (Set.Ioc 0 (x / n)) =
      volume.restrict (Set.Ioc 0 (x / n)) := fun n => by
    rw [Measure.restrict_restrict measurableSet_Ioc, Set.inter_eq_left.mpr (hsub n)]
  have hgb : ∀ n : ℕ, ∀ u ∈ Set.Ioc (0 : ℝ) (x / n), ‖g n u‖ ≤ K / n := by
    intro n u hu
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at hu <;> linarith
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hux : u ≤ x := le_trans hu.2 (div_le_self hx.le hn1)
      have h1 := norm_div_le f hf hf0 x hx.le u hu.1 hux
      have hmu : ‖(moebius n : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
      have h2 : ‖(moebius n : ℂ) / (n : ℂ)‖ ≤ 1 / n := by
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_right hmu (by positivity)
      calc ‖g n u‖ = ‖(moebius n : ℂ) / (n : ℂ)‖ * ‖f u / u‖ := norm_mul _ _
        _ ≤ (1 / n) * K := mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
        _ = K / n := by ring
  have hgm : ∀ n : ℕ, AEStronglyMeasurable (g n) (volume.restrict (Set.Ioc 0 (x / n))) := by
    intro n
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine continuousOn_const.mul (ContinuousOn.div
      (hf.continuous.comp Complex.continuous_ofReal).continuousOn (by fun_prop) fun u hu => ?_)
    exact_mod_cast hu.1.ne'
  have hint : ∀ n : ℕ, Integrable (F n) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro n
    rw [hF, integrable_indicator_iff measurableSet_Ioc, IntegrableOn, hres]
    refine Integrable.of_bound (μ := volume.restrict (Set.Ioc 0 (x / n))) (hgm n) (K / n) ?_
    · rw [ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall (hgb n)
  have hval : ∀ n : ℕ, ∫ u in Set.Ioi (0 : ℝ), F n u =
      ((moebius n : ℂ) / (n : ℂ)) * ∫ u in (0 : ℝ)..(x / n), f u / u := by
    intro n
    rw [hF, integral_indicator measurableSet_Ioc, hres, intervalIntegral.integral_of_le (by positivity),
      ← integral_const_mul]
  have hnorm : ∀ n : ℕ, ∫ u in Set.Ioi (0 : ℝ), ‖F n u‖ ≤ K * x / (n : ℝ) ^ 2 := by
    intro n
    have e : (fun u => ‖F n u‖) = (Set.Ioc 0 (x / n)).indicator (fun u => ‖g n u‖) := by
      funext u; simp only [hF, norm_indicator_eq_indicator_norm]
    rw [e, integral_indicator measurableSet_Ioc, hres]
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc 0 (x / n))
      (f := fun u => ‖g n u‖) (C := K / n) measure_Ioc_lt_top (fun u hu => by
        rw [norm_norm]; exact hgb n u hu)
    rw [Real.volume_real_Ioc_of_le (by positivity), sub_zero] at h
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine h.trans (le_of_eq ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · field_simp
  have hK0 : 0 ≤ K := tsum_nonneg fun k => by positivity
  have hsumm : Summable (fun n : ℕ => ∫ u in Set.Ioi (0 : ℝ), ‖F n u‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun u => norm_nonneg _) hnorm ?_
    have := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left (K * x)
    refine this.congr fun n => ?_
    ring
  have hswap := integral_tsum_of_summable_integral_norm hint hsumm
  rw [← tsum_congr hval, hswap]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0 : ℝ) < u := hu
  simp only [hF]
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x / u⌋₊)]
  · push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' := Finset.mem_Icc.mp hn
    have hn1 : (0 : ℝ) < n := by exact_mod_cast hn'.1
    have hnx : (n : ℝ) ≤ x / u := (Nat.le_floor_iff (by positivity)).mp hn'.2
    rw [Set.indicator_of_mem]
    exact ⟨hu0, by rw [le_div_iff₀ hn1]; rw [le_div_iff₀ hu0] at hnx; linarith⟩
  · intro n hn
    rw [Set.indicator_of_notMem]
    intro hmem
    apply hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp at hmem <;> linarith
    · rw [Finset.mem_Icc]
      refine ⟨hpos, ?_⟩
      have hn1 : (0 : ℝ) < n := by exact_mod_cast hpos
      rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hu0]
      have := hmem.2
      rw [le_div_iff₀ hn1] at this
      linarith

end EntireAux

open IntegralsAux EntireAux ArithmeticFunction MeasureTheory

theorem solution :
    ∀ f : ℂ → ℂ, Differentiable ℂ f → f 0 = 0 →
      (∀ σ : ℝ, -(1/2) < σ → σ < 0 → MeasureTheory.IntegrableOn
        (fun t : ℝ => t^(-σ-1) * ‖f (t : ℂ)‖) (Set.Ioi 0)) →
      (∀ s : ℂ, -(1/2) < s.re → s.re < 0 →
        (∫ t in Set.Ioi (0 : ℝ), (t : ℂ)^(-s-1) * f (t : ℂ)) ≠ 0) →
      ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop
        (fun x : ℝ => ∑' k : ℕ, (iteratedDeriv (k+1) f 0 / ((k+1).factorial : ℂ)) *
          (x : ℂ)^(k+1) / (((k+1 : ℕ) : ℂ) * riemannZeta ((k : ℂ)+2)))
        (fun x : ℝ => x^(-(1/2) + ε)) := by
  intro f hf hf0 hint _ ε hε
  set δ := min ε (1/2) with hδ
  have hδ0 : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ ≤ 1/2 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  set θ := 1 / 2 + δ / 2 with hθ
  have hθ1 : θ < 1 := by rw [hθ]; linarith
  obtain ⟨D, hD0, hgb⟩ := g_bound_RH θ (by rw [hθ]; linarith) hθ1
  have hI : IntegrableOn (fun t : ℝ => t ^ (-θ) * ‖f (t : ℂ)‖) (Set.Ioi 0) := by
    have h1 := hint (θ - 1) (by rw [hθ]; linarith) (by linarith)
    refine h1.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only; congr 2; ring
  set I := ∫ t in Set.Ioi (0 : ℝ), t ^ (-θ) * ‖f (t : ℂ)‖ with hIdef
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi fun t ht => by
    have : 0 < t := ht; positivity
  refine Asymptotics.IsBigO.of_bound (D * I) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  rw [← (S_hasSum f hf hf0 x hx0).tsum_eq, S_integral f hf hf0 x hx0]
  have hb : ∀ᵐ u ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖(((∑ n ∈ Finset.Icc 1 ⌊x / u⌋₊, (moebius n : ℝ) / n : ℝ) : ℂ) * (f u / u))‖ ≤
      (D * x ^ (θ - 1)) * (u ^ (-θ) * ‖f (u : ℂ)‖) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun u hu => ?_
    have hu0 : 0 < u := hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div, Complex.norm_real,
      Real.norm_of_nonneg hu0.le]
    have h := hgb (x / u) (by positivity)
    have e : (x / u) ^ (θ - 1) / u = x ^ (θ - 1) * u ^ (-θ) := by
      rw [Real.div_rpow hx0.le hu0.le, div_div, ← Real.rpow_add_one hu0.ne', Real.rpow_neg hu0.le]
      ring_nf
    calc |∑ n ∈ Finset.Icc 1 ⌊x / u⌋₊, (moebius n : ℝ) / n| * (‖f (u : ℂ)‖ / u)
        ≤ (D * (x / u) ^ (θ - 1)) * (‖f (u : ℂ)‖ / u) :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = D * ((x / u) ^ (θ - 1) / u) * ‖f (u : ℂ)‖ := by ring
      _ = _ := by rw [e]; ring
  have := norm_integral_le_of_norm_le (hI.const_mul (D * x ^ (θ - 1))) hb
  rw [integral_const_mul] at this
  refine this.trans ?_
  rw [Real.norm_of_nonneg (Real.rpow_pos_of_pos hx0 _).le]
  have hxp : x ^ (θ - 1) ≤ x ^ (-(1/2) + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx (by rw [hθ]; linarith)
  calc D * x ^ (θ - 1) * I = D * I * x ^ (θ - 1) := by ring
    _ ≤ D * I * x ^ (-(1/2) + ε) := mul_le_mul_of_nonneg_left hxp (by positivity)
