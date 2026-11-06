-- Prove2me | solution 1 for ChoicePAC.MidPoint.lemma_C4_window_mgf
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T16:09:35.183301+00:00
-- url     : https://prove2.me/submissions/cabf0c00-d7f5-4839-9a63-176258b18887

import Mathlib
import Definitions.Def_ChoicePAC_MidPoint_Model
import Definitions.Def_ChoicePAC_MidPoint_OPAC

open ChoicePAC.MidPoint MeasureTheory

namespace C4aux

variable {NT n m : ℕ} (I : Instance NT n m)

lemma exp_tsum (x : ℝ) : Real.exp x = ∑' N : ℕ, x ^ N / (N.factorial : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- The one-arrival multiplicative factor of the exponential moment. -/
noncomputable def g (p : Fin n → ℝ) (r : ℝ) (i : Fin m) : ℝ :=
  ∑ q, (I.lam q / I.Λ) * ((1 - ∑ j ∈ I.S q, p j) +
    ∑ j ∈ I.S q, p j * ∫ a, Real.exp (r * a i) ∂(I.D j))

lemma step (p : Fin n → ℝ) (r : ℝ) (i : Fin m) (c : ℝ) :
    I.opacStep p (fun acc => c * Real.exp (r * acc i)) =
      fun acc => (c * g I p r i) * Real.exp (r * acc i) := by
  funext acc
  unfold Instance.opacStep g
  set X := c * Real.exp (r * acc i) with hX
  have hint : ∀ j, ∫ a, c * Real.exp (r * (acc + a) i) ∂(I.D j) =
      X * ∫ a, Real.exp (r * a i) ∂(I.D j) := by
    intro j
    rw [← integral_const_mul]
    congr 1; funext a; simp only [Pi.add_apply]; rw [mul_add, Real.exp_add]; ring
  simp_rw [hint]
  rw [show (c * ∑ q, I.lam q / I.Λ * ((1 - ∑ j ∈ I.S q, p j) +
      ∑ j ∈ I.S q, p j * ∫ a, Real.exp (r * a i) ∂(I.D j))) * Real.exp (r * acc i) =
      X * ∑ q, I.lam q / I.Λ * ((1 - ∑ j ∈ I.S q, p j) +
      ∑ j ∈ I.S q, p j * ∫ a, Real.exp (r * a i) ∂(I.D j)) by rw [hX]; ring]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  have : ∑ j ∈ I.S q, p j * (X * ∫ a, Real.exp (r * a i) ∂(I.D j)) =
      X * ∑ j ∈ I.S q, p j * ∫ a, Real.exp (r * a i) ∂(I.D j) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  rw [this]; ring

lemma iter (p : Fin n → ℝ) (r : ℝ) (i : Fin m) (c : ℝ) (N : ℕ) :
    (I.opacStep p)^[N] (fun acc => c * Real.exp (r * acc i)) =
      fun acc => (c * g I p r i ^ N) * Real.exp (r * acc i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih, step]
    funext acc; ring

lemma expect (k : ℕ) (ℓ : ℝ) (p : Fin n → ℝ) (r : ℝ) (i : Fin m) (c : ℝ)
    (hμ : 0 ≤ (k : ℝ) * I.Λ * ℓ) :
    I.opacExpect k ℓ p (fun ζ => c * Real.exp (r * ζ i)) =
      c * Real.exp ((k : ℝ) * I.Λ * ℓ * (g I p r i - 1)) := by
  unfold Instance.opacExpect Instance.poissonWeight
  simp_rw [iter]
  rw [max_eq_left hμ]
  set μ := (k : ℝ) * I.Λ * ℓ
  have : ∀ N : ℕ, Real.exp (-μ) * μ ^ N / (N.factorial : ℝ) *
      (c * g I p r i ^ N * Real.exp (r * (0 : Fin m → ℝ) i)) =
      (Real.exp (-μ) * c) * ((μ * g I p r i) ^ N / (N.factorial : ℝ)) := by
    intro N; simp only [Pi.zero_apply, mul_zero, Real.exp_zero, mul_one]; rw [mul_pow]; ring
  simp_rw [this]
  rw [tsum_mul_left, ← exp_tsum]
  have : Real.exp (μ * (g I p r i - 1)) = Real.exp (-μ) * Real.exp (μ * g I p r i) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]; ring

end C4aux

theorem solution {NT n m : ℕ} (I : Instance NT n m) (hI : I.IsValid) :
    ∃ φ : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ ℓ : ℝ, 0 ≤ ℓ → ∀ p : Fin n → ℝ, I.AdmissibleProbs p →
      ∀ r : ℝ, |r * I.ξmax| ≤ 1 → ∀ i : Fin m,
        I.opacExpect k ℓ p (fun ζ => Real.exp (r * (ζ i - I.opacMean k ℓ p i))) ≤
            ∏ q, Real.exp ((k : ℝ) * I.lam q * ℓ * r ^ 2 *
              ∑ j ∈ I.S q, p j * ∫ a, (a i) ^ 2 ∂(I.D j)) ∧
          ∏ q, Real.exp ((k : ℝ) * I.lam q * ℓ * r ^ 2 *
              ∑ j ∈ I.S q, p j * ∫ a, (a i) ^ 2 ∂(I.D j)) ≤
            Real.exp ((k : ℝ) * φ * ℓ * r ^ 2) := by
  obtain ⟨hlam, _, hprob, hsupp, _⟩ := hI
  refine ⟨I.Λ * ∑ j, I.ξ j ^ 2, ?_⟩
  intro k hk ℓ hℓ p hp r hr i
  have hΛ : 0 ≤ I.Λ := Finset.sum_nonneg (fun q _ => hlam q)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  -- facts about the consumption laws
  have hxi0 : ∀ j, 0 ≤ I.ξ j := by
    intro j
    haveI := hprob j
    obtain ⟨a, ha⟩ := (hsupp j).exists
    exact le_trans (ha i).1 (ha i).2
  have hximax : ∀ j, I.ξ j ≤ I.ξmax := fun j =>
    le_ciSup (Set.finite_range _).bddAbove j
  have hrx : ∀ j, |r| * I.ξ j ≤ 1 := by
    intro j
    calc |r| * I.ξ j ≤ |r| * I.ξmax := mul_le_mul_of_nonneg_left (hximax j) (abs_nonneg r)
      _ ≤ |r| * |I.ξmax| := mul_le_mul_of_nonneg_left (le_abs_self _) (abs_nonneg r)
      _ = |r * I.ξmax| := (abs_mul r _).symm
      _ ≤ 1 := hr
  have hmeasi : Measurable (fun a : Fin m → ℝ => a i) := measurable_pi_apply i
  have hInt1 : ∀ j, Integrable (fun a : Fin m → ℝ => a i) (I.D j) := by
    intro j; haveI := hprob j
    refine Integrable.of_bound hmeasi.aestronglyMeasurable (I.ξ j) ?_
    filter_upwards [hsupp j] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (ha i).1]; exact (ha i).2
  have hInt2 : ∀ j, Integrable (fun a : Fin m → ℝ => (a i) ^ 2) (I.D j) := by
    intro j; haveI := hprob j
    refine Integrable.of_bound (hmeasi.pow_const 2).aestronglyMeasurable (I.ξ j ^ 2) ?_
    filter_upwards [hsupp j] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (ha i).1 (ha i).2 2
  have hIntE : ∀ j, Integrable (fun a : Fin m → ℝ => Real.exp (r * a i)) (I.D j) := by
    intro j; haveI := hprob j
    refine Integrable.of_bound (Real.measurable_exp.comp (hmeasi.const_mul r)).aestronglyMeasurable
      (Real.exp 1) ?_
    filter_upwards [hsupp j] with a ha
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc r * a i ≤ |r * a i| := le_abs_self _
      _ = |r| * a i := by rw [abs_mul, abs_of_nonneg (ha i).1]
      _ ≤ |r| * I.ξ j := mul_le_mul_of_nonneg_left (ha i).2 (abs_nonneg r)
      _ ≤ 1 := hrx j
  -- the one-offer moment bound
  have hmgf : ∀ j, ∫ a, Real.exp (r * a i) ∂(I.D j) - 1 - r * I.Abar i j ≤
      r ^ 2 * ∫ a, (a i) ^ 2 ∂(I.D j) := by
    intro j; haveI := hprob j
    have hle : ∫ a, Real.exp (r * a i) ∂(I.D j) ≤
        ∫ a, (1 + r * a i + r ^ 2 * (a i) ^ 2) ∂(I.D j) := by
      apply integral_mono_ae (hIntE j)
      · exact ((integrable_const 1).add ((hInt1 j).const_mul r)).add ((hInt2 j).const_mul _)
      · filter_upwards [hsupp j] with a ha
        have hb : |r * a i| ≤ 1 := by
          rw [abs_mul, abs_of_nonneg (ha i).1]
          exact le_trans (mul_le_mul_of_nonneg_left (ha i).2 (abs_nonneg r)) (hrx j)
        have := Real.abs_exp_sub_one_sub_id_le hb
        have := (abs_le.mp this).2
        show Real.exp (r * a i) ≤ 1 + r * a i + r ^ 2 * a i ^ 2
        nlinarith
    have i1 : Integrable (fun a : Fin m → ℝ => 1 + r * a i) (I.D j) :=
      (integrable_const 1).add ((hInt1 j).const_mul r)
    have i2 : Integrable (fun a : Fin m → ℝ => r ^ 2 * a i ^ 2) (I.D j) :=
      (hInt2 j).const_mul _
    have i3 : Integrable (fun a : Fin m → ℝ => r * a i) (I.D j) := (hInt1 j).const_mul r
    rw [integral_add i1 i2, integral_add (integrable_const 1) i3,
      integral_const_mul, integral_const_mul] at hle
    simp only [integral_const, probReal_univ, one_smul, smul_eq_mul, one_mul] at hle
    have : I.Abar i j = ∫ a, a i ∂(I.D j) := rfl
    rw [this]; linarith
  have hsecond : ∀ j, ∫ a, (a i) ^ 2 ∂(I.D j) ≤ I.ξ j ^ 2 := by
    intro j; haveI := hprob j
    have : ∫ a, (a i) ^ 2 ∂(I.D j) ≤ ∫ _a, I.ξ j ^ 2 ∂(I.D j) := by
      apply integral_mono_ae (hInt2 j) (integrable_const _)
      filter_upwards [hsupp j] with a ha
      exact pow_le_pow_left₀ (ha i).1 (ha i).2 2
    simpa using this
  have hsecond0 : ∀ j, 0 ≤ ∫ a, (a i) ^ 2 ∂(I.D j) := fun j =>
    integral_nonneg (fun a => sq_nonneg _)
  -- the exponent identities
  set M : Fin n → ℝ := fun j => ∫ a, Real.exp (r * a i) ∂(I.D j) with hM
  have hμg : (k : ℝ) * I.Λ * ℓ * (C4aux.g I p r i - 1) =
      ∑ q, ∑ j ∈ I.S q, (k : ℝ) * I.lam q * ℓ * p j * (M j - 1) := by
    by_cases hΛ0 : I.Λ = 0
    · have hl0 : ∀ q, I.lam q = 0 := by
        intro q
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => hlam q)).mp hΛ0 q (Finset.mem_univ q)
      simp [hΛ0, hl0]
    · have hg : (k : ℝ) * I.Λ * ℓ * C4aux.g I p r i = ∑ q, (k : ℝ) * I.lam q * ℓ *
          ((1 - ∑ j ∈ I.S q, p j) + ∑ j ∈ I.S q, p j * M j) := by
        unfold C4aux.g
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro q _
        simp only [hM]
        field_simp
      have hl : (k : ℝ) * I.Λ * ℓ = ∑ q, (k : ℝ) * I.lam q * ℓ := by
        simp only [Instance.Λ]; rw [Finset.mul_sum, Finset.sum_mul]
      rw [mul_sub, mul_one, hg, hl, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q _
      have e1 : ∑ j ∈ I.S q, (k : ℝ) * I.lam q * ℓ * p j * (M j - 1) =
          (k : ℝ) * I.lam q * ℓ * (∑ j ∈ I.S q, p j * M j - ∑ j ∈ I.S q, p j) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring
      rw [e1]; ring
  have hmean : I.opacMean k ℓ p i =
      ∑ q, ∑ j ∈ I.S q, (k : ℝ) * I.lam q * ℓ * p j * I.Abar i j := by
    unfold Instance.opacMean
    rw [← Finset.sum_fiberwise Finset.univ I.typ]
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [hj]
  have hfun : (fun ζ : Fin m → ℝ => Real.exp (r * (ζ i - I.opacMean k ℓ p i))) =
      fun ζ => Real.exp (-(r * I.opacMean k ℓ p i)) * Real.exp (r * ζ i) := by
    funext ζ; rw [← Real.exp_add]; ring_nf
  have hμ : 0 ≤ (k : ℝ) * I.Λ * ℓ := by positivity
  refine ⟨?_, ?_⟩
  · rw [hfun, C4aux.expect I k ℓ p r i _ hμ, ← Real.exp_add, ← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    rw [hμg, hmean]
    have hL : -(r * ∑ q, ∑ j ∈ I.S q, (k : ℝ) * I.lam q * ℓ * p j * I.Abar i j) +
        ∑ q, ∑ j ∈ I.S q, (k : ℝ) * I.lam q * ℓ * p j * (M j - 1) =
        ∑ q, ∑ j ∈ I.S q, (k : ℝ) * I.lam q * ℓ * p j * (M j - 1 - r * I.Abar i j) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro q _
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hL]
    apply Finset.sum_le_sum
    intro q _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hc : 0 ≤ (k : ℝ) * I.lam q * ℓ * p j :=
      mul_nonneg (mul_nonneg (mul_nonneg hk0 (hlam q)) hℓ) (hp.1 j)
    have key := mul_le_mul_of_nonneg_left (hmgf j) hc
    have e : (k : ℝ) * I.lam q * ℓ * r ^ 2 * (p j * ∫ a, (a i) ^ 2 ∂(I.D j)) =
        (k : ℝ) * I.lam q * ℓ * p j * (r ^ 2 * ∫ a, (a i) ^ 2 ∂(I.D j)) := by ring
    rw [e]; exact key
  · rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    set Ξ := ∑ j, I.ξ j ^ 2
    have hΞ : ∀ j, ∫ a, (a i) ^ 2 ∂(I.D j) ≤ Ξ := fun j =>
      le_trans (hsecond j) (Finset.single_le_sum (f := fun j => I.ξ j ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ j))
    have hΞ0 : 0 ≤ Ξ := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hq : ∀ q, ∑ j ∈ I.S q, p j * ∫ a, (a i) ^ 2 ∂(I.D j) ≤ Ξ := by
      intro q
      calc ∑ j ∈ I.S q, p j * ∫ a, (a i) ^ 2 ∂(I.D j) ≤ ∑ j ∈ I.S q, p j * Ξ :=
            Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hΞ j) (hp.1 j))
        _ = (∑ j ∈ I.S q, p j) * Ξ := by rw [Finset.sum_mul]
        _ ≤ 1 * Ξ := mul_le_mul_of_nonneg_right (hp.2 q) hΞ0
        _ = Ξ := one_mul _
    calc ∑ q, (k : ℝ) * I.lam q * ℓ * r ^ 2 * ∑ j ∈ I.S q, p j * ∫ a, (a i) ^ 2 ∂(I.D j)
        ≤ ∑ q, (k : ℝ) * I.lam q * ℓ * r ^ 2 * Ξ := by
          apply Finset.sum_le_sum; intro q _
          apply mul_le_mul_of_nonneg_left (hq q)
          exact mul_nonneg (mul_nonneg (mul_nonneg hk0 (hlam q)) hℓ) (sq_nonneg r)
      _ = (k : ℝ) * (I.Λ * Ξ) * ℓ * r ^ 2 := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
          simp only [Instance.Λ]; ring
