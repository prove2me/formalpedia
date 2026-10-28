-- Prove2me | solution 1 for DataDrivenNV.LRS.theoremEC1_bernstein
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:27:32.568709+00:00
-- url     : https://prove2.me/submissions/1a25e0f3-b028-4420-a729-ad11eb109a88

import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory


namespace DataDrivenNV.LRS.BernsteinProof

lemma two_three_pow_le_factorial (k : ℕ) : 2 * 3 ^ k ≤ (k + 2).factorial := by
  induction k with
  | zero => simp [Nat.factorial]
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, Nat.factorial_succ, pow_succ]
    nlinarith

lemma exp_le_quad_pos {u : ℝ} (h0 : 0 ≤ u) (h3 : u < 3) :
    Real.exp u ≤ 1 + u + u ^ 2 / (2 * (1 - u / 3)) := by
  have hs := Real.summable_pow_div_factorial u
  have hexp : Real.exp u = ∑' k, u ^ k / (k.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hsplit := hs.sum_add_tsum_nat_add 2
  have hr : 0 ≤ u / 3 := by positivity
  have hr1 : u / 3 < 1 := by linarith
  have hgs : Summable fun k : ℕ => u ^ 2 / 2 * (u / 3) ^ k :=
    (summable_geometric_of_lt_one hr hr1).mul_left _
  have hterm : ∀ k : ℕ, u ^ (k + 2) / ((k + 2).factorial : ℝ) ≤ u ^ 2 / 2 * (u / 3) ^ k := by
    intro k
    have hf : (2 * 3 ^ k : ℝ) ≤ ((k + 2).factorial : ℝ) := by
      exact_mod_cast two_three_pow_le_factorial k
    have hpos : (0 : ℝ) < 2 * 3 ^ k := by positivity
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((k + 2).factorial : ℝ))]
    calc u ^ (k + 2) = u ^ 2 / 2 * (u / 3) ^ k * (2 * 3 ^ k) := by
          rw [div_pow]; field_simp; ring
      _ ≤ u ^ 2 / 2 * (u / 3) ^ k * ((k + 2).factorial : ℝ) :=
          mul_le_mul_of_nonneg_left hf (by positivity)
  have hle := (hs.comp_injective (add_left_injective 2)).tsum_le_tsum hterm hgs
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr1] at hle
  rw [hexp, ← hsplit]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, zero_add, pow_one, Nat.factorial_one]
  have e : u ^ 2 / 2 * (1 - u / 3)⁻¹ = u ^ 2 / (2 * (1 - u / 3)) := by
    field_simp
  have : ∑' k : ℕ, u ^ (k + 2) / ((k + 2).factorial : ℝ) ≤ u ^ 2 / (2 * (1 - u / 3)) := by
    rw [← e]; exact hle
  linarith

lemma exp_le_quad_neg {x : ℝ} (hx : x ≤ 0) : Real.exp x ≤ 1 + x + x ^ 2 / 2 := by
  have hanti : AntitoneOn (fun y => 1 + y + y ^ 2 / 2 - Real.exp y) (Set.Iic 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
    · exact (by fun_prop : Continuous fun y : ℝ => 1 + y + y ^ 2 / 2 - Real.exp y).continuousOn
    · exact (by fun_prop : Differentiable ℝ fun y : ℝ => 1 + y + y ^ 2 / 2 - Real.exp y)
        |>.differentiableOn
    · intro y hy
      rw [interior_Iic] at hy
      have hd : HasDerivAt (fun y : ℝ => 1 + y + y ^ 2 / 2 - Real.exp y)
          (1 + y - Real.exp y) y := by
        have := ((((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).add
          ((hasDerivAt_pow 2 y).div_const 2)).sub (Real.hasDerivAt_exp y))
        refine this.congr_deriv ?_
        simp only [Nat.cast_ofNat, id]
        ring
      rw [hd.deriv]
      linarith [Real.add_one_le_exp y]
  have := hanti hx (Set.mem_Iic.mpr le_rfl) hx
  simp at this
  linarith

lemma exp_le_quad {x c : ℝ} (hc0 : 0 ≤ c) (hc3 : c < 3) (hx : x ≤ c) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - c / 3)) := by
  have hden : 0 < 2 * (1 - c / 3) := by linarith
  rcases le_or_gt x 0 with hneg | hpos
  · have h1 := exp_le_quad_neg hneg
    have h2 : x ^ 2 / 2 ≤ x ^ 2 / (2 * (1 - c / 3)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg x) hden
      linarith
    linarith
  · have h1 := exp_le_quad_pos hpos.le (by linarith)
    have h2 : x ^ 2 / (2 * (1 - x / 3)) ≤ x ^ 2 / (2 * (1 - c / 3)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg x) hden
      linarith
    linarith


lemma mgf_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B σ : ℝ) (X : Ω → ℝ) (hm : Measurable X) (hmean : ∫ ω, X ω ∂P = 0)
    (hbound : ∀ᵐ ω ∂P, |X ω| ≤ B) (hvar : ∫ ω, (X ω) ^ 2 ∂P ≤ σ ^ 2)
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl3 : lam * B < 3) :
    mgf X P lam ≤ Real.exp (lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3))) := by
  have hB0 : 0 ≤ B := by
    obtain ⟨ω, hω⟩ := hbound.exists
    exact (abs_nonneg _).trans hω
  have hc0 : 0 ≤ lam * B := mul_nonneg hl0 hB0
  have hden : 0 < 2 * (1 - lam * B / 3) := by linarith
  have hXint : Integrable X P :=
    Integrable.of_bound hm.aestronglyMeasurable B (by
      filter_upwards [hbound] with ω hω; rwa [Real.norm_eq_abs])
  have hX2int : Integrable (fun ω => (X ω) ^ 2) P :=
    Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (B ^ 2) (by
      filter_upwards [hbound] with ω hω
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hω 2)
  have hEint : Integrable (fun ω => Real.exp (lam * X ω)) P :=
    Integrable.of_bound (by fun_prop) (Real.exp (lam * B)) (by
      filter_upwards [hbound] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hω) hl0)
  set K := 1 / (2 * (1 - lam * B / 3)) with hK
  have hpt : ∀ᵐ ω ∂P, Real.exp (lam * X ω) ≤ 1 + lam * X ω + K * lam ^ 2 * (X ω) ^ 2 := by
    filter_upwards [hbound] with ω hω
    have hx : lam * X ω ≤ lam * B := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hω) hl0
    have := exp_le_quad hc0 hl3 hx
    rw [hK]
    calc Real.exp (lam * X ω) ≤ 1 + lam * X ω + (lam * X ω) ^ 2 / (2 * (1 - lam * B / 3)) := this
      _ = _ := by field_simp
  have hA : Integrable (fun ω => 1 + lam * X ω) P := (integrable_const 1).add (hXint.const_mul lam)
  have hB2 : Integrable (fun ω => K * lam ^ 2 * (X ω) ^ 2) P := hX2int.const_mul (K * lam ^ 2)
  have hint2 : Integrable (fun ω => 1 + lam * X ω + K * lam ^ 2 * (X ω) ^ 2) P := hA.add hB2
  have hmono := integral_mono_ae hEint hint2 hpt
  have hL : Integrable (fun ω => lam * X ω) P := hXint.const_mul lam
  rw [integral_add hA hB2, integral_add (integrable_const 1) hL, integral_const_mul,
    integral_const_mul, hmean] at hmono
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero] at hmono
  have hK0 : 0 ≤ K * lam ^ 2 := by rw [hK]; positivity
  have h2 : 1 + K * lam ^ 2 * ∫ ω, (X ω) ^ 2 ∂P ≤ 1 + lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3)) := by
    have := mul_le_mul_of_nonneg_left hvar hK0
    rw [hK] at this ⊢
    have e : 1 / (2 * (1 - lam * B / 3)) * lam ^ 2 * σ ^ 2 =
        lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3)) := by field_simp
    linarith
  unfold mgf
  calc ∫ ω, Real.exp (lam * X ω) ∂P ≤ 1 + K * lam ^ 2 * ∫ ω, (X ω) ^ 2 ∂P := hmono
    _ ≤ 1 + lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3)) := h2
    _ ≤ Real.exp (lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3))) := by
        linarith [Real.add_one_le_exp (lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3)))]

lemma bernstein_positive_variance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B σ : ℝ) (hB : 0 ≤ B) (hσ : 0 < σ ^ 2)
    (n : ℕ) (hn : 0 < n) (ξ : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hmean : ∀ i, ∫ ω, ξ i ω ∂P = 0) (hbound : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| ≤ B)
    (hvar : ∀ i, ∫ ω, (ξ i ω) ^ 2 ∂P ≤ σ ^ 2) (t : ℝ) (ht : 0 < t) :
    P.real {ω | t ≤ (1 / (n : ℝ)) * ∑ i, ξ i ω} ≤
      Real.exp (-((n : ℝ) * t ^ 2) / (2 * σ ^ 2 + 2 * t * B / 3)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set T := (n : ℝ) * t with hT
  have hTpos : 0 < T := mul_pos hnR ht
  set D := n * σ ^ 2 + B * T / 3 with hD
  have hDpos : 0 < D := add_pos_of_pos_of_nonneg (mul_pos hnR hσ) (by positivity)
  set lam := T / D with hlam
  have hl0 : 0 ≤ lam := by positivity
  have hl3 : lam * B < 3 := by
    rw [hlam, div_mul_eq_mul_div, div_lt_iff₀ hDpos, hD]
    nlinarith [mul_pos hnR hσ]
  have hset : {ω | t ≤ (1 / (n : ℝ)) * ∑ i, ξ i ω} =
      {ω | T ≤ (∑ i, ξ i) ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.sum_apply]
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hnR, hT, mul_comm t]
  rw [hset]
  have hSm : Measurable (∑ i, ξ i) := by
    rw [Finset.sum_fn]
    exact Finset.measurable_sum _ fun i _ => hmeas i
  have hSint : Integrable (fun ω => Real.exp (lam * (∑ i, ξ i) ω)) P := by
    refine Integrable.of_bound (by fun_prop) (Real.exp (lam * (n * B))) ?_
    have hall : ∀ᵐ ω ∂P, ∀ i, |ξ i ω| ≤ B := ae_all_iff.mpr hbound
    filter_upwards [hall] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    apply mul_le_mul_of_nonneg_left _ hl0
    simp only [Finset.sum_apply]
    calc ∑ i, ξ i ω ≤ ∑ _i : Fin n, B :=
          Finset.sum_le_sum fun i _ => le_trans (le_abs_self _) (hω i)
      _ = n * B := by simp
  have hch := measure_ge_le_exp_mul_mgf (X := ∑ i, ξ i) (μ := P) T hl0 hSint
  rw [hindep.mgf_sum hmeas Finset.univ] at hch
  have hprod : ∏ i ∈ Finset.univ, mgf (ξ i) P lam ≤
      Real.exp (lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3))) ^ n := by
    have := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => mgf (ξ i) P lam)
      (g := fun _ => Real.exp (lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3))))
      (fun i _ => mgf_nonneg) fun i _ =>
      mgf_bound P B σ (ξ i) (hmeas i) (hmean i) (hbound i) (hvar i) lam hl0 hl3
    rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  refine hch.trans ((mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le).trans ?_)
  rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
  have hD0 : D ≠ 0 := hDpos.ne'
  have h1 : 1 - lam * B / 3 = n * σ ^ 2 / D := by
    rw [hlam, eq_div_iff hD0]
    field_simp
    rw [hD]
    ring
  rw [h1]
  have hkey : -lam * T + n * (lam ^ 2 * σ ^ 2 / (2 * (n * σ ^ 2 / D))) =
      -(T ^ 2 / (2 * D)) := by
    rw [hlam]
    have hσ0 : σ ≠ 0 := by
      intro h
      simpa [h] using hσ
    have : (n : ℝ) * σ ^ 2 ≠ 0 := (mul_pos hnR hσ).ne'
    field_simp [hσ0]
    ring
  rw [hkey]
  have heq : -(T ^ 2 / (2 * D)) =
      -((n : ℝ) * t ^ 2) / (2 * σ ^ 2 + 2 * t * B / 3) := by
    rw [hD, hT]
    have hden : 2 * σ ^ 2 + 2 * t * B / 3 ≠ 0 := by positivity
    field_simp
    <;> ring
  exact heq.le

end DataDrivenNV.LRS.BernsteinProof

theorem solution (ν : Measure ℝ) [IsProbabilityMeasure ν] (N : ℕ) (hN : 1 ≤ N)
    (c σ : ℝ) (hc : ∀ᵐ x ∂ν, |x| ≤ c) (hcent : ∀ᵐ x ∂ν, |x - ∫ y, y ∂ν| ≤ c)
    (hvar : ∫ x, (x - ∫ y, y ∂ν) ^ 2 ∂ν = σ ^ 2) (t : ℝ) (ht : 0 < t) :
    (Measure.pi fun _ : Fin N => ν)
        {x : Fin N → ℝ | t ≤ (1 / (N : ℝ)) * ∑ i, x i - ∫ y, y ∂ν} ≤
      ENNReal.ofReal (Real.exp (-((N : ℝ) * t ^ 2) / (2 * σ ^ 2 + 2 * t * c / 3))) := by
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hc0 : 0 ≤ c := by
    obtain ⟨x, hx⟩ := hc.exists
    exact (abs_nonneg x).trans hx
  let m : ℝ := ∫ y, y ∂ν
  let ξ : Fin N → (Fin N → ℝ) → ℝ := fun i x => x i - m
  let P : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => ν
  have hξm : ∀ i, Measurable (ξ i) := by
    intro i
    change Measurable (fun x : Fin N → ℝ => x i - m)
    exact (measurable_pi_apply i).sub measurable_const
  have hξb : ∀ i, ∀ᵐ x ∂P, |ξ i x| ≤ c := fun i =>
    (measurePreserving_eval (fun _ : Fin N => ν) i).quasiMeasurePreserving.ae hcent
  have hxint : Integrable (fun x : ℝ => x) ν :=
    Integrable.of_bound measurable_id.aestronglyMeasurable c (by
      filter_upwards [hc] with x hx
      simpa only [Real.norm_eq_abs] using hx)
  have hcenterint : Integrable (fun x : ℝ => x - m) ν := hxint.sub (integrable_const m)
  have hξmean : ∀ i, ∫ x, ξ i x ∂P = 0 := by
    intro i
    dsimp [ξ, P]
    rw [integral_comp_eval (μ := fun _ : Fin N => ν) (i := i) hcenterint.aestronglyMeasurable,
      integral_sub hxint (integrable_const m)]
    simp [m]
  have hξvar : ∀ i, ∫ x, (ξ i x) ^ 2 ∂P = σ ^ 2 := by
    intro i
    dsimp [ξ, P]
    rw [integral_comp_eval (μ := fun _ : Fin N => ν) (i := i)
      (f := fun x : ℝ => (x - m) ^ 2) (by fun_prop)]
    exact hvar
  have hset : {x : Fin N → ℝ | t ≤ (1 / (N : ℝ)) * ∑ i, x i - ∫ y, y ∂ν} =
      {x | t ≤ (1 / (N : ℝ)) * ∑ i, ξ i x} := by
    ext x
    dsimp [ξ, m]
    congr 1
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  change P _ ≤ _
  rw [hset]
  by_cases hσ : σ ^ 2 = 0
  · have hξzero : ∀ i, ∀ᵐ x ∂P, ξ i x = 0 := by
      intro i
      have hint : Integrable (fun x => (ξ i x) ^ 2) P :=
        Integrable.of_bound ((hξm i).pow_const 2).aestronglyMeasurable (c ^ 2) (by
          filter_upwards [hξb i] with x hx
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) hx 2)
      have hz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (ξ i x)) hint).mp
        ((hξvar i).trans hσ)
      filter_upwards [hz] with x hx
      exact eq_zero_of_pow_eq_zero hx
    have hall : ∀ᵐ x ∂P, ∀ i, ξ i x = 0 := ae_all_iff.mpr hξzero
    have hnull : P {x | t ≤ (1 / (N : ℝ)) * ∑ i, ξ i x} = 0 := by
      have hnmem : ∀ᵐ x ∂P, ¬t ≤ (1 / (N : ℝ)) * ∑ i, ξ i x := by
        filter_upwards [hall] with x hx
        simp only [hx, Finset.sum_const_zero, mul_zero]
        exact not_le_of_gt ht
      simpa only [ae_iff, not_not] using hnmem
    rw [hnull]
    exact bot_le
  · apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr
    exact DataDrivenNV.LRS.BernsteinProof.bernstein_positive_variance P c σ hc0
      (lt_of_le_of_ne (sq_nonneg σ) (Ne.symm hσ)) N hNpos ξ hξm
      (iIndepFun_pi fun _ => (measurable_id.sub_const m).aemeasurable) hξmean hξb
      (fun i => (hξvar i).le) t ht

