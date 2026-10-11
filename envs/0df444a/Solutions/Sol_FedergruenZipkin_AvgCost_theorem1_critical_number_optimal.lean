-- Prove2me | solution 1 for FedergruenZipkin.AvgCost.theorem1_critical_number_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T14:07:40.147828+00:00
-- url     : https://prove2.me/submissions/95f45ab3-3d92-413b-bdb8-706ec2eed294

import Mathlib
import Definitions.Def_FedergruenZipkin_AvgCost_Model

set_option autoImplicit false
open Filter Topology Asymptotics
open scoped ENNReal

namespace FZ9
open FedergruenZipkin.AvgCost


lemma sym_bound {G : ℝ → ℝ} (hG : AnalyticAt ℝ G 0) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ θ : ℝ, |θ| ≤ δ → |G θ + G (-θ) - 2 * G 0| ≤ C * θ ^ 2 := by
  obtain ⟨P, hP⟩ := hG
  have h0 : P.coeff 0 = G 0 := hP.coeff_zero 1
  have hbig := hP.isBigO_sub_partialSum_pow 2
  obtain ⟨C, hCpos, hC⟩ := hbig.exists_pos
  rw [Asymptotics.IsBigOWith] at hC
  rw [Metric.eventually_nhds_iff] at hC
  obtain ⟨ε, hε, hball⟩ := hC
  refine ⟨2 * C, ε / 2, by positivity, ?_⟩
  intro θ hθ
  have h1 := hball (y := θ) (by rw [Real.dist_eq]; simp; linarith)
  have h2 := hball (y := -θ) (by rw [Real.dist_eq]; simp; linarith)
  have ps : ∀ y : ℝ, P.partialSum 2 y = P.coeff 0 + y * P.coeff 1 := by
    intro y
    simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  have h1' : |G θ - (G 0 + θ * P.coeff 1)| ≤ C * θ ^ 2 := by
    have := h1
    simp only [zero_add, ps, h0, Real.norm_eq_abs, abs_abs, abs_pow, sq_abs] at this
    exact this
  have h2' : |G (-θ) - (G 0 + (-θ) * P.coeff 1)| ≤ C * θ ^ 2 := by
    have := h2
    simp only [zero_add, ps, h0, Real.norm_eq_abs, abs_abs, abs_pow, sq_abs, abs_neg, neg_sq] at this
    exact this
  have e : G θ + G (-θ) - 2 * G 0
      = (G θ - (G 0 + θ * P.coeff 1)) + (G (-θ) - (G 0 + (-θ) * P.coeff 1)) := by ring
  rw [e]
  calc |(G θ - (G 0 + θ * P.coeff 1)) + (G (-θ) - (G 0 + (-θ) * P.coeff 1))|
      ≤ |G θ - (G 0 + θ * P.coeff 1)| + |G (-θ) - (G 0 + (-θ) * P.coeff 1)| := abs_add_le _ _
    _ ≤ C * θ ^ 2 + C * θ ^ 2 := add_le_add h1' h2'
    _ = 2 * C * θ ^ 2 := by ring


noncomputable def cser (p : ℕ → ℝ) (m : ℕ) (θ : ℝ) : ℝ :=
  ∑' j : ℕ, p j * (j:ℝ)^m * Real.cos ((j:ℝ) * θ)
noncomputable def sser (p : ℕ → ℝ) (m : ℕ) (θ : ℝ) : ℝ :=
  ∑' j : ℕ, p j * (j:ℝ)^m * Real.sin ((j:ℝ) * θ)

lemma cser_neg (p : ℕ → ℝ) (m : ℕ) (θ : ℝ) : cser p m (-θ) = cser p m θ := by
  unfold cser
  congr 1; ext j
  rw [mul_neg, Real.cos_neg]

lemma cser_zero (p : ℕ → ℝ) (m : ℕ) : cser p m 0 = ∑' j : ℕ, p j * (j:ℝ)^m := by
  unfold cser; simp

lemma cs_summable (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (m : ℕ)
    (h : Summable (fun j : ℕ => p j * (j:ℝ)^m)) (f : ℝ → ℝ) (hf : ∀ x, |f x| ≤ 1) (θ : ℝ) :
    Summable (fun j : ℕ => p j * (j:ℝ)^m * f ((j:ℝ) * θ)) := by
  refine Summable.of_norm_bounded h (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have : 0 ≤ p j * (j:ℝ)^m := mul_nonneg (hp j) (by positivity)
  rw [abs_of_nonneg this]
  calc p j * (j:ℝ)^m * |f ((j:ℝ) * θ)| ≤ p j * (j:ℝ)^m * 1 :=
        mul_le_mul_of_nonneg_left (hf _) this
    _ = _ := mul_one _

lemma cser_deriv (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (m : ℕ)
    (h0 : Summable (fun j : ℕ => p j * (j:ℝ)^m))
    (h1 : Summable (fun j : ℕ => p j * (j:ℝ)^(m+1))) (θ : ℝ) :
    HasDerivAt (cser p m) (-(sser p (m+1) θ)) θ := by
  have key := hasDerivAt_tsum (𝕜 := ℝ) (u := fun j : ℕ => p j * (j:ℝ)^(m+1))
    (g := fun (j : ℕ) (θ : ℝ) => p j * (j:ℝ)^m * Real.cos ((j:ℝ) * θ))
    (g' := fun (j : ℕ) (θ : ℝ) => -(p j * (j:ℝ)^(m+1) * Real.sin ((j:ℝ) * θ)))
    h1 ?_ ?_ ?_ θ (y₀ := 0)
  · unfold sser cser
    rw [tsum_neg] at key
    exact key
  · intro j y
    have := (((hasDerivAt_id y).const_mul (j:ℝ)).cos).const_mul (p j * (j:ℝ)^m)
    refine HasDerivAt.congr_deriv this ?_
    simp only [id, mul_one]
    ring
  · intro j y
    rw [Real.norm_eq_abs, abs_neg, abs_mul]
    have : 0 ≤ p j * (j:ℝ)^(m+1) := mul_nonneg (hp j) (by positivity)
    rw [abs_of_nonneg this]
    calc p j * (j:ℝ)^(m+1) * |Real.sin ((j:ℝ) * y)| ≤ p j * (j:ℝ)^(m+1) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) this
      _ = _ := mul_one _
  · exact cs_summable p hp m h0 Real.cos Real.abs_cos_le_one 0

lemma sser_deriv (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (m : ℕ)
    (h0 : Summable (fun j : ℕ => p j * (j:ℝ)^m))
    (h1 : Summable (fun j : ℕ => p j * (j:ℝ)^(m+1))) (θ : ℝ) :
    HasDerivAt (sser p m) (cser p (m+1) θ) θ := by
  have key := hasDerivAt_tsum (𝕜 := ℝ) (u := fun j : ℕ => p j * (j:ℝ)^(m+1))
    (g := fun (j : ℕ) (θ : ℝ) => p j * (j:ℝ)^m * Real.sin ((j:ℝ) * θ))
    (g' := fun (j : ℕ) (θ : ℝ) => p j * (j:ℝ)^(m+1) * Real.cos ((j:ℝ) * θ))
    h1 ?_ ?_ ?_ θ (y₀ := 0)
  · exact key
  · intro j y
    have := (((hasDerivAt_id y).const_mul (j:ℝ)).sin).const_mul (p j * (j:ℝ)^m)
    refine HasDerivAt.congr_deriv this ?_
    simp only [id, mul_one]
    ring
  · intro j y
    rw [Real.norm_eq_abs, abs_mul]
    have : 0 ≤ p j * (j:ℝ)^(m+1) := mul_nonneg (hp j) (by positivity)
    rw [abs_of_nonneg this]
    calc p j * (j:ℝ)^(m+1) * |Real.cos ((j:ℝ) * y)| ≤ p j * (j:ℝ)^(m+1) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) this
      _ = _ := mul_one _
  · exact cs_summable p hp m h0 Real.sin Real.abs_sin_le_one 0


lemma moment_step (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (m : ℕ)
    (h0 : Summable (fun j : ℕ => p j * (j:ℝ)^m))
    (hA : AnalyticAt ℝ (cser p m) 0) :
    Summable (fun j : ℕ => p j * (j:ℝ)^(m+2)) := by
  obtain ⟨C, δ, hδ, hsym⟩ := sym_bound hA
  have hCs : ∀ θ : ℝ, |θ| ≤ δ → cser p m 0 - cser p m θ ≤ |C| * θ ^ 2 := by
    intro θ hθ
    have h := hsym θ hθ
    rw [cser_neg] at h
    have h2 := (abs_le.1 h).1
    have : C * θ ^ 2 ≤ |C| * θ ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _)
    have := mul_nonneg (abs_nonneg C) (sq_nonneg θ)
    linarith
  have hnn : ∀ j : ℕ, 0 ≤ p j * (j:ℝ)^(m+2) := fun j => mul_nonneg (hp j) (by positivity)
  refine summable_of_sum_range_le hnn (c := 2 * |C| + 2) (fun N => ?_)
  set B : ℝ := ∑ j ∈ Finset.range N, p j * (j:ℝ)^(m+4) with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun j _ => mul_nonneg (hp j) (by positivity))
  set θ : ℝ := min (min δ (1 / ((N:ℝ) + 1))) (1 / (B + 1)) with hθdef
  have hθ0 : 0 < θ := lt_min (lt_min hδ (by positivity)) (by positivity)
  have hθδ : θ ≤ δ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hθN : θ ≤ 1 / ((N:ℝ) + 1) := le_trans (min_le_left _ _) (min_le_right _ _)
  have hθB : θ ≤ 1 / (B + 1) := min_le_right _ _
  have hθ1 : θ ≤ 1 := by
    have : 1 / (B + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    linarith
  -- upper bound
  have hup : ∑ j ∈ Finset.range N, p j * (j:ℝ)^m * (1 - Real.cos ((j:ℝ) * θ)) ≤ |C| * θ ^ 2 := by
    have hs1 : Summable (fun j : ℕ => p j * (j:ℝ)^m * Real.cos ((j:ℝ) * θ)) :=
      cs_summable p hp m h0 Real.cos Real.abs_cos_le_one θ
    have hterm : ∀ j : ℕ, 0 ≤ p j * (j:ℝ)^m * (1 - Real.cos ((j:ℝ) * θ)) := fun j =>
      mul_nonneg (mul_nonneg (hp j) (by positivity)) (by linarith [Real.cos_le_one ((j:ℝ) * θ)])
    have hsum : Summable (fun j : ℕ => p j * (j:ℝ)^m * (1 - Real.cos ((j:ℝ) * θ))) := by
      have := h0.sub hs1
      refine this.congr (fun j => ?_)
      ring
    calc _ ≤ ∑' j : ℕ, p j * (j:ℝ)^m * (1 - Real.cos ((j:ℝ) * θ)) :=
          Summable.sum_le_tsum _ (fun j _ => hterm j) hsum
      _ = cser p m 0 - cser p m θ := by
          rw [cser_zero]; unfold cser
          rw [← Summable.tsum_sub h0 hs1]
          congr 1; ext j; ring
      _ ≤ |C| * θ ^ 2 := hCs θ (by rw [abs_of_pos hθ0]; exact hθδ)
  -- lower bound termwise
  have hlow : ∀ j ∈ Finset.range N, θ ^ 2 / 2 * (p j * (j:ℝ)^(m+2)) - θ ^ 4 * (5 / 96) * (p j * (j:ℝ)^(m+4))
      ≤ p j * (j:ℝ)^m * (1 - Real.cos ((j:ℝ) * θ)) := by
    intro j hj
    have hjN : (j:ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.1 hj).le
    have hx : |(j:ℝ) * θ| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      calc (j:ℝ) * θ ≤ N * (1 / ((N:ℝ) + 1)) := by
            apply mul_le_mul hjN hθN hθ0.le (by positivity)
        _ ≤ 1 := by
            rw [mul_one_div, div_le_one (by positivity)]; linarith
    have hc := Real.cos_bound hx
    have hc2 := (abs_le.1 hc).2
    have e4 : |(j:ℝ) * θ| ^ 4 = ((j:ℝ) * θ) ^ 4 := by
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
    rw [e4] at hc2
    have hpj : 0 ≤ p j * (j:ℝ)^m := mul_nonneg (hp j) (by positivity)
    have : p j * (j:ℝ)^m * (((j:ℝ) * θ) ^ 2 / 2 - ((j:ℝ) * θ) ^ 4 * (5 / 96))
        ≤ p j * (j:ℝ)^m * (1 - Real.cos ((j:ℝ) * θ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hpj
    calc _ = p j * (j:ℝ)^m * (((j:ℝ) * θ) ^ 2 / 2 - ((j:ℝ) * θ) ^ 4 * (5 / 96)) := by ring
      _ ≤ _ := this
  have hlow' := Finset.sum_le_sum hlow
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hlow'
  rw [← hB] at hlow'
  set A : ℝ := ∑ j ∈ Finset.range N, p j * (j:ℝ)^(m+2) with hAdef
  have hcomb : θ ^ 2 / 2 * A - θ ^ 4 * (5 / 96) * B ≤ |C| * θ ^ 2 := le_trans hlow' hup
  have hθ2 : 0 < θ ^ 2 := by positivity
  have hBθ : θ ^ 2 * B ≤ 1 := by
    have h1 : θ * B ≤ 1 := by
      calc θ * B ≤ 1 / (B + 1) * B := mul_le_mul_of_nonneg_right hθB hB0
        _ ≤ 1 := by
          rw [one_div, inv_mul_le_iff₀ (by positivity)]; linarith
    calc θ ^ 2 * B = θ * (θ * B) := by ring
      _ ≤ 1 * 1 := mul_le_mul hθ1 h1 (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have : A ≤ 2 * |C| + 2 := by
    have h3 : θ ^ 2 * (A / 2 - θ ^ 2 * (5 / 96) * B - |C|) ≤ 0 := by nlinarith
    have h4 : A / 2 - θ ^ 2 * (5 / 96) * B - |C| ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      have := mul_pos hθ2 hcon
      linarith
    nlinarith
  exact this


lemma F_analytic (M : FedergruenZipkin.AvgCost.Model) : AnalyticAt ℝ (cser M.p 0) 0 := by
  have hA := (Complex.reCLM.analyticAt _).comp M.charfun_analytic
  convert hA using 1
  funext θ
  simp only [Function.comp]
  have hs : Summable (fun j : ℕ => ((M.p j : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ) * (j : ℂ))) := by
    refine Summable.of_norm_bounded M.p_sum.summable (fun j => ?_)
    have e : Complex.I * (θ : ℂ) * (j : ℂ) = (((θ * j : ℝ)) : ℂ) * Complex.I := by push_cast; ring
    rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact le_of_eq (abs_of_nonneg (M.p_nonneg j))
  rw [Complex.reCLM_apply, Complex.re_tsum hs]
  unfold cser
  congr 1; ext j
  have e : Complex.I * (θ : ℂ) * (j : ℂ) = (((θ * j : ℝ)) : ℂ) * Complex.I := by push_cast; ring
  rw [e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  simp [mul_comm]

lemma moments_aux (M : FedergruenZipkin.AvgCost.Model) (k : ℕ) :
    Summable (fun j : ℕ => M.p j * (j:ℝ)^(2*k)) ∧
    deriv^[2*k] (cser M.p 0) = fun θ => (-1:ℝ)^k * cser M.p (2*k) θ := by
  induction k with
  | zero =>
    refine ⟨by simpa using M.p_sum.summable, ?_⟩
    funext θ
    simp
  | succ k ih =>
    obtain ⟨hS, hD⟩ := ih
    have hp := M.p_nonneg
    have hGA : AnalyticAt ℝ (deriv^[2*k] (cser M.p 0)) 0 := (F_analytic M).iterated_deriv (2*k)
    have hCA : AnalyticAt ℝ (cser M.p (2*k)) 0 := by
      have : cser M.p (2*k) = fun θ => (-1:ℝ)^k * (deriv^[2*k] (cser M.p 0)) θ := by
        rw [hD]; funext θ
        rw [← mul_assoc, ← mul_pow]; simp
      rw [this]
      exact analyticAt_const.mul hGA
    have S2 := moment_step M.p hp (2*k) hS hCA
    have S1 : Summable (fun j : ℕ => M.p j * (j:ℝ)^(2*k+1)) := by
      refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hp j) (by positivity)) (fun j => ?_) (hS.add S2)
      have hx : 0 ≤ (j:ℝ)^(2*k) := by positivity
      have : (j:ℝ)^(2*k+1) ≤ (j:ℝ)^(2*k) + (j:ℝ)^(2*k+2) := by
        rw [pow_succ, pow_add]
        nlinarith [sq_nonneg ((j:ℝ) - 1), mul_nonneg hx (sq_nonneg ((j:ℝ) - 1))]
      calc M.p j * (j:ℝ)^(2*k+1) ≤ M.p j * ((j:ℝ)^(2*k) + (j:ℝ)^(2*k+2)) :=
            mul_le_mul_of_nonneg_left this (hp j)
        _ = _ := by ring
    have S2' : Summable (fun j : ℕ => M.p j * (j:ℝ)^(2*k+1+1)) := S2
    have e : 2*(k+1) = 2*k+1+1 := by ring
    rw [e]
    refine ⟨S2', ?_⟩
    have d1 : deriv (deriv^[2*k] (cser M.p 0)) = fun θ => (-1:ℝ)^k * (-(sser M.p (2*k+1) θ)) := by
      rw [hD]; funext θ
      exact (((cser_deriv M.p hp (2*k) hS S1 θ).const_mul ((-1:ℝ)^k))).deriv
    have d2 : deriv (deriv (deriv^[2*k] (cser M.p 0))) = fun θ => (-1:ℝ)^(k+1) * cser M.p (2*k+1+1) θ := by
      rw [d1]; funext θ
      have := ((sser_deriv M.p hp (2*k+1) S1 S2' θ).neg.const_mul ((-1:ℝ)^k)).deriv
      exact this.trans (by ring)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact d2


/-- All moments of the demand are finite (consequence of Assumption 2, analytic characteristic function). -/
theorem moments_finite (M : FedergruenZipkin.AvgCost.Model) (k : ℕ) :
    Summable (fun j : ℕ => M.p j * (j:ℝ)^k) := by
  have h2 := (moments_aux M k).1
  have h1 := M.p_sum.summable
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (M.p_nonneg j) (by positivity)) (fun j => ?_) (h2.add h1)
  have hp := M.p_nonneg j
  have : (j:ℝ)^k ≤ (j:ℝ)^(2*k) + 1 := by
    rcases le_or_gt (j:ℝ) 1 with h | h
    · have : (j:ℝ)^k ≤ 1 := pow_le_one₀ (by positivity) h
      have : 0 ≤ (j:ℝ)^(2*k) := by positivity
      linarith
    · have : (j:ℝ)^k ≤ (j:ℝ)^(2*k) := pow_le_pow_right₀ h.le (by omega)
      linarith
  calc M.p j * (j:ℝ)^k ≤ M.p j * ((j:ℝ)^(2*k) + 1) := mul_le_mul_of_nonneg_left this hp
    _ = _ := by ring


lemma abs_sub_pow_le (y : ℝ) (j : ℕ) (n : ℕ) :
    |y - (j:ℝ)| ^ n ≤ 2 ^ n * (|y| ^ n + (j:ℝ) ^ n) := by
  have h1 : |y - (j:ℝ)| ≤ |y| + (j:ℝ) := by
    calc |y - (j:ℝ)| ≤ |y| + |(j:ℝ)| := abs_sub _ _
      _ = _ := by rw [Nat.abs_cast]
  have h2 : |y| + (j:ℝ) ≤ 2 * max |y| (j:ℝ) := by
    have := le_max_left |y| (j:ℝ)
    have := le_max_right |y| (j:ℝ)
    linarith
  have h3 : |y - (j:ℝ)| ^ n ≤ (2 * max |y| (j:ℝ)) ^ n :=
    pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) n
  have h4 : (max |y| (j:ℝ)) ^ n ≤ |y| ^ n + (j:ℝ) ^ n := by
    rcases le_total |y| (j:ℝ) with h | h
    · rw [max_eq_right h]; have : 0 ≤ |y| ^ n := by positivity
      linarith
    · rw [max_eq_left h]; have : 0 ≤ (j:ℝ) ^ n := by positivity
      linarith
  calc |y - (j:ℝ)| ^ n ≤ (2 * max |y| (j:ℝ)) ^ n := h3
    _ = 2 ^ n * (max |y| (j:ℝ)) ^ n := mul_pow _ _ _
    _ ≤ 2 ^ n * (|y| ^ n + (j:ℝ) ^ n) := mul_le_mul_of_nonneg_left h4 (by positivity)

theorem summable_poly (M : FedergruenZipkin.AvgCost.Model) (n : ℕ) (A B : ℝ) (U : ℤ) (v : ℤ → ℝ)
    (hv : ∀ x ≤ U, |v x| ≤ A + B * |(x : ℝ)| ^ n) (y : ℤ) (hy : y ≤ U) :
    Summable (fun j : ℕ => M.p j * v (y - j)) := by
  have hp := M.p_nonneg
  have hn := moments_finite M n
  have hs := M.p_sum.summable
  have key : Summable (fun j : ℕ => M.p j * |A| + |B| * 2 ^ n * (|(y:ℝ)| ^ n * M.p j + M.p j * (j:ℝ) ^ n)) :=
    (hs.mul_right _).add (((hs.mul_left (|(y:ℝ)| ^ n)).add hn).mul_left _)
  refine Summable.of_norm_bounded key (fun j => ?_)
  have hyj : y - (j:ℤ) ≤ U := by omega
  have h1 := hv (y - j) hyj
  have h2 := abs_sub_pow_le (y:ℝ) j n
  have hc : ((y - (j:ℤ) : ℤ) : ℝ) = (y:ℝ) - (j:ℝ) := by push_cast; ring
  rw [hc] at h1
  have h3 : |v (y - j)| ≤ |A| + |B| * (2 ^ n * (|(y:ℝ)| ^ n + (j:ℝ) ^ n)) := by
    calc |v (y - j)| ≤ A + B * |(y:ℝ) - (j:ℝ)| ^ n := h1
      _ ≤ |A| + |B| * |(y:ℝ) - (j:ℝ)| ^ n := by
          have := le_abs_self A
          have : B * |(y:ℝ) - (j:ℝ)| ^ n ≤ |B| * |(y:ℝ) - (j:ℝ)| ^ n :=
            mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
          linarith
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left h2 (abs_nonneg B)
          linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp j)]
  calc M.p j * |v (y - j)| ≤ M.p j * (|A| + |B| * (2 ^ n * (|(y:ℝ)| ^ n + (j:ℝ) ^ n))) :=
        mul_le_mul_of_nonneg_left h3 (hp j)
    _ = _ := by ring



lemma pos_prop {f : ℤ → ℝ} {U : ℤ} (hc : ∀ x, x + 1 ≤ U → f x - f (x-1) ≤ f (x+1) - f x)
    {y : ℤ} (h : 0 < f (y+1) - f y) : ∀ n, y ≤ n → n + 1 ≤ U → 0 < f (n+1) - f n := by
  intro n hn
  induction n, hn using Int.le_induction with
  | base => intro _; exact h
  | succ n hn ih =>
    intro hU
    have h1 := ih (by omega)
    have h2 := hc (n+1) (by omega)
    have e : n + 1 - 1 = n := by ring
    rw [e] at h2
    linarith

lemma conv_mono_above {f : ℤ → ℝ} {U : ℤ}
    (hc : ∀ x, x + 1 ≤ U → f x - f (x-1) ≤ f (x+1) - f x)
    {s : ℤ} (hs : ∀ z ≤ U, f s ≤ f z) (hsU : s ≤ U) :
    ∀ a b, s ≤ a → a ≤ b → b ≤ U → f a ≤ f b := by
  have key : ∀ y, s ≤ y → y + 1 ≤ U → f y ≤ f (y+1) := by
    intro y hy
    induction y, hy using Int.le_induction with
    | base => intro hU; exact hs _ hU
    | succ n hn ih =>
      intro hU
      have h1 := ih (by omega)
      have h2 := hc (n+1) (by omega)
      have e : n + 1 - 1 = n := by ring
      rw [e] at h2
      linarith
  intro a b ha hab hb
  revert hb
  induction b, hab using Int.le_induction with
  | base => intro _; exact le_rfl
  | succ n hn ih =>
    intro hU
    exact le_trans (ih (by omega)) (key n (by omega) hU)

lemma conv_anti_below {f : ℤ → ℝ} {U : ℤ}
    (hc : ∀ x, x + 1 ≤ U → f x - f (x-1) ≤ f (x+1) - f x)
    {s : ℤ} (hs : ∀ z ≤ U, f s ≤ f z) (hsU : s ≤ U) :
    ∀ a b, a ≤ b → b ≤ s → f b ≤ f a := by
  have key : ∀ y, y + 1 ≤ s → f (y+1) ≤ f y := by
    intro y hy
    by_contra hcon
    push_neg at hcon
    have h := pos_prop hc (y := y) (by linarith) (s-1) (by omega) (by omega)
    have e : s - 1 + 1 = s := by ring
    rw [e] at h
    have := hs (s-1) (by omega)
    linarith
  intro a b hab
  induction b, hab using Int.le_induction with
  | base => intro _; exact le_rfl
  | succ n hn ih =>
    intro hU
    exact le_trans (key n (by omega)) (ih (by omega))

lemma R_convex (M : Model) (U : ℤ) (v : ℤ → ℝ) (hconv : ConvexBelow U v)
    (hsum : ∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j))) :
    ∀ y, y + 1 ≤ U → R M v y - R M v (y-1) ≤ R M v (y+1) - R M v y := by
  intro y hy
  have hG := M.G_convex y
  have s0 := hsum y (by omega)
  have s1 := hsum (y-1) (by omega)
  have s2 := hsum (y+1) hy
  have key : ∑' j : ℕ, M.p j * v (y - j) - ∑' j : ℕ, M.p j * v (y - 1 - j)
      ≤ ∑' j : ℕ, M.p j * v (y + 1 - j) - ∑' j : ℕ, M.p j * v (y - j) := by
    rw [← Summable.tsum_sub s0 s1, ← Summable.tsum_sub s2 s0]
    refine Summable.tsum_le_tsum (fun j => ?_) (s0.sub s1) (s2.sub s0)
    have h := hconv (y - j) (by have : (0:ℤ) ≤ j := by positivity
                                omega)
    have e1 : y - (j:ℤ) - 1 = y - 1 - j := by ring
    have e2 : y - (j:ℤ) + 1 = y + 1 - j := by ring
    rw [e1, e2] at h
    have hp := M.p_nonneg j
    nlinarith
  unfold R
  linarith

lemma G_anti (M : Model) (yInf : ℤ) (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf) :
    ∀ y, y < yInf → M.G (y+1) ≤ M.G y := by
  intro y hy
  by_contra hcon
  push_neg at hcon
  have hc : ∀ x, x + 1 ≤ yInf → M.G x - M.G (x-1) ≤ M.G (x+1) - M.G x := fun x _ => M.G_convex x
  have h := pos_prop hc (y := y) (by linarith) (yInf - 1) (by omega) (by omega)
  have e : yInf - 1 + 1 = yInf := by ring
  rw [e] at h
  have := hyInf.1 (yInf - 1)
  linarith [this]

lemma R_anti (M : Model) (U yInf : ℤ) (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf)
    (hU : yInf ≤ U) (v : ℤ → ℝ) (hmono : ∀ x, x < yInf → v (x + 1) ≤ v x)
    (hsum : ∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j))) :
    ∀ y, y < yInf → R M v (y+1) ≤ R M v y := by
  intro y hy
  have s0 := hsum y (by omega)
  have s2 := hsum (y+1) (by omega)
  unfold R
  have hG := G_anti M yInf hyInf y hy
  have : ∑' j : ℕ, M.p j * v (y + 1 - j) ≤ ∑' j : ℕ, M.p j * v (y - j) := by
    refine Summable.tsum_le_tsum (fun j => ?_) s2 s0
    have h := hmono (y - j) (by have : (0:ℤ) ≤ j := by positivity
                                omega)
    have e2 : y - (j:ℤ) + 1 = y + 1 - j := by ring
    rw [e2] at h
    exact mul_le_mul_of_nonneg_left h (M.p_nonneg j)
  linarith

theorem critNum_attains (M : Model) (U yInf : ℤ)
    (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf) (hU : yInf ≤ U) (g : ℝ) (v : ℤ → ℝ)
    (hv : InV M U yInf v) (hsum : ∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j)))
    (hopt : OptEq M U g v) :
    ∃ ystar : ℤ, ystar ≤ U ∧ yInf ≤ ystar ∧ (∀ x ≤ U, v ystar ≤ v x) ∧
      Feasible M U (critNum M ystar) ∧ ∀ x ≤ U, g + v x = R M v (critNum M ystar x) := by
  obtain ⟨_, hmono, hconv⟩ := hv
  have hRc := R_convex M U v hconv hsum
  have hRa := R_anti M U yInf hyInf hU v hmono hsum
  -- global minimizer over y ≤ U lies in [yInf, U]
  have hanti : ∀ y, y ≤ yInf → R M v yInf ≤ R M v y := by
    intro y hy
    induction y, hy using Int.le_induction_down with
    | base => exact le_rfl
    | pred n hn ih =>
      have := hRa (n-1) (by omega)
      rw [sub_add_cancel] at this
      exact le_trans ih this
  let S : Finset ℤ := (Finset.Icc yInf U).filter (fun y => ∀ z ∈ Finset.Icc yInf U, R M v y ≤ R M v z)
  have hne : S.Nonempty := by
    obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.Icc yInf U) (R M v)
      ⟨yInf, Finset.mem_Icc.2 ⟨le_rfl, hU⟩⟩
    exact ⟨m, Finset.mem_filter.2 ⟨hm, hmin⟩⟩
  set ys := S.min' hne with hys
  have hysS : ys ∈ S := Finset.min'_mem S hne
  have hysI := (Finset.mem_filter.1 hysS).1
  have hysmin := (Finset.mem_filter.1 hysS).2
  have hys1 : yInf ≤ ys := (Finset.mem_Icc.1 hysI).1
  have hys2 : ys ≤ U := (Finset.mem_Icc.1 hysI).2
  have hglob : ∀ z ≤ U, R M v ys ≤ R M v z := by
    intro z hz
    by_cases h : yInf ≤ z
    · exact hysmin z (Finset.mem_Icc.2 ⟨h, hz⟩)
    · have := hanti z (by omega)
      exact le_trans (hysmin yInf (Finset.mem_Icc.2 ⟨le_rfl, hU⟩)) this
  have hmonoR := conv_mono_above hRc hglob hys2
  have hantiR := conv_anti_below hRc hglob hys2
  -- OptEq at ys
  have hvys : g + v ys = R M v ys := by
    obtain ⟨hle, y, hy1, hy2, hy3, heq⟩ := hopt ys hys2
    have := hglob y hy3
    have h2 := hle ys le_rfl (by have := M.b_pos; omega) hys2
    linarith
  have hvmin : ∀ x ≤ U, v ys ≤ v x := by
    intro x hx
    obtain ⟨_, y, hy1, hy2, hy3, heq⟩ := hopt x hx
    have := hglob y hy3
    linarith
  have hfeas : Feasible M U (critNum M ys) := by
    intro x hx
    unfold critNum
    have := M.b_pos
    refine ⟨le_max_left _ _, ?_, ?_⟩
    · apply max_le (by omega)
      exact le_trans (min_le_right _ _) le_rfl
    · apply max_le hx
      exact le_trans (min_le_left _ _) hys2
  refine ⟨ys, hys2, hys1, hvmin, hfeas, ?_⟩
  intro x hx
  obtain ⟨hle, y, hy1, hy2, hy3, heq⟩ := hopt x hx
  have hb := M.b_pos
  unfold critNum
  by_cases hxy : ys ≤ x
  · have : max x (min ys (x + M.b)) = x := by
      apply max_eq_left
      exact le_trans (min_le_left _ _) hxy
    rw [this]
    -- R x ≤ R y for y ≥ x ≥ ys
    have := hmonoR x y hxy hy1 hy3
    have h2 := hle x le_rfl (by omega) hx
    linarith
  · push_neg at hxy
    by_cases hb' : ys ≤ x + M.b
    · have : max x (min ys (x + M.b)) = ys := by
        rw [min_eq_left hb']
        exact max_eq_right hxy.le
      rw [this]
      have h2 := hle ys hxy.le hb' hys2
      have := hglob y hy3
      linarith
    · push_neg at hb'
      have : max x (min ys (x + M.b)) = x + M.b := by
        rw [min_eq_right hb'.le]
        exact max_eq_right (by omega)
      rw [this]
      have h2 := hle (x + M.b) (by omega) le_rfl (by omega)
      have h3 := hantiR y (x + M.b) hy2 hb'.le
      linarith


lemma R_min_exists (M : Model) (U yInf : ℤ) (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf)
    (hU : yInf ≤ U) (v : ℤ → ℝ) (hv : InV M U yInf v)
    (hsum : ∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j))) :
    ∃ ys : ℤ, yInf ≤ ys ∧ ys ≤ U ∧ ∀ z ≤ U, R M v ys ≤ R M v z := by
  obtain ⟨_, hmono, hconv⟩ := hv
  have hRa := R_anti M U yInf hyInf hU v hmono hsum
  have hanti : ∀ y, y ≤ yInf → R M v yInf ≤ R M v y := by
    intro y hy
    induction y, hy using Int.le_induction_down with
    | base => exact le_rfl
    | pred n hn ih =>
      have := hRa (n-1) (by omega)
      rw [sub_add_cancel] at this
      exact le_trans ih this
  let S' : Finset ℤ := (Finset.Icc yInf U).filter (fun y => ∀ z ∈ Finset.Icc yInf U, R M v y ≤ R M v z)
  have hne : S'.Nonempty := by
    obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.Icc yInf U) (R M v)
      ⟨yInf, Finset.mem_Icc.2 ⟨le_rfl, hU⟩⟩
    exact ⟨m, Finset.mem_filter.2 ⟨hm, hmin⟩⟩
  have hysS : S'.min' hne ∈ S' := Finset.min'_mem S' hne
  have hysI := (Finset.mem_filter.1 hysS).1
  have hysmin := (Finset.mem_filter.1 hysS).2
  refine ⟨S'.min' hne, (Finset.mem_Icc.1 hysI).1, (Finset.mem_Icc.1 hysI).2, ?_⟩
  intro z hz
  by_cases h : yInf ≤ z
  · exact hysmin z (Finset.mem_Icc.2 ⟨h, hz⟩)
  · have := hanti z (by omega)
    exact le_trans (hysmin yInf (Finset.mem_Icc.2 ⟨le_rfl, hU⟩)) this

/-- the critical-number policy attains the min of a convex `R` with global min `ys` over `Y(x)` -/
lemma crit_opt (M : Model) (U : ℤ) (R' : ℤ → ℝ)
    (hRc : ∀ y, y + 1 ≤ U → R' y - R' (y-1) ≤ R' (y+1) - R' y)
    {ys : ℤ} (hysU : ys ≤ U) (hglob : ∀ z ≤ U, R' ys ≤ R' z) (x : ℤ) (hx : x ≤ U) :
    (x ≤ critNum M ys x ∧ critNum M ys x ≤ x + M.b ∧ critNum M ys x ≤ U) ∧
    ∀ y, x ≤ y → y ≤ x + M.b → y ≤ U → R' (critNum M ys x) ≤ R' y := by
  have hmonoR := conv_mono_above hRc hglob hysU
  have hantiR := conv_anti_below hRc hglob hysU
  have hb := M.b_pos
  refine ⟨⟨le_max_left _ _, max_le (by omega) (min_le_right _ _), max_le hx (le_trans (min_le_left _ _) hysU)⟩, ?_⟩
  intro y hy1 hy2 hy3
  unfold critNum
  by_cases hxy : ys ≤ x
  · have : max x (min ys (x + M.b)) = x := max_eq_left (le_trans (min_le_left _ _) hxy)
    rw [this]
    exact hmonoR x y hxy hy1 hy3
  · push_neg at hxy
    by_cases hb' : ys ≤ x + M.b
    · have : max x (min ys (x + M.b)) = ys := by
        rw [min_eq_left hb']; exact max_eq_right hxy.le
      rw [this]
      exact hglob y hy3
    · push_neg at hb'
      have : max x (min ys (x + M.b)) = x + M.b := by
        rw [min_eq_right hb'.le]; exact max_eq_right (by omega)
      rw [this]
      exact hantiR y (x + M.b) hy2 hb'.le

lemma S_eq_R (M : Model) (U : ℤ) (v : ℤ → ℝ)
    (hRc : ∀ y, y + 1 ≤ U → R M v y - R M v (y-1) ≤ R M v (y+1) - R M v y)
    {ys : ℤ} (hysU : ys ≤ U) (hglob : ∀ z ≤ U, R M v ys ≤ R M v z) (x : ℤ) (hx : x ≤ U) :
    S M U v x = R M v (critNum M ys x) := by
  obtain ⟨⟨h1, h2, h3⟩, hopt⟩ := crit_opt M U (R M v) hRc hysU hglob x hx
  unfold S
  apply le_antisymm
  · exact ciInf_le (f := fun y : {y : ℤ // x ≤ y ∧ y ≤ x + M.b ∧ y ≤ U} => R M v y)
      ⟨R M v (critNum M ys x), by
        rintro _ ⟨⟨y, hy⟩, rfl⟩
        exact hopt y hy.1 hy.2.1 hy.2.2⟩ ⟨critNum M ys x, h1, h2, h3⟩
  · have : Nonempty {y : ℤ // x ≤ y ∧ y ≤ x + M.b ∧ y ≤ U} := ⟨⟨critNum M ys x, h1, h2, h3⟩⟩
    exact le_ciInf (fun ⟨y, hy⟩ => hopt y hy.1 hy.2.1 hy.2.2)

/-- `x ↦ R (critNum ys x)` is discretely convex on `x ≤ U`. -/
lemma g_convex (M : Model) (U : ℤ) (R' : ℤ → ℝ)
    (hRc : ∀ y, y + 1 ≤ U → R' y - R' (y-1) ≤ R' (y+1) - R' y)
    {ys : ℤ} (hysU : ys ≤ U) (hglob : ∀ z ≤ U, R' ys ≤ R' z) :
    ∀ x, x + 1 ≤ U → R' (critNum M ys x) - R' (critNum M ys (x-1))
      ≤ R' (critNum M ys (x+1)) - R' (critNum M ys x) := by
  have hmonoR := conv_mono_above hRc hglob hysU
  have hantiR := conv_anti_below hRc hglob hysU
  have hb := M.b_pos
  have hh : ∀ t, ys ≤ t → critNum M ys t = t := fun t ht =>
    max_eq_left (le_trans (min_le_left _ _) ht)
  have hh2 : ∀ t, t ≤ ys → critNum M ys t = min ys (t + M.b) := by
    intro t ht
    unfold critNum
    apply max_eq_right
    rcases le_total ys (t + M.b) with h | h
    · rw [min_eq_left h]; exact ht
    · rw [min_eq_right h]; omega
  intro x hx
  have e1 : x - 1 + 1 = x := by ring
  by_cases hA : ys ≤ x - 1
  · rw [hh _ hA, hh x (by omega), hh (x+1) (by omega)]
    have := hRc x hx
    linarith
  · push_neg at hA
    by_cases hB : ys ≤ x
    · have hxy : x = ys := by omega
      have c1 : critNum M ys (x-1) = ys := by
        rw [hh2 _ (by omega)]; apply min_eq_left; omega
      rw [c1, hh x hB, hh (x+1) (by omega)]
      have := hmonoR x (x+1) hB (by omega) hx
      subst hxy
      linarith
    · push_neg at hB
      -- x < ys
      rw [hh2 (x-1) (by omega), hh2 x (by omega), hh2 (x+1) (by omega)]
      by_cases hC1 : x + 1 + M.b ≤ ys
      · rw [min_eq_right (show x - 1 + M.b ≤ ys by omega), min_eq_right (show x + M.b ≤ ys by omega),
          min_eq_right (show x + 1 + M.b ≤ ys by omega)]
        have := hRc (x + M.b) (by omega)
        have e2 : x - 1 + M.b = x + M.b - 1 := by ring
        rw [e2]
        have e3 : x + 1 + M.b = x + M.b + 1 := by ring
        rw [e3]
        linarith
      · push_neg at hC1
        by_cases hC2 : x + M.b ≤ ys
        · have hq : x + M.b = ys := by omega
          rw [min_eq_right (show x - 1 + M.b ≤ ys by omega), min_eq_left (show ys ≤ x + M.b by omega),
            min_eq_left (show ys ≤ x + 1 + M.b by omega)]
          have := hantiR (ys - 1) ys (by omega) le_rfl
          have e4 : x - 1 + M.b = ys - 1 := by omega
          rw [e4]
          linarith
        · push_neg at hC2
          rw [min_eq_left (show ys ≤ x - 1 + M.b by omega), min_eq_left (show ys ≤ x + M.b by omega),
            min_eq_left (show ys ≤ x + 1 + M.b by omega)]
          try linarith


lemma pow_add_le2 (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (n : ℕ) :
    (a + c) ^ n ≤ 2 ^ n * (a ^ n + c ^ n) := by
  have h2 : a + c ≤ 2 * max a c := by
    have := le_max_left a c
    have := le_max_right a c
    linarith
  have h3 : (a + c) ^ n ≤ (2 * max a c) ^ n := pow_le_pow_left₀ (by positivity) h2 n
  have h4 : (max a c) ^ n ≤ a ^ n + c ^ n := by
    rcases le_total a c with h | h
    · rw [max_eq_right h]; have : 0 ≤ a ^ n := by positivity
      linarith
    · rw [max_eq_left h]; have : 0 ≤ c ^ n := by positivity
      linarith
  calc (a + c) ^ n ≤ (2 * max a c) ^ n := h3
    _ = 2 ^ n * (max a c) ^ n := mul_pow _ _ _
    _ ≤ 2 ^ n * (a ^ n + c ^ n) := mul_le_mul_of_nonneg_left h4 (by positivity)

lemma poly_series_bound (M : Model) (n : ℕ) (A B : ℝ) (U : ℤ) (v : ℤ → ℝ)
    (hv : ∀ x ≤ U, |v x| ≤ A + B * |(x : ℝ)| ^ n) :
    ∃ A' B' : ℝ, ∀ y ≤ U, |∑' j : ℕ, M.p j * v (y - j)| ≤ A' + B' * |(y:ℝ)| ^ n := by
  have hp := M.p_nonneg
  have hn := moments_finite M n
  have hs := M.p_sum
  refine ⟨|A| + |B| * 2 ^ n * (∑' j : ℕ, M.p j * (j:ℝ)^n), |B| * 2 ^ n, fun y hy => ?_⟩
  have hsum : HasSum (fun j : ℕ => M.p j * |A| + |B| * 2 ^ n * (|(y:ℝ)| ^ n * M.p j + M.p j * (j:ℝ) ^ n))
      (1 * |A| + |B| * 2 ^ n * (|(y:ℝ)| ^ n * 1 + ∑' j : ℕ, M.p j * (j:ℝ)^n)) :=
    (hs.mul_right _).add (((hs.mul_left (|(y:ℝ)| ^ n)).add hn.hasSum).mul_left _)
  have key := tsum_of_norm_bounded hsum (f := fun j : ℕ => M.p j * v (y - j)) (fun j => ?_)
  · rw [Real.norm_eq_abs] at key
    calc _ ≤ _ := key
      _ = _ := by ring
  · have hyj : y - (j:ℤ) ≤ U := by omega
    have h1 := hv (y - j) hyj
    have h2 := abs_sub_pow_le (y:ℝ) j n
    have hc : ((y - (j:ℤ) : ℤ) : ℝ) = (y:ℝ) - (j:ℝ) := by push_cast; ring
    rw [hc] at h1
    have h3 : |v (y - j)| ≤ |A| + |B| * (2 ^ n * (|(y:ℝ)| ^ n + (j:ℝ) ^ n)) := by
      calc |v (y - j)| ≤ A + B * |(y:ℝ) - (j:ℝ)| ^ n := h1
        _ ≤ |A| + |B| * |(y:ℝ) - (j:ℝ)| ^ n := by
            have := le_abs_self A
            have : B * |(y:ℝ) - (j:ℝ)| ^ n ≤ |B| * |(y:ℝ) - (j:ℝ)| ^ n :=
              mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
            linarith
        _ ≤ _ := by
            have := mul_le_mul_of_nonneg_left h2 (abs_nonneg B)
            linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp j)]
    calc M.p j * |v (y - j)| ≤ M.p j * (|A| + |B| * (2 ^ n * (|(y:ℝ)| ^ n + (j:ℝ) ^ n))) :=
          mul_le_mul_of_nonneg_left h3 (hp j)
      _ = _ := by ring

lemma R_growth (M : Model) (U : ℤ) (v : ℤ → ℝ) (A B : ℝ)
    (hv : ∀ x ≤ U, |v x| ≤ A + B * |(x : ℝ)| ^ (M.ρ + 3)) :
    ∃ A1 B1 : ℝ, ∀ y ≤ U, |R M v y| ≤ A1 + B1 * |(y:ℝ)| ^ (M.ρ + 3) := by
  obtain ⟨AG, BG, hAG, hBG, hG⟩ := M.G_growth
  obtain ⟨A', B', hAB⟩ := poly_series_bound M (M.ρ + 3) A B U v hv
  refine ⟨AG + BG + A', BG + B', fun y hy => ?_⟩
  have h1 := hAB y hy
  have h2 := hG y
  have h3 := M.G_nonneg y
  have h4 : |(y:ℝ)| ^ M.ρ ≤ 1 + |(y:ℝ)| ^ (M.ρ + 3) := by
    rcases le_total |(y:ℝ)| 1 with h | h
    · have := pow_le_one₀ (abs_nonneg (y:ℝ)) h (n := M.ρ)
      have : 0 ≤ |(y:ℝ)| ^ (M.ρ + 3) := by positivity
      linarith
    · have := pow_le_pow_right₀ h (show M.ρ ≤ M.ρ + 3 by omega)
      linarith
  unfold R
  calc |M.G y + ∑' j : ℕ, M.p j * v (y - j)| ≤ |M.G y| + |∑' j : ℕ, M.p j * v (y - j)| := abs_add_le _ _
    _ ≤ (AG + BG * |(y:ℝ)| ^ M.ρ) + (A' + B' * |(y:ℝ)| ^ (M.ρ + 3)) := by
        rw [abs_of_nonneg h3]; linarith
    _ ≤ _ := by nlinarith

lemma InV_sub_const (M : Model) (U yInf : ℤ) (v : ℤ → ℝ) (hv : InV M U yInf v) (c : ℝ) :
    InV M U yInf (fun x => v x - c) := by
  obtain ⟨⟨A, B, hAB⟩, hm, hc⟩ := hv
  refine ⟨⟨A + |c|, B, fun x hx => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · have := hAB x hx
    have := abs_sub (v x) c
    linarith
  · have := hm x hx; simp only; linarith
  · have := hc x hx; simp only; linarith


lemma crit_eq_of_le (M : Model) (ys t : ℤ) (ht : t ≤ ys) :
    critNum M ys t = min ys (t + M.b) := by
  have hb := M.b_pos
  unfold critNum
  apply max_eq_right
  rcases le_total ys (t + M.b) with h | h
  · rw [min_eq_left h]; exact ht
  · rw [min_eq_right h]; omega

lemma S_inV (M : Model) (U yInf : ℤ) (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf)
    (hU : yInf ≤ U) (v : ℤ → ℝ) (hv : InV M U yInf v)
    (hsum : ∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j))) :
    ∃ ys : ℤ, yInf ≤ ys ∧ ys ≤ U ∧ (∀ z ≤ U, R M v ys ≤ R M v z) ∧ InV M U yInf (S M U v) := by
  obtain ⟨ys, hys1, hys2, hglob⟩ := R_min_exists M U yInf hyInf hU v hv hsum
  have hRc := R_convex M U v hv.2.2 hsum
  have hantiR := conv_anti_below hRc hglob hys2
  refine ⟨ys, hys1, hys2, hglob, ?_, ?_, ?_⟩
  · obtain ⟨A, B, hAB⟩ := hv.1
    obtain ⟨A1, B1, h1⟩ := R_growth M U v A B hAB
    refine ⟨A1 + |B1| * 2 ^ (M.ρ + 3) * (M.b:ℝ) ^ (M.ρ + 3), |B1| * 2 ^ (M.ρ + 3), fun x hx => ?_⟩
    rw [S_eq_R M U v hRc hys2 hglob x hx]
    obtain ⟨⟨c1, c2, c3⟩, _⟩ := crit_opt M U (R M v) hRc hys2 hglob x hx
    have h1y := h1 _ c3
    have hy : |((critNum M ys x : ℤ) : ℝ)| ≤ |(x:ℝ)| + (M.b:ℝ) := by
      have a1 : (x:ℝ) ≤ ((critNum M ys x : ℤ) : ℝ) := by exact_mod_cast c1
      have a2 : ((critNum M ys x : ℤ) : ℝ) ≤ (x:ℝ) + (M.b:ℝ) := by exact_mod_cast c2
      apply abs_le.2
      constructor
      · linarith [neg_abs_le (x:ℝ), (Nat.cast_nonneg M.b : (0:ℝ) ≤ M.b)]
      · linarith [le_abs_self (x:ℝ)]
    have hy2 : |((critNum M ys x : ℤ) : ℝ)| ^ (M.ρ + 3) ≤ 2 ^ (M.ρ + 3) * (|(x:ℝ)| ^ (M.ρ + 3) + (M.b:ℝ) ^ (M.ρ + 3)) :=
      (pow_le_pow_left₀ (abs_nonneg _) hy _).trans (pow_add_le2 _ _ (abs_nonneg _) (Nat.cast_nonneg _) _)
    have hB : B1 * |((critNum M ys x : ℤ) : ℝ)| ^ (M.ρ + 3) ≤
        |B1| * (2 ^ (M.ρ + 3) * (|(x:ℝ)| ^ (M.ρ + 3) + (M.b:ℝ) ^ (M.ρ + 3))) :=
      (mul_le_mul_of_nonneg_right (le_abs_self B1) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hy2 (abs_nonneg _))
    calc _ ≤ A1 + B1 * |((critNum M ys x : ℤ) : ℝ)| ^ (M.ρ + 3) := h1y
      _ ≤ _ := by nlinarith
  · intro x hx
    have hxU : x ≤ U := by omega
    have hx1U : x + 1 ≤ U := by omega
    rw [S_eq_R M U v hRc hys2 hglob (x+1) hx1U, S_eq_R M U v hRc hys2 hglob x hxU,
      crit_eq_of_le M ys x (by omega), crit_eq_of_le M ys (x+1) (by omega)]
    have hb := M.b_pos
    exact hantiR _ _ (min_le_min le_rfl (by omega)) (min_le_left _ _)
  · intro x hx
    have := g_convex M U (R M v) hRc hys2 hglob x hx
    rw [S_eq_R M U v hRc hys2 hglob (x-1) (by omega), S_eq_R M U v hRc hys2 hglob x (by omega),
      S_eq_R M U v hRc hys2 hglob (x+1) hx]
    exact this

theorem lemma5_full (M : Model) (U yInf : ℤ)
    (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf) (hU : yInf ≤ U)
    (v : ℤ → ℝ) (hv : InV M U yInf v) :
    (∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j))) ∧
    InV M U yInf (S M U v) ∧ InV M U yInf (Q M U yInf v) ∧
    ∀ L : ℤ, L ≤ yInf - M.b →
      (∀ x ≤ U, SL M U L v x = S M U v x) ∧ (∀ x ≤ U, QL M U L yInf v x = Q M U yInf v x) := by
  have hsum : ∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j)) := by
    obtain ⟨⟨A, B, hAB⟩, _, _⟩ := hv
    exact fun y hy => summable_poly M (M.ρ + 3) A B U v hAB y hy
  obtain ⟨ys, hys1, hys2, hglob, hS⟩ := S_inV M U yInf hyInf hU v hv hsum
  have hRc := R_convex M U v hv.2.2 hsum
  refine ⟨hsum, hS, InV_sub_const M U yInf (S M U v) hS (S M U v yInf), ?_⟩
  intro L hL
  have hb := M.b_pos
  have hSL : ∀ x ≤ U, SL M U L v x = S M U v x := by
    intro x hx
    unfold SL
    split_ifs with h
    · rw [S_eq_R M U v hRc hys2 hglob x hx]
      have : critNum M ys x = x + M.b := by
        unfold critNum
        rw [min_eq_right (by omega)]
        exact max_eq_right (by omega)
      rw [this]
    · rfl
  refine ⟨hSL, fun x hx => ?_⟩
  unfold QL Q
  rw [hSL x hx, hSL yInf hU]

end FZ9

namespace FZL
open FedergruenZipkin.AvgCost

/-- pointwise second-order binomial bound -/
lemma binom_bound (n d : ℝ) (hn : 1 ≤ n) (k : ℕ) :
    (n + d) ^ (k + 2) ≤ n ^ (k + 2) + (k + 2) * n ^ (k + 1) * d + n ^ k * (1 + |d|) ^ (k + 2) := by
  have hn0 : 0 ≤ n := by linarith
  rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ]
  have e1 : (k + 1 + 1 - (k + 1)) = 1 := by omega
  have e2 : (k + 2 - (k + 2)) = 0 := by omega
  have hc1 : ((Nat.choose (k + 2) (k + 1) : ℕ) : ℝ) = k + 2 := by
    rw [Nat.choose_succ_self_right]; push_cast; ring
  simp only [e1, e2, pow_one, pow_zero, mul_one, Nat.choose_self, Nat.cast_one]
  have hrest : ∑ m ∈ Finset.range (k + 1), n ^ m * d ^ (k + 2 - m) * ((Nat.choose (k + 2) m : ℕ) : ℝ)
      ≤ n ^ k * (1 + |d|) ^ (k + 2) := by
    rw [add_pow, Finset.mul_sum]
    calc ∑ m ∈ Finset.range (k + 1), n ^ m * d ^ (k + 2 - m) * ((Nat.choose (k + 2) m : ℕ) : ℝ)
        ≤ ∑ m ∈ Finset.range (k + 1), n ^ k * (1 ^ m * |d| ^ (k + 2 - m) * ((Nat.choose (k + 2) m : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro m hm
          have hmk : m ≤ k := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hm
          have h1 : n ^ m ≤ n ^ k := pow_le_pow_right₀ hn hmk
          have h2 : d ^ (k + 2 - m) ≤ |d| ^ (k + 2 - m) := by
            calc d ^ (k + 2 - m) ≤ |d ^ (k + 2 - m)| := le_abs_self _
              _ = |d| ^ (k + 2 - m) := abs_pow _ _
          have hC : (0:ℝ) ≤ ((Nat.choose (k + 2) m : ℕ) : ℝ) := by positivity
          have h3 : 0 ≤ |d| ^ (k + 2 - m) := by positivity
          have h4 : 0 ≤ n ^ m := by positivity
          rw [one_pow, one_mul]
          calc n ^ m * d ^ (k + 2 - m) * ((Nat.choose (k + 2) m : ℕ) : ℝ)
              ≤ n ^ m * |d| ^ (k + 2 - m) * ((Nat.choose (k + 2) m : ℕ) : ℝ) := by gcongr
            _ ≤ n ^ k * |d| ^ (k + 2 - m) * ((Nat.choose (k + 2) m : ℕ) : ℝ) := by gcongr
            _ = _ := by ring
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm; simp only [Finset.mem_range] at hm ⊢; omega
          · intro m _ _; positivity
  have hc1' : ((Nat.choose (k + 1 + 1) (k + 1) : ℕ) : ℝ) = k + 2 := hc1
  rw [hc1']
  have : n ^ (k + 1) * d * ((k:ℝ) + 2) = (k + 2) * n ^ (k + 1) * d := by ring
  linarith

lemma summ_pow_shift (M : Model) (hmom : ∀ k, Summable (fun j : ℕ => M.p j * (j:ℝ)^k))
    (c : ℝ) (hc : 0 ≤ c) (m : ℕ) : Summable (fun j : ℕ => M.p j * (c + j) ^ m) := by
  have hs := (M.p_sum.summable.mul_left (2 ^ (m - 1) * c ^ m)).add ((hmom m).mul_left (2 ^ (m - 1)))
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (M.p_nonneg j) (by positivity)) (fun j => ?_) hs
  have h := add_pow_le hc (Nat.cast_nonneg j : (0:ℝ) ≤ j) m
  have hp := M.p_nonneg j
  calc M.p j * (c + j) ^ m ≤ M.p j * (2 ^ (m - 1) * (c ^ m + (j:ℝ) ^ m)) := mul_le_mul_of_nonneg_left h hp
    _ = _ := by ring

/-- drift of the polynomial `n ^ (k+2)` under the order-to-capacity step `n ↦ n - b + D` -/
lemma drift (M : Model) (hmom : ∀ k, Summable (fun j : ℕ => M.p j * (j:ℝ)^k)) (k : ℕ) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ n : ℝ, N₀ ≤ n →
      Summable (fun j : ℕ => M.p j * (n - M.b + j) ^ (k + 2)) ∧
      ∑' j : ℕ, M.p j * (n - M.b + j) ^ (k + 2)
        ≤ n ^ (k + 2) - ((k + 2) * (M.b - ∑' j : ℕ, (j:ℝ) * M.p j) / 2) * n ^ (k + 1) := by
  set μ := ∑' j : ℕ, (j:ℝ) * M.p j with hμdef
  have hμ : μ < M.b := M.mean_lt_b
  have hb0 : (0:ℝ) ≤ M.b := Nat.cast_nonneg _
  have hKs : Summable (fun j : ℕ => M.p j * (1 + |(j:ℝ) - M.b|) ^ (k + 2)) := by
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (M.p_nonneg j) (by positivity)) (fun j => ?_)
      (summ_pow_shift M hmom (1 + M.b) (by positivity) (k + 2))
    have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
    have h1 : |(j:ℝ) - M.b| ≤ M.b + j := by rw [abs_le]; constructor <;> linarith
    have h2 : (1 + |(j:ℝ) - M.b|) ^ (k + 2) ≤ (1 + M.b + j) ^ (k + 2) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    exact mul_le_mul_of_nonneg_left h2 (M.p_nonneg j)
  set K := ∑' j : ℕ, M.p j * (1 + |(j:ℝ) - M.b|) ^ (k + 2) with hKdef
  set c := ((k:ℝ) + 2) * (M.b - μ) / 2 with hcdef
  have hc : 0 < c := by
    have : 0 < (M.b:ℝ) - μ := sub_pos.2 hμ
    positivity
  refine ⟨max 1 (K / c), le_max_left _ _, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnK : K / c ≤ n := le_trans (le_max_right _ _) hn
  have hs1 := M.p_sum.summable
  have hm1 : Summable (fun j : ℕ => (j:ℝ) * M.p j) := (hmom 1).congr (fun j => by ring)
  have hsd : Summable (fun j : ℕ => M.p j * ((j:ℝ) - M.b)) :=
    (hm1.sub (hs1.mul_right (M.b:ℝ))).congr (fun j => by ring)
  have hpt : ∀ j : ℕ, M.p j * (n - M.b + j) ^ (k + 2) ≤
      (M.p j * n ^ (k + 2) + ((k + 2) * n ^ (k + 1)) * (M.p j * ((j:ℝ) - M.b)))
        + n ^ k * (M.p j * (1 + |(j:ℝ) - M.b|) ^ (k + 2)) := by
    intro j
    have h := binom_bound n ((j:ℝ) - M.b) hn1 k
    have e : n - M.b + j = n + ((j:ℝ) - M.b) := by ring
    rw [e]
    calc M.p j * (n + ((j:ℝ) - M.b)) ^ (k + 2)
        ≤ M.p j * (n ^ (k + 2) + (k + 2) * n ^ (k + 1) * ((j:ℝ) - M.b) + n ^ k * (1 + |(j:ℝ) - M.b|) ^ (k + 2)) :=
          mul_le_mul_of_nonneg_left h (M.p_nonneg j)
      _ = _ := by ring
  have hsA : Summable (fun j : ℕ => M.p j * n ^ (k + 2) + ((k + 2) * n ^ (k + 1)) * (M.p j * ((j:ℝ) - M.b))) :=
    (hs1.mul_right _).add (hsd.mul_left _)
  have hsR := hsA.add (hKs.mul_left (n ^ k))
  have hsL : Summable (fun j : ℕ => M.p j * (n - M.b + j) ^ (k + 2)) := by
    refine Summable.of_norm_bounded (summ_pow_shift M hmom (n + M.b) (by linarith) (k + 2)) (fun j => ?_)
    have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (M.p_nonneg j), abs_pow]
    apply mul_le_mul_of_nonneg_left _ (M.p_nonneg j)
    apply pow_le_pow_left₀ (abs_nonneg _)
    rw [abs_le]; constructor <;> linarith
  refine ⟨hsL, ?_⟩
  have hle := Summable.tsum_le_tsum hpt hsL hsR
  rw [Summable.tsum_add hsA (hKs.mul_left _), Summable.tsum_add (hs1.mul_right _) (hsd.mul_left _),
    tsum_mul_right, tsum_mul_left, tsum_mul_left, M.p_sum.tsum_eq] at hle
  have hEd : ∑' j : ℕ, M.p j * ((j:ℝ) - M.b) = μ - M.b := by
    have e : (fun j : ℕ => M.p j * ((j:ℝ) - M.b)) = fun j : ℕ => (j:ℝ) * M.p j - M.p j * M.b := by
      funext j; ring
    rw [e, Summable.tsum_sub hm1 (hs1.mul_right _), tsum_mul_right, M.p_sum.tsum_eq]
    ring
  rw [hEd, ← hKdef] at hle
  have key : n ^ k * K ≤ c * n ^ (k + 1) := by
    have h1 : K ≤ c * n := by rw [div_le_iff₀ hc] at hnK; linarith
    calc n ^ k * K ≤ n ^ k * (c * n) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = c * n ^ (k + 1) := by ring
  have e2 : ((k:ℝ) + 2) * n ^ (k + 1) * (μ - M.b) = -(2 * c) * n ^ (k + 1) := by
    rw [hcdef]; ring
  linarith

/-- polynomial Lyapunov supersolution for order-to-capacity, absorbing a cost of degree `k+1` -/
lemma lyap (M : Model) (hmom : ∀ k, Summable (fun j : ℕ => M.p j * (j:ℝ)^k)) (U : ℤ) (k : ℕ)
    (A₀ B₀ T₀ : ℝ) (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀) :
    ∃ T A : ℝ, (U:ℝ) + M.b + 1 ≤ T ∧ T₀ ≤ T ∧ 0 < A ∧ ∀ x : ℤ, x ≤ U →
      Summable (fun j : ℕ => M.p j * (A * (T - ((x + M.b - j : ℤ) : ℝ)) ^ (k + 2))) ∧
      A₀ + B₀ * |((x + M.b : ℤ) : ℝ)| ^ (k + 1)
        + ∑' j : ℕ, M.p j * (A * (T - ((x + M.b - j : ℤ) : ℝ)) ^ (k + 2)) ≤ A * (T - x) ^ (k + 2) := by
  obtain ⟨N₀, hN1, hdr⟩ := drift M hmom k
  set μ := ∑' j : ℕ, (j:ℝ) * M.p j with hμdef
  have hμ : μ < M.b := M.mean_lt_b
  have hb0 : (0:ℝ) ≤ M.b := Nat.cast_nonneg _
  set c := ((k:ℝ) + 2) * (M.b - μ) / 2 with hcdef
  have hc : 0 < c := by
    have : 0 < (M.b:ℝ) - μ := sub_pos.2 hμ
    positivity
  set T : ℝ := |(U:ℝ)| + M.b + 1 + N₀ + |T₀| with hTdef
  set C₁ : ℝ := A₀ + B₀ * (1 + |T| + M.b) ^ (k + 1) with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨T, C₁ / c + 1, ?_, ?_, by positivity, fun x hx => ?_⟩
  · have := le_abs_self (U:ℝ); have := abs_nonneg T₀; linarith
  · have := le_abs_self T₀; have := abs_nonneg (U:ℝ); linarith
  have hxR : (x:ℝ) ≤ U := by exact_mod_cast hx
  set n := T - x with hndef
  have hnN : N₀ ≤ n := by have := le_abs_self (U:ℝ); have := abs_nonneg T₀; linarith
  have hn1 : 1 ≤ n := le_trans hN1 hnN
  obtain ⟨hs, hE⟩ := hdr n hnN
  have hcast : ∀ j : ℕ, (T - ((x + M.b - j : ℤ) : ℝ)) = n - M.b + j := by
    intro j; push_cast; ring
  have hfun : (fun j : ℕ => M.p j * ((C₁ / c + 1) * (T - ((x + M.b - j : ℤ) : ℝ)) ^ (k + 2)))
      = fun j : ℕ => (C₁ / c + 1) * (M.p j * (n - M.b + j) ^ (k + 2)) := by
    funext j; rw [hcast j]; ring
  rw [hfun]
  refine ⟨hs.mul_left _, ?_⟩
  rw [tsum_mul_left]
  have hA0 : 0 ≤ C₁ / c + 1 := by positivity
  have h1 : (C₁ / c + 1) * ∑' j : ℕ, M.p j * (n - M.b + j) ^ (k + 2)
      ≤ (C₁ / c + 1) * (n ^ (k + 2) - c * n ^ (k + 1)) := mul_le_mul_of_nonneg_left hE hA0
  have hxb : |((x + M.b : ℤ) : ℝ)| ≤ n * (1 + |T| + M.b) := by
    have e : ((x + M.b : ℤ) : ℝ) = T - n + M.b := by push_cast; ring
    rw [e]
    have := abs_add_le (T - n) (M.b:ℝ)
    have := abs_sub T n
    have hTa := abs_nonneg T
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ n)] at *
    rw [abs_of_nonneg hb0] at *
    nlinarith
  have h2 : B₀ * |((x + M.b : ℤ) : ℝ)| ^ (k + 1) ≤ B₀ * (1 + |T| + M.b) ^ (k + 1) * n ^ (k + 1) := by
    calc B₀ * |((x + M.b : ℤ) : ℝ)| ^ (k + 1) ≤ B₀ * (n * (1 + |T| + M.b)) ^ (k + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hxb _) hB₀
      _ = _ := by rw [mul_pow]; ring
  have h3 : A₀ ≤ A₀ * n ^ (k + 1) := by
    have : 1 ≤ n ^ (k + 1) := one_le_pow₀ hn1
    nlinarith
  have h4 : (C₁ / c + 1) * c = C₁ + c := by field_simp
  have hnp : 0 ≤ n ^ (k + 1) := by positivity
  have h5 : (C₁ / c + 1) * (n ^ (k + 2) - c * n ^ (k + 1))
      = (C₁ / c + 1) * n ^ (k + 2) - (C₁ + c) * n ^ (k + 1) := by rw [← h4]; ring
  have h6 : C₁ * n ^ (k + 1) = A₀ * n ^ (k + 1) + B₀ * (1 + |T| + M.b) ^ (k + 1) * n ^ (k + 1) := by
    rw [hC₁]; ring
  nlinarith

end FZL

namespace FZF
open FedergruenZipkin.AvgCost

noncomputable def Lam (T A : ℝ) (k : ℕ) (x : ℤ) : ℝ := A * (T - x) ^ k

def LyapOK (M : Model) (U : ℤ) (T A : ℝ) : Prop :=
  (U:ℝ) + M.b + 1 ≤ T ∧ 0 < A ∧ ∀ x : ℤ, x ≤ U →
    Summable (fun j : ℕ => M.p j * Lam T A (M.ρ + 1) (x + M.b - j)) ∧
    M.G (x + M.b) + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (x + M.b - j) ≤ Lam T A (M.ρ + 1) x

lemma Lam_nonneg (M : Model) (U : ℤ) (T A : ℝ) (hLy : LyapOK M U T A) (x : ℤ) (hx : x ≤ U + M.b) :
    0 ≤ Lam T A (M.ρ + 1) x := by
  obtain ⟨hT, hA, _⟩ := hLy
  have : (x:ℝ) ≤ U + M.b := by exact_mod_cast hx
  unfold Lam
  have : 0 ≤ T - x := by linarith
  positivity

lemma Lam_summ (M : Model) (U : ℤ) (T A : ℝ) (hLy : LyapOK M U T A) (y : ℤ) (hy : y ≤ U + M.b) :
    Summable (fun j : ℕ => M.p j * Lam T A (M.ρ + 1) (y - j)) := by
  have h := (hLy.2.2 (y - M.b) (by omega)).1
  refine h.congr (fun j => ?_)
  rw [show y - (M.b:ℤ) + (M.b:ℤ) - (j:ℤ) = y - j by ring]

noncomputable def Vit (M : Model) (U : ℤ) (α : ℝ) : ℕ → ℤ → ℝ
  | 0 => fun _ => 0
  | n + 1 => S M U (fun z => α * Vit M U α n z)

lemma summ_of_InV (M : Model) (U yInf : ℤ) (v : ℤ → ℝ) (hv : InV M U yInf v) :
    ∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j)) := by
  obtain ⟨⟨A, B, h⟩, _, _⟩ := hv
  exact fun y hy => FZ9.summable_poly M _ A B U v h y hy

lemma InV_smul (M : Model) (U yInf : ℤ) (v : ℤ → ℝ) (hv : InV M U yInf v) (α : ℝ) (hα : 0 ≤ α) :
    InV M U yInf (fun z => α * v z) := by
  obtain ⟨⟨A, B, h⟩, hm, hc⟩ := hv
  refine ⟨⟨α * A, α * B, fun x hx => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · rw [abs_mul, abs_of_nonneg hα]
    have := mul_le_mul_of_nonneg_left (h x hx) hα
    linarith
  · exact mul_le_mul_of_nonneg_left (hm x hx) hα
  · have := mul_le_mul_of_nonneg_left (hc x hx) hα
    simp only
    linarith

lemma S_props (M : Model) (U yInf : ℤ) (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf)
    (hU : yInf ≤ U) (v : ℤ → ℝ) (hv : InV M U yInf v)
    (hsum : ∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j))) (x : ℤ) (hx : x ≤ U) :
    (∀ y, x ≤ y → y ≤ x + M.b → y ≤ U → S M U v x ≤ R M v y) ∧
    ∃ y, x ≤ y ∧ y ≤ x + M.b ∧ y ≤ U ∧ S M U v x = R M v y := by
  obtain ⟨ys, _, hysU, hglob, _⟩ := FZ9.S_inV M U yInf hyInf hU v hv hsum
  have hRc := FZ9.R_convex M U v hv.2.2 hsum
  have hS := FZ9.S_eq_R M U v hRc hysU hglob x hx
  obtain ⟨⟨h1, h2, h3⟩, hopt⟩ := FZ9.crit_opt M U (R M v) hRc hysU hglob x hx
  refine ⟨fun y a b c => ?_, ⟨_, h1, h2, h3, hS⟩⟩
  rw [hS]; exact hopt y a b c

lemma Vit_props (M : Model) (U yInf : ℤ) (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf)
    (hU : yInf ≤ U) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (T A : ℝ) (hLy : LyapOK M U T A) (n : ℕ) :
    InV M U yInf (Vit M U α n) ∧ (∀ x ≤ U, 0 ≤ Vit M U α n x) ∧
    (∀ x ≤ U, Vit M U α n x ≤ Lam T A (M.ρ + 1) x
        + (M.G U + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (U - j)) / (1 - α)) := by
  set K := M.G U + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (U - j) with hKdef
  have hK0 : 0 ≤ K := by
    have := M.G_nonneg U
    have : 0 ≤ ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (U - j) :=
      tsum_nonneg (fun j => mul_nonneg (M.p_nonneg j) (Lam_nonneg M U T A hLy _ (by omega)))
    linarith
  have h1α : 0 < 1 - α := by linarith
  set K' := K / (1 - α) with hK'def
  have hK'0 : 0 ≤ K' := div_nonneg hK0 h1α.le
  have hKK : K + α * K' = K' := by rw [hK'def]; field_simp; ring
  have hs1 := M.p_sum.summable
  induction n with
  | zero =>
    refine ⟨⟨⟨0, 0, fun x _ => by simp [Vit]⟩, fun x _ => by simp [Vit], fun x _ => by simp [Vit]⟩,
      fun x _ => by simp [Vit], fun x hx => ?_⟩
    have := Lam_nonneg M U T A hLy x (by omega)
    simp only [Vit]
    linarith
  | succ n ih =>
    obtain ⟨hI, hN, hB⟩ := ih
    have hw := InV_smul M U yInf _ hI α hα0.le
    have hws := summ_of_InV M U yInf _ hw
    have hS := S_props M U yInf hyInf hU _ hw hws
    have hdef : Vit M U α (n + 1) = S M U (fun z => α * Vit M U α n z) := rfl
    have hRb : ∀ y ≤ U, R M (fun z => α * Vit M U α n z) y
        ≤ M.G y + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (y - j) + α * K' := by
      intro y hy
      have hsL := Lam_summ M U T A hLy y (by omega)
      have hle : ∑' j : ℕ, M.p j * (α * Vit M U α n (y - j))
          ≤ ∑' j : ℕ, (M.p j * Lam T A (M.ρ + 1) (y - j) + M.p j * (α * K')) := by
        refine Summable.tsum_le_tsum (fun j => ?_) (hws y hy) (hsL.add (hs1.mul_right _))
        have hyj : y - (j:ℤ) ≤ U := by omega
        have h1 := hB (y - j) hyj
        have h2 := Lam_nonneg M U T A hLy (y - j) (by omega)
        have h3 : α * Vit M U α n (y - j) ≤ Lam T A (M.ρ + 1) (y - j) + α * K' := by nlinarith
        have := mul_le_mul_of_nonneg_left h3 (M.p_nonneg j)
        linarith
      rw [Summable.tsum_add hsL (hs1.mul_right _), tsum_mul_right, M.p_sum.tsum_eq, one_mul] at hle
      unfold R
      linarith
    refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
    · rw [hdef]
      obtain ⟨_, _, _, _, hSI⟩ := FZ9.S_inV M U yInf hyInf hU _ hw hws
      exact hSI
    · obtain ⟨y, hy1, hy2, hy3, heq⟩ := (hS x hx).2
      rw [hdef, heq]
      unfold R
      have := M.G_nonneg y
      have : 0 ≤ ∑' j : ℕ, M.p j * (α * Vit M U α n (y - j)) :=
        tsum_nonneg (fun j => mul_nonneg (M.p_nonneg j) (mul_nonneg hα0.le (hN _ (by omega))))
      linarith
    · have hL0 := Lam_nonneg M U T A hLy x (by omega)
      rw [hdef]
      by_cases hxb : x + M.b ≤ U
      · have h1 := (hS x hx).1 (x + M.b) (by omega) le_rfl hxb
        have h2 := hRb (x + M.b) hxb
        have h3 := (hLy.2.2 x hx).2
        have h4 : α * K' ≤ K' := by nlinarith
        linarith
      · have h1 := (hS x hx).1 U hx (by omega) le_rfl
        have h2 := hRb U le_rfl
        linarith

lemma Vit_mono (M : Model) (U yInf : ℤ) (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf)
    (hU : yInf ≤ U) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (T A : ℝ) (hLy : LyapOK M U T A) :
    ∀ n, ∀ x ≤ U, Vit M U α n x ≤ Vit M U α (n + 1) x := by
  have P := fun m => Vit_props M U yInf hyInf hU α hα0 hα1 T A hLy m
  intro n
  induction n with
  | zero => intro x hx; exact (P 1).2.1 x hx
  | succ n ih =>
    intro x hx
    have hw1 := InV_smul M U yInf _ (P (n + 1)).1 α hα0.le
    have hws1 := summ_of_InV M U yInf _ hw1
    have hw0 := InV_smul M U yInf _ (P n).1 α hα0.le
    have hws0 := summ_of_InV M U yInf _ hw0
    obtain ⟨y, hy1, hy2, hy3, heq⟩ := (S_props M U yInf hyInf hU _ hw1 hws1 x hx).2
    have hle := (S_props M U yInf hyInf hU _ hw0 hws0 x hx).1 y hy1 hy2 hy3
    show S M U (fun z => α * Vit M U α n z) x ≤ S M U (fun z => α * Vit M U α (n + 1) z) x
    rw [heq]
    refine le_trans hle ?_
    unfold R
    have : ∑' j : ℕ, M.p j * (α * Vit M U α n (y - j)) ≤ ∑' j : ℕ, M.p j * (α * Vit M U α (n + 1) (y - j)) :=
      Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (ih _ (by omega)) hα0.le) (M.p_nonneg j)) (hws0 y hy3) (hws1 y hy3)
    linarith

noncomputable def Vlim (M : Model) (U : ℤ) (α : ℝ) (x : ℤ) : ℝ := ⨆ n, Vit M U α n x

lemma Vit_tendsto (M : Model) (U yInf : ℤ) (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf)
    (hU : yInf ≤ U) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (T A : ℝ) (hLy : LyapOK M U T A)
    (x : ℤ) (hx : x ≤ U) : Tendsto (fun n => Vit M U α n x) atTop (𝓝 (Vlim M U α x)) :=
  tendsto_atTop_ciSup (monotone_nat_of_le_succ (fun n => Vit_mono M U yInf hyInf hU α hα0 hα1 T A hLy n x hx))
    ⟨_, by rintro _ ⟨n, rfl⟩; exact (Vit_props M U yInf hyInf hU α hα0 hα1 T A hLy n).2.2 x hx⟩

lemma Lam_poly (M : Model) (U : ℤ) (T A : ℝ) (hLy : LyapOK M U T A) :
    ∃ A' B' : ℝ, ∀ x ≤ U, Lam T A (M.ρ + 1) x ≤ A' + B' * |(x:ℝ)| ^ (M.ρ + 3) := by
  obtain ⟨hT, hA, _⟩ := hLy
  refine ⟨A * 2 ^ M.ρ * (|T| ^ (M.ρ + 1) + 1), A * 2 ^ M.ρ, fun x hx => ?_⟩
  have hxU : (x:ℝ) ≤ U := by exact_mod_cast hx
  have hb0 : (0:ℝ) ≤ M.b := Nat.cast_nonneg _
  have h1 : T - x ≤ |T| + |(x:ℝ)| := by
    have := le_abs_self T; have := neg_abs_le (x:ℝ); linarith
  have h2 : (T - x) ^ (M.ρ + 1) ≤ (|T| + |(x:ℝ)|) ^ (M.ρ + 1) := pow_le_pow_left₀ (by linarith) h1 _
  have h3 := add_pow_le (abs_nonneg T) (abs_nonneg (x:ℝ)) (M.ρ + 1)
  have h4 : |(x:ℝ)| ^ (M.ρ + 1) ≤ 1 + |(x:ℝ)| ^ (M.ρ + 3) := by
    rcases le_or_gt |(x:ℝ)| 1 with h | h
    · have : |(x:ℝ)| ^ (M.ρ + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) h
      have : 0 ≤ |(x:ℝ)| ^ (M.ρ + 3) := by positivity
      linarith
    · have : |(x:ℝ)| ^ (M.ρ + 1) ≤ |(x:ℝ)| ^ (M.ρ + 3) := pow_le_pow_right₀ h.le (by omega)
      linarith
  simp only [Nat.add_sub_cancel] at h3
  unfold Lam
  calc A * (T - x) ^ (M.ρ + 1) ≤ A * (2 ^ M.ρ * (|T| ^ (M.ρ + 1) + |(x:ℝ)| ^ (M.ρ + 1))) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) hA.le
    _ ≤ A * (2 ^ M.ρ * (|T| ^ (M.ρ + 1) + (1 + |(x:ℝ)| ^ (M.ρ + 3)))) := by gcongr
    _ = _ := by ring

lemma R_tendsto (M : Model) (U yInf : ℤ) (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf)
    (hU : yInf ≤ U) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (T A : ℝ) (hLy : LyapOK M U T A)
    (y : ℤ) (hy : y ≤ U) :
    Tendsto (fun n => R M (fun z => α * Vit M U α n z) y) atTop
      (𝓝 (R M (fun z => α * Vlim M U α z) y)) := by
  have P := fun m => Vit_props M U yInf hyInf hU α hα0 hα1 T A hLy m
  set K' := (M.G U + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (U - j)) / (1 - α) with hK'
  have hb : Summable (fun j : ℕ => M.p j * Lam T A (M.ρ + 1) (y - j) + M.p j * K') :=
    (Lam_summ M U T A hLy y (by omega)).add (M.p_sum.summable.mul_right _)
  have hbd : ∀ n (j : ℕ), ‖M.p j * (α * Vit M U α n (y - j))‖
      ≤ M.p j * Lam T A (M.ρ + 1) (y - j) + M.p j * K' := by
    intro n j
    have hyj : y - (j:ℤ) ≤ U := by omega
    have h0 := (P n).2.1 (y - j) hyj
    have h1 := (P n).2.2 (y - j) hyj
    have hp := M.p_nonneg j
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (mul_nonneg hα0.le h0))]
    have h2 : α * Vit M U α n (y - j) ≤ Lam T A (M.ρ + 1) (y - j) + K' := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hp]
  have := tendsto_tsum_of_dominated_convergence
    (f := fun n (j : ℕ) => M.p j * (α * Vit M U α n (y - j)))
    (g := fun j => M.p j * (α * Vlim M U α (y - j))) hb
    (fun j => ((Vit_tendsto M U yInf hyInf hU α hα0 hα1 T A hLy (y - j) (by omega)).const_mul α).const_mul (M.p j))
    (Filter.Eventually.of_forall hbd)
  unfold R
  exact this.const_add _

theorem F1 (M : Model) (U yInf : ℤ) (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf)
    (hU : yInf ≤ U) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (T A : ℝ) (hLy : LyapOK M U T A) :
    ∃ V : ℤ → ℝ, InV M U yInf V ∧ (∀ x ≤ U, 0 ≤ V x) ∧
      (∀ x ≤ U, V x ≤ Lam T A (M.ρ + 1) x
        + (M.G U + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (U - j)) / (1 - α)) ∧
      ∀ x ≤ U, (∀ y, x ≤ y → y ≤ x + M.b → y ≤ U → V x ≤ R M (fun z => α * V z) y) ∧
        ∃ y, x ≤ y ∧ y ≤ x + M.b ∧ y ≤ U ∧ V x = R M (fun z => α * V z) y := by
  have P := fun m => Vit_props M U yInf hyInf hU α hα0 hα1 T A hLy m
  set K' := (M.G U + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (U - j)) / (1 - α) with hK'
  have hT := fun x hx => Vit_tendsto M U yInf hyInf hU α hα0 hα1 T A hLy x hx
  have hbnd : ∀ x ≤ U, 0 ≤ Vlim M U α x ∧ Vlim M U α x ≤ Lam T A (M.ρ + 1) x + K' :=
    fun x hx => ⟨ge_of_tendsto' (hT x hx) (fun n => (P n).2.1 x hx),
      le_of_tendsto' (hT x hx) (fun n => (P n).2.2 x hx)⟩
  have hK'0 : 0 ≤ K' := by
    have := (hbnd U le_rfl).1
    have := (hbnd U le_rfl).2
    have : 0 ≤ (M.G U + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (U - j)) := by
      have := M.G_nonneg U
      have : 0 ≤ ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (U - j) :=
        tsum_nonneg (fun j => mul_nonneg (M.p_nonneg j) (Lam_nonneg M U T A hLy _ (by omega)))
      linarith
    exact div_nonneg this (by linarith)
  refine ⟨Vlim M U α, ⟨?_, ?_, ?_⟩, fun x hx => (hbnd x hx).1, fun x hx => (hbnd x hx).2, fun x hx => ?_⟩
  · obtain ⟨A', B', hAB⟩ := Lam_poly M U T A hLy
    refine ⟨A' + K', B', fun x hx => ?_⟩
    rw [abs_of_nonneg (hbnd x hx).1]
    linarith [(hbnd x hx).2, hAB x hx]
  · intro x hx
    exact le_of_tendsto_of_tendsto' (hT (x + 1) (by omega)) (hT x (by omega)) (fun n => (P n).1.2.1 x hx)
  · intro x hx
    exact le_of_tendsto_of_tendsto' ((hT x (by omega)).sub (hT (x - 1) (by omega)))
      ((hT (x + 1) hx).sub (hT x (by omega))) (fun n => (P n).1.2.2 x hx)
  · have hRT := fun y hy => R_tendsto M U yInf hyInf hU α hα0 hα1 T A hLy y hy
    have hSP := fun n => S_props M U yInf hyInf hU _ (InV_smul M U yInf _ (P n).1 α hα0.le)
      (summ_of_InV M U yInf _ (InV_smul M U yInf _ (P n).1 α hα0.le)) x hx
    have hT1 : Tendsto (fun n => Vit M U α (n + 1) x) atTop (𝓝 (Vlim M U α x)) :=
      (hT x hx).comp (tendsto_add_atTop_nat 1)
    have hle : ∀ y, x ≤ y → y ≤ x + M.b → y ≤ U → Vlim M U α x ≤ R M (fun z => α * Vlim M U α z) y :=
      fun y h1 h2 h3 => le_of_tendsto_of_tendsto' hT1 (hRT y h3) (fun n => (hSP n).1 y h1 h2 h3)
    refine ⟨hle, ?_⟩
    set Yx := (Finset.Icc x (x + M.b)).filter (fun y => y ≤ U) with hYx
    have hne : Yx.Nonempty := ⟨x, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨le_rfl, by omega⟩, hx⟩⟩
    obtain ⟨y₀, hy₀, hmin⟩ := Yx.exists_min_image (fun y => R M (fun z => α * Vlim M U α z) y) hne
    have hy₀' := Finset.mem_filter.1 hy₀
    have hy₀I := Finset.mem_Icc.1 hy₀'.1
    refine ⟨y₀, hy₀I.1, hy₀I.2, hy₀'.2, le_antisymm (hle y₀ hy₀I.1 hy₀I.2 hy₀'.2) ?_⟩
    by_contra hcon0
    have hcon := not_le.1 hcon0
    set ε := R M (fun z => α * Vlim M U α z) y₀ - Vlim M U α x with hε
    have hε0 : 0 < ε := by linarith
    have hev : ∀ᶠ n in atTop, ∀ y ∈ Yx, Vlim M U α x + ε / 2 < R M (fun z => α * Vit M U α n z) y := by
      rw [eventually_all_finset]
      intro y hy
      have hy' := Finset.mem_filter.1 hy
      have h1 : Vlim M U α x + ε / 2 < R M (fun z => α * Vlim M U α z) y := by
        have := hmin y hy; linarith
      exact (hRT y hy'.2).eventually (lt_mem_nhds h1)
    obtain ⟨n, hn⟩ := hev.exists
    obtain ⟨y, h1, h2, h3, heq⟩ := (hSP n).2
    have hyY : y ∈ Yx := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨h1, h2⟩, h3⟩
    have h4 := hn y hyY
    have hVle : Vit M U α (n + 1) x ≤ Vlim M U α x :=
      (monotone_nat_of_le_succ (fun m => Vit_mono M U yInf hyInf hU α hα0 hα1 T A hLy m x hx)).ge_of_tendsto
        (hT x hx) (n + 1)
    have h5 : Vit M U α (n + 1) x = R M (fun z => α * Vit M U α n z) y := heq
    linarith

noncomputable def Dseq (c q : ℝ) : ℕ → ℝ
  | 0 => 0
  | d + 1 => (Dseq c q d + c) / q

lemma Dseq_nonneg (c q : ℝ) (hc : 0 ≤ c) (hq : 0 < q) : ∀ d, 0 ≤ Dseq c q d
  | 0 => le_rfl
  | d + 1 => by
    have := Dseq_nonneg c q hc hq d
    show 0 ≤ (Dseq c q d + c) / q
    positivity

lemma Dseq_mono (c q : ℝ) (hc : 0 ≤ c) (hq : 0 < q) (hq1 : q ≤ 1) : Monotone (Dseq c q) := by
  apply monotone_nat_of_le_succ
  intro d
  have h0 := Dseq_nonneg c q hc hq d
  show Dseq c q d ≤ (Dseq c q d + c) / q
  rw [le_div_iff₀ hq]
  nlinarith

lemma anti_below_le (f : ℤ → ℝ) (yInf : ℤ) (hm : ∀ x, x < yInf → f (x + 1) ≤ f x) :
    ∀ x ≤ yInf, f yInf ≤ f x := by
  have key : ∀ k : ℕ, f yInf ≤ f (yInf - k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := hm (yInf - ((k + 1 : ℕ) : ℤ)) (by push_cast; omega)
      have e : yInf - ((k + 1 : ℕ) : ℤ) + 1 = yInf - k := by push_cast; ring
      rw [e] at h
      exact le_trans ih h
  intro x hx
  have := key (yInf - x).toNat
  rwa [Int.toNat_of_nonneg (by omega), show yInf - (yInf - x) = x by ring] at this

lemma p0_lt_one (M : Model) : M.p 0 < 1 := by
  by_contra h
  have h1 : 1 ≤ M.p 0 := not_lt.1 h
  have hz : ∀ j, j ≠ 0 → M.p j = 0 := by
    intro j hj
    have := sum_le_hasSum ({0, j} : Finset ℕ) (fun i _ => M.p_nonneg i) M.p_sum
    rw [Finset.sum_pair (Ne.symm hj)] at this
    linarith [M.p_nonneg j]
  have h2 : (fun j : ℕ => (j:ℝ) * M.p j) = fun _ => 0 := by
    funext j
    by_cases hj : j = 0
    · simp [hj]
    · simp [hz j hj]
  have h3 := M.mean_pos
  rw [h2, tsum_zero] at h3
  exact lt_irrefl _ h3

theorem F2 (M : Model) (U yInf : ℤ) (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf)
    (hU : yInf ≤ U) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (T A : ℝ) (hLy : LyapOK M U T A)
    (V : ℤ → ℝ) (hV : InV M U yInf V) (hV0 : ∀ x ≤ U, 0 ≤ V x)
    (hVb : ∀ x ≤ U, V x ≤ Lam T A (M.ρ + 1) x
        + (M.G U + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (U - j)) / (1 - α))
    (hB : ∀ x ≤ U, (∀ y, x ≤ y → y ≤ x + M.b → y ≤ U → V x ≤ R M (fun z => α * V z) y) ∧
        ∃ y, x ≤ y ∧ y ≤ x + M.b ∧ y ≤ U ∧ V x = R M (fun z => α * V z) y) :
    ∃ m : ℝ, 0 ≤ m ∧ (∀ x ≤ U, m ≤ V x) ∧
      (1 - α) * m ≤ Lam T A (M.ρ + 1) yInf + (M.G U + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (U - j)) ∧
      ∀ x ≤ U, V x - m ≤ Lam T A (M.ρ + 1) x +
        Dseq (∑ z ∈ Finset.Icc yInf U, (M.G z + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (z - j)))
          (1 - M.p 0) (U - yInf).toNat := by
  set K := M.G U + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (U - j) with hK
  set c := ∑ z ∈ Finset.Icc yInf U, (M.G z + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (z - j)) with hc
  set q := 1 - M.p 0 with hq
  have hq0 : 0 < q := by have := p0_lt_one M; linarith
  have hq1 : q ≤ 1 := by have := M.p_nonneg 0; linarith
  have hcz_nonneg : ∀ z ∈ Finset.Icc yInf U,
      0 ≤ M.G z + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (z - j) := by
    intro z hz
    have hzU := (Finset.mem_Icc.1 hz).2
    have := M.G_nonneg z
    have : 0 ≤ ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (z - j) :=
      tsum_nonneg (fun j => mul_nonneg (M.p_nonneg j) (Lam_nonneg M U T A hLy _ (by omega)))
    linarith
  have hcz : ∀ z, yInf ≤ z → z ≤ U → M.G z + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (z - j) ≤ c :=
    fun z h1 h2 => Finset.single_le_sum (f := fun z => M.G z + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (z - j))
      hcz_nonneg (Finset.mem_Icc.2 ⟨h1, h2⟩)
  have hc0 : 0 ≤ c := Finset.sum_nonneg hcz_nonneg
  have hVs := summ_of_InV M U yInf V hV
  have hs1 := M.p_sum.summable
  have hRe : ∀ y, R M (fun z => α * V z) y = M.G y + α * ∑' j : ℕ, M.p j * V (y - j) := by
    intro y; unfold R; rw [← tsum_mul_left]; congr 1; congr 1; funext j; ring
  obtain ⟨z₀, hz₀, hzmin⟩ := (Finset.Icc yInf U).exists_min_image V ⟨yInf, Finset.mem_Icc.2 ⟨le_rfl, hU⟩⟩
  have hz₀I := Finset.mem_Icc.1 hz₀
  set m := V z₀ with hm
  have hmin : ∀ x ≤ U, m ≤ V x := by
    intro x hx
    by_cases h : yInf ≤ x
    · exact hzmin x (Finset.mem_Icc.2 ⟨h, hx⟩)
    · exact le_trans (hzmin yInf (Finset.mem_Icc.2 ⟨le_rfl, hU⟩)) (anti_below_le V yInf hV.2.1 x (by omega))
  have hm0 : 0 ≤ m := hV0 z₀ hz₀I.2
  obtain ⟨ys, hys1, hys2, hysU, hyseq⟩ := (hB z₀ hz₀I.2).2
  have hwin : ∀ x, ys - M.b ≤ x → x ≤ ys → V x ≤ m := by
    intro x h1 h2
    have := (hB x (by omega)).1 ys h2 (by omega) hysU
    rw [hm, hyseq]; exact this
  -- lower region: V - m ≤ Lam on x ≤ ys
  set u : ℤ → ℝ := fun x => V x - m - Lam T A (M.ρ + 1) x with hu
  have hubdd : BddAbove (Set.range (fun x : {x : ℤ // x ≤ ys} => u x)) := by
    refine ⟨K / (1 - α), ?_⟩
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have := hVb x (by omega)
    simp only [hu]
    linarith
  set S := sSup (Set.range (fun x : {x : ℤ // x ≤ ys} => u x)) with hS
  have huS : ∀ x ≤ ys, u x ≤ S := fun x hx => le_csSup hubdd ⟨⟨x, hx⟩, rfl⟩
  have hstep : ∀ x ≤ ys, u x ≤ max 0 (α * S) := by
    intro x hx
    by_cases hxw : ys - M.b ≤ x
    · have h1 := hwin x hxw hx
      have h2 := Lam_nonneg M U T A hLy x (by omega)
      have := le_max_left 0 (α * S)
      simp only [hu]
      linarith
    · have hxb : x + M.b ≤ U := by omega
      have hxU : x ≤ U := by omega
      have hb1 := (hB x hxU).1 (x + M.b) (by omega) le_rfl hxb
      rw [hRe] at hb1
      have hL := hLy.2.2 x hxU
      have hsL := hL.1
      have hsV := hVs (x + M.b) hxb
      have hsum3 : Summable (fun j : ℕ => M.p j * u (x + M.b - j)) :=
        ((hsV.sub (hs1.mul_right m)).sub hsL).congr (fun j => by simp only [hu]; ring)
      have h1 : ∑' j : ℕ, M.p j * u (x + M.b - j) ≤ ∑' j : ℕ, M.p j * S :=
        Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (huS _ (by omega)) (M.p_nonneg j))
          hsum3 (hs1.mul_right S)
      rw [tsum_mul_right, M.p_sum.tsum_eq, one_mul] at h1
      have h2 : ∑' j : ℕ, M.p j * u (x + M.b - j) = ∑' j : ℕ, M.p j * V (x + M.b - j) - m
          - ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (x + M.b - j) := by
        rw [show (fun j : ℕ => M.p j * u (x + M.b - j)) = fun j : ℕ => (M.p j * V (x + M.b - j) - M.p j * m)
            - M.p j * Lam T A (M.ρ + 1) (x + M.b - j) from funext (fun j => by simp only [hu]; ring)]
        rw [Summable.tsum_sub (hsV.sub (hs1.mul_right m)) hsL, Summable.tsum_sub hsV (hs1.mul_right m),
          tsum_mul_right, M.p_sum.tsum_eq, one_mul]
      have hEL : 0 ≤ ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (x + M.b - j) :=
        tsum_nonneg (fun j => mul_nonneg (M.p_nonneg j) (Lam_nonneg M U T A hLy _ (by omega)))
      have hE : ∑' j : ℕ, M.p j * V (x + M.b - j) - m - ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (x + M.b - j) ≤ S := by
        linarith
      have h3 := mul_le_mul_of_nonneg_left hE hα0.le
      have h4 : 0 ≤ (1 - α) * (m + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (x + M.b - j)) :=
        mul_nonneg (by linarith) (by linarith)
      have : u x ≤ α * S := by
        simp only [hu]
        nlinarith [hL.2, hb1]
      exact le_trans this (le_max_right _ _)
  have hS0 : S ≤ 0 := by
    have hle : S ≤ max 0 (α * S) := csSup_le ⟨u ys, ⟨⟨ys, le_rfl⟩, rfl⟩⟩
      (by rintro _ ⟨⟨x, hx⟩, rfl⟩; exact hstep x hx)
    by_contra h
    have h0 : 0 < S := not_le.1 h
    have : α * S < S := by nlinarith
    have : max 0 (α * S) < S := max_lt h0 this
    linarith
  have hlow : ∀ x ≤ ys, V x - m ≤ Lam T A (M.ρ + 1) x := by
    intro x hx
    have := le_trans (huS x hx) hS0
    simp only [hu] at this
    linarith
  -- upper region
  have hys_min : ∀ z ≤ U, V ys ≤ V z := fun z hz => le_trans (hwin ys (by omega) le_rfl) (hmin z hz)
  have hmono := FZ9.conv_mono_above (f := V) (U := U) hV.2.2 hys_min hysU
  have hup : ∀ d : ℕ, ∀ x, x = ys + d → x ≤ U → V x - m ≤ Dseq c q d := by
    intro d
    induction d with
    | zero =>
      intro x hx hxU
      have := hwin x (by push_cast at hx; omega) (by push_cast at hx; omega)
      show V x - m ≤ 0
      linarith
    | succ d ih =>
      intro x hx hxU
      push_cast at hx
      have ih' := ih (x - 1) (by omega) (by omega)
      have hb1 := (hB x hxU).1 x le_rfl (by omega) hxU
      rw [hRe] at hb1
      have hsV := hVs x hxU
      have hsL := Lam_summ M U T A hLy x (by omega)
      have hVx : 0 ≤ V x - m := by have := hmin x hxU; linarith
      have hx1 : 0 ≤ V (x - 1) - m := by have := hmin (x - 1) (by omega); linarith
      have hterm : ∀ j : ℕ, M.p j * (V (x - j) - m) ≤
          ((if j = 0 then M.p 0 * (V x - m) else 0) + M.p j * (V (x - 1) - m))
            + M.p j * Lam T A (M.ρ + 1) (x - j) := by
        intro j
        have hp := M.p_nonneg j
        have hLj := Lam_nonneg M U T A hLy (x - j) (by omega)
        by_cases hj : j = 0
        · subst hj
          simp only [if_true, Nat.cast_zero, sub_zero] at hLj ⊢
          have := mul_nonneg hp hx1
          have := mul_nonneg hp hLj
          linarith
        · simp only [hj, if_false, zero_add]
          by_cases hxj : ys ≤ x - j
          · have := hmono (x - j) (x - 1) hxj (by omega) (by omega)
            nlinarith
          · have := hlow (x - j) (by omega)
            nlinarith
      have hsI : Summable (fun j : ℕ => if j = 0 then M.p 0 * (V x - m) else 0) := by
        apply summable_of_ne_finset_zero (s := {0})
        intro j hj
        simp only [Finset.mem_singleton] at hj
        simp [hj]
      have hsLHS : Summable (fun j : ℕ => M.p j * (V (x - j) - m)) :=
        (hsV.sub (hs1.mul_right m)).congr (fun j => by ring)
      have hT := Summable.tsum_le_tsum hterm hsLHS ((hsI.add (hs1.mul_right _)).add hsL)
      rw [Summable.tsum_add (hsI.add (hs1.mul_right _)) hsL, Summable.tsum_add hsI (hs1.mul_right _),
        tsum_ite_eq, tsum_mul_right, M.p_sum.tsum_eq, one_mul] at hT
      have hL2 : ∑' j : ℕ, M.p j * (V (x - j) - m) = ∑' j : ℕ, M.p j * V (x - j) - m := by
        rw [show (fun j : ℕ => M.p j * (V (x - j) - m)) = fun j : ℕ => M.p j * V (x - j) - M.p j * m
          from funext (fun j => by ring), Summable.tsum_sub hsV (hs1.mul_right m), tsum_mul_right,
          M.p_sum.tsum_eq, one_mul]
      rw [hL2] at hT
      have hEnn : 0 ≤ ∑' j : ℕ, M.p j * V (x - j) - m := by
        rw [← hL2]
        exact tsum_nonneg (fun j => mul_nonneg (M.p_nonneg j) (by have := hmin (x - j) (by omega); linarith))
      have hcx := hcz x (by omega) hxU
      have h5 : α * ∑' j : ℕ, M.p j * V (x - j) - m ≤ ∑' j : ℕ, M.p j * V (x - j) - m := by
        nlinarith
      show V x - m ≤ (Dseq c q d + c) / q
      rw [le_div_iff₀ hq0]
      have : q * (V x - m) = V x - m - M.p 0 * (V x - m) := by rw [hq]; ring
      nlinarith
  refine ⟨m, hm0, hmin, ?_, fun x hx => ?_⟩
  · have h1 := hmin yInf hU
    have h2 := hVb yInf hU
    have h3 := Lam_nonneg M U T A hLy yInf (by omega)
    have hK0 : 0 ≤ K := by
      have := hcz U hU le_rfl
      have := M.G_nonneg U
      have : 0 ≤ ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (U - j) :=
        tsum_nonneg (fun j => mul_nonneg (M.p_nonneg j) (Lam_nonneg M U T A hLy _ (by omega)))
      linarith
    have hne : (1 - α) ≠ 0 := (by linarith : (0:ℝ) < 1 - α).ne'
    have h4 : (1 - α) * (K / (1 - α)) = K := by rw [mul_comm]; exact div_mul_cancel₀ K hne
    have h5 : (1 - α) * m ≤ (1 - α) * (Lam T A (M.ρ + 1) yInf + K / (1 - α)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  · have hD0 := Dseq_nonneg c q hc0 hq0 (U - yInf).toNat
    by_cases hx' : x ≤ ys
    · have := hlow x hx'
      linarith
    · have hxy : 0 ≤ x - ys := by omega
      have h1 := hup (x - ys).toNat x (by rw [Int.toNat_of_nonneg hxy]; ring) hx
      have h2 := Dseq_mono c q hc0 hq0 hq1 (Int.toNat_le_toNat (show x - ys ≤ U - yInf by omega))
      have := Lam_nonneg M U T A hLy x (by omega)
      linarith

lemma lyapOK_exists (M : Model) (U : ℤ) (T₀ : ℝ) : ∃ T A : ℝ, LyapOK M U T A ∧ T₀ ≤ T := by
  obtain ⟨AG, BG, hAG, hBG, hG⟩ := M.G_growth
  obtain ⟨k, hk⟩ : ∃ k, M.ρ = k + 1 := ⟨M.ρ - 1, by have := M.ρ_pos; omega⟩
  obtain ⟨T, A, hT, hT0, hA, hL⟩ := FZL.lyap M (FZ9.moments_finite M) U k AG BG T₀ hAG.le hBG.le
  refine ⟨T, A, ⟨hT, hA, fun x hx => ?_⟩, hT0⟩
  obtain ⟨h1, h2⟩ := hL x hx
  have e : M.ρ + 1 = k + 2 := by omega
  unfold Lam
  rw [e]
  refine ⟨h1, ?_⟩
  have := hG (x + M.b)
  rw [hk] at this
  push_cast at this h2 ⊢
  linarith

lemma R_shift (M : Model) (U yInf : ℤ) (α m : ℝ) (V : ℤ → ℝ) (hV : InV M U yInf V) (y : ℤ) (hy : y ≤ U) :
    R M (fun z => α * V z) y = M.G y + α * (∑' j : ℕ, M.p j * (V (y - j) - m)) + α * m := by
  have hs := summ_of_InV M U yInf V hV y hy
  have hs1 := M.p_sum.summable
  unfold R
  have e1 : ∑' j : ℕ, M.p j * (α * V (y - j)) = α * ∑' j : ℕ, M.p j * V (y - j) := by
    rw [← tsum_mul_left]; congr 1; funext j; ring
  have e2 : ∑' j : ℕ, M.p j * (V (y - j) - m) = ∑' j : ℕ, M.p j * V (y - j) - m := by
    rw [show (fun j : ℕ => M.p j * (V (y - j) - m)) = fun j : ℕ => M.p j * V (y - j) - M.p j * m
      from funext (fun j => by ring), Summable.tsum_sub hs (hs1.mul_right m), tsum_mul_right,
      M.p_sum.tsum_eq, one_mul]
  rw [e1, e2]
  ring

theorem F3 (M : Model) (U yInf : ℤ) (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf)
    (hU : yInf ≤ U) (T A : ℝ) (hLy : LyapOK M U T A) :
    ∃ (g : ℝ) (v : ℤ → ℝ) (D : ℝ), 0 ≤ g ∧ InV M U yInf v ∧
      (∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j))) ∧ OptEq M U g v ∧
      ∀ x ≤ U, 0 ≤ v x ∧ v x ≤ Lam T A (M.ρ + 1) x + D := by
  set K := M.G U + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (U - j) with hK
  set D := Dseq (∑ z ∈ Finset.Icc yInf U, (M.G z + ∑' j : ℕ, M.p j * Lam T A (M.ρ + 1) (z - j)))
          (1 - M.p 0) (U - yInf).toNat with hD
  set Gb := Lam T A (M.ρ + 1) yInf + K with hGb
  set α : ℕ → ℝ := fun k => 1 - 1 / ((k:ℝ) + 2) with hαdef
  have hα0 : ∀ k, 0 < α k := by
    intro k
    have : 1 / ((k:ℝ) + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    simp only [hαdef]; linarith
  have hα1 : ∀ k, α k < 1 := by
    intro k
    have : 0 < 1 / ((k:ℝ) + 2) := by positivity
    simp only [hαdef]; linarith
  have hF1 := fun k => F1 M U yInf hyInf hU (α k) (hα0 k) (hα1 k) T A hLy
  choose V hVI hV0 hVb hVB using hF1
  have hF2 := fun k => F2 M U yInf hyInf hU (α k) (hα0 k) (hα1 k) T A hLy (V k) (hVI k) (hV0 k) (hVb k) (hVB k)
  choose m hm0 hmin hgm hhm using hF2
  set Hb : ℤ → ℝ := fun x => if x ≤ U then Lam T A (M.ρ + 1) x + D else 0 with hHb
  set seq : ℕ → ℝ × (ℤ → ℝ) := fun k => ((1 - α k) * m k, fun x => if x ≤ U then V k x - m k else 0)
    with hseq
  have hcpt : IsCompact (Set.Icc (0:ℝ) Gb ×ˢ Set.pi Set.univ (fun x => Set.Icc (0:ℝ) (Hb x))) :=
    isCompact_Icc.prod (isCompact_univ_pi (fun x => isCompact_Icc))
  have hmem : ∀ k, seq k ∈ Set.Icc (0:ℝ) Gb ×ˢ Set.pi Set.univ (fun x => Set.Icc (0:ℝ) (Hb x)) := by
    intro k
    refine ⟨⟨mul_nonneg (by linarith [hα1 k]) (hm0 k), hgm k⟩, fun x _ => ?_⟩
    simp only [hHb, hseq]
    split_ifs with hx
    · exact ⟨by linarith [hmin k x hx], hhm k x hx⟩
    · exact ⟨le_rfl, le_rfl⟩
  obtain ⟨⟨g, h⟩, _, φ, hφ, hlim⟩ := hcpt.tendsto_subseq hmem
  have hg_lim : Tendsto (fun k => (1 - α (φ k)) * m (φ k)) atTop (𝓝 g) :=
    ((continuous_fst.tendsto _).comp hlim : _)
  have hh_lim : ∀ x, Tendsto (fun k => (seq (φ k)).2 x) atTop (𝓝 (h x)) := fun x =>
    ((continuous_apply x).tendsto _).comp ((continuous_snd.tendsto _).comp hlim)
  have hhx : ∀ x ≤ U, Tendsto (fun k => V (φ k) x - m (φ k)) atTop (𝓝 (h x)) := by
    intro x hx
    have := hh_lim x
    simp only [hseq, if_pos hx] at this
    exact this
  have hinv : Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat
      (fun n => by positivity)
      (fun n => by
        apply one_div_le_one_div_of_le (by positivity)
        linarith)
  have hαlim : Tendsto (fun k => α (φ k)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1:ℝ))).sub (hinv.comp hφ.tendsto_atTop)
    simpa [hαdef] using this
  -- bounds on the limit
  have hbnd : ∀ x ≤ U, 0 ≤ h x ∧ h x ≤ Lam T A (M.ρ + 1) x + D := fun x hx =>
    ⟨ge_of_tendsto' (hhx x hx) (fun k => by linarith [hmin (φ k) x hx]),
     le_of_tendsto' (hhx x hx) (fun k => hhm (φ k) x hx)⟩
  -- convergence of the expectations
  have hE : ∀ y ≤ U, Tendsto (fun k => ∑' j : ℕ, M.p j * (V (φ k) (y - j) - m (φ k))) atTop
      (𝓝 (∑' j : ℕ, M.p j * h (y - j))) := by
    intro y hy
    have hb : Summable (fun j : ℕ => M.p j * Lam T A (M.ρ + 1) (y - j) + M.p j * D) :=
      (Lam_summ M U T A hLy y (by omega)).add (M.p_sum.summable.mul_right _)
    refine tendsto_tsum_of_dominated_convergence (bound := fun j => M.p j * Lam T A (M.ρ + 1) (y - j) + M.p j * D)
      hb (fun j => (hhx (y - j) (by omega)).const_mul (M.p j)) (Filter.Eventually.of_forall (fun k j => ?_))
    have hyj : y - (j:ℤ) ≤ U := by omega
    have h0 : 0 ≤ V (φ k) (y - j) - m (φ k) := by linarith [hmin (φ k) (y - j) hyj]
    have h1 := hhm (φ k) (y - j) hyj
    have hp := M.p_nonneg j
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp h0)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hp]
  have hRk : ∀ y ≤ U, Tendsto (fun k => M.G y + α (φ k) * ∑' j : ℕ, M.p j * (V (φ k) (y - j) - m (φ k)))
      atTop (𝓝 (R M h y)) := by
    intro y hy
    have := tendsto_const_nhds (x := M.G y) |>.add (hαlim.mul (hE y hy))
    simpa [R] using this
  have hineq : ∀ k, ∀ x ≤ U, ∀ y, x ≤ y → y ≤ x + M.b → y ≤ U →
      (1 - α (φ k)) * m (φ k) + (V (φ k) x - m (φ k))
        ≤ M.G y + α (φ k) * ∑' j : ℕ, M.p j * (V (φ k) (y - j) - m (φ k)) := by
    intro k x hx y h1 h2 h3
    have := (hVB (φ k) x hx).1 y h1 h2 h3
    rw [R_shift M U yInf (α (φ k)) (m (φ k)) (V (φ k)) (hVI (φ k)) y h3] at this
    linarith
  have hlhs : ∀ x ≤ U, Tendsto (fun k => (1 - α (φ k)) * m (φ k) + (V (φ k) x - m (φ k))) atTop
      (𝓝 (g + h x)) := fun x hx => hg_lim.add (hhx x hx)
  refine ⟨g, h, D, ge_of_tendsto' hg_lim (fun k => mul_nonneg (by linarith [hα1 (φ k)]) (hm0 (φ k))),
    ⟨?_, ?_, ?_⟩, ?_, ?_, hbnd⟩
  · obtain ⟨A', B', hAB⟩ := Lam_poly M U T A hLy
    refine ⟨A' + |D|, B', fun x hx => ?_⟩
    rw [abs_of_nonneg (hbnd x hx).1]
    linarith [(hbnd x hx).2, hAB x hx, le_abs_self D]
  · intro x hx
    exact le_of_tendsto_of_tendsto' (hhx (x + 1) (by omega)) (hhx x (by omega))
      (fun k => by have := (hVI (φ k)).2.1 x hx; linarith)
  · intro x hx
    exact le_of_tendsto_of_tendsto' ((hhx x (by omega)).sub (hhx (x - 1) (by omega)))
      ((hhx (x + 1) hx).sub (hhx x (by omega)))
      (fun k => by have := (hVI (φ k)).2.2 x hx; linarith)
  · intro y hy
    refine Summable.of_norm_bounded ((Lam_summ M U T A hLy y (by omega)).add (M.p_sum.summable.mul_right D)) (fun j => ?_)
    have hyj : y - (j:ℤ) ≤ U := by omega
    have hp := M.p_nonneg j
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (hbnd _ hyj).1)]
    nlinarith [mul_le_mul_of_nonneg_left (hbnd _ hyj).2 hp]
  · intro x hx
    have hle : ∀ y, x ≤ y → y ≤ x + M.b → y ≤ U → g + h x ≤ R M h y := fun y h1 h2 h3 =>
      le_of_tendsto_of_tendsto' (hlhs x hx) (hRk y h3) (fun k => hineq k x hx y h1 h2 h3)
    refine ⟨hle, ?_⟩
    set Yx := (Finset.Icc x (x + M.b)).filter (fun y => y ≤ U) with hYx
    have hne : Yx.Nonempty := ⟨x, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨le_rfl, by omega⟩, hx⟩⟩
    obtain ⟨y₀, hy₀, hmin0⟩ := Yx.exists_min_image (fun y => R M h y) hne
    have hy₀' := Finset.mem_filter.1 hy₀
    have hy₀I := Finset.mem_Icc.1 hy₀'.1
    refine ⟨y₀, hy₀I.1, hy₀I.2, hy₀'.2, le_antisymm (hle y₀ hy₀I.1 hy₀I.2 hy₀'.2) ?_⟩
    by_contra hcon0
    have hcon := not_le.1 hcon0
    set ε := R M h y₀ - (g + h x) with hε
    have hε0 : 0 < ε := by linarith
    have hev1 : ∀ᶠ k in atTop, ∀ y ∈ Yx, g + h x + ε / 2 <
        M.G y + α (φ k) * ∑' j : ℕ, M.p j * (V (φ k) (y - j) - m (φ k)) := by
      rw [eventually_all_finset]
      intro y hy
      have hy' := Finset.mem_filter.1 hy
      have h1 : g + h x + ε / 2 < R M h y := by have := hmin0 y hy; linarith
      exact (hRk y hy'.2).eventually (lt_mem_nhds h1)
    have hev2 : ∀ᶠ k in atTop, (1 - α (φ k)) * m (φ k) + (V (φ k) x - m (φ k)) < g + h x + ε / 2 :=
      (hlhs x hx).eventually (gt_mem_nhds (by linarith))
    obtain ⟨k, hk1, hk2⟩ := (hev1.and hev2).exists
    obtain ⟨y, h1, h2, h3, heq⟩ := (hVB (φ k) x hx).2
    have hyY : y ∈ Yx := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨h1, h2⟩, h3⟩
    have h4 := hk1 y hyY
    rw [R_shift M U yInf (α (φ k)) (m (φ k)) (V (φ k)) (hVI (φ k)) y h3] at heq
    linarith

end FZF

namespace FZE
open FedergruenZipkin.AvgCost

noncomputable def Py (M : Model) (y : ℤ) (f : ℤ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal (M.p j) * f (y - j)

lemma P_eq (M : Model) (δ : ℤ → ℤ) (f : ℤ → ℝ≥0∞) (x : ℤ) : P M δ f x = Py M (δ x) f := rfl

lemma psum1 (M : Model) : ∑' j : ℕ, ENNReal.ofReal (M.p j) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg M.p_nonneg M.p_sum.summable, M.p_sum.tsum_eq, ENNReal.ofReal_one]

lemma Py_mono (M : Model) (y : ℤ) (f f' : ℤ → ℝ≥0∞) (h : ∀ z ≤ y, f z ≤ f' z) :
    Py M y f ≤ Py M y f' :=
  ENNReal.tsum_le_tsum (fun j => by gcongr; exact h _ (by omega))

lemma Py_add (M : Model) (y : ℤ) (f f' : ℤ → ℝ≥0∞) :
    Py M y (fun z => f z + f' z) = Py M y f + Py M y f' := by
  unfold Py
  rw [← ENNReal.tsum_add]
  congr 1; funext j; ring

lemma Py_cmul (M : Model) (y : ℤ) (c : ℝ≥0∞) (f : ℤ → ℝ≥0∞) :
    Py M y (fun z => c * f z) = c * Py M y f := by
  unfold Py
  rw [← ENNReal.tsum_mul_left]
  congr 1; funext j; ring

lemma Py_const (M : Model) (y : ℤ) (c : ℝ≥0∞) : Py M y (fun _ => c) = c := by
  unfold Py
  rw [ENNReal.tsum_mul_right, psum1, one_mul]

lemma Py_ofReal (M : Model) (y : ℤ) (f : ℤ → ℝ) (hf : ∀ z ≤ y, 0 ≤ f z)
    (hs : Summable (fun j : ℕ => M.p j * f (y - j))) :
    Py M y (fun z => ENNReal.ofReal (f z)) = ENNReal.ofReal (∑' j : ℕ, M.p j * f (y - j)) := by
  unfold Py
  rw [ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (M.p_nonneg j) (hf _ (by omega))) hs]
  congr 1; funext j
  rw [ENNReal.ofReal_mul (M.p_nonneg j)]

lemma iter_mono (M : Model) (U : ℤ) (δ : ℤ → ℤ) (hδ : ∀ x ≤ U, δ x ≤ U) (t : ℕ)
    (f f' : ℤ → ℝ≥0∞) (h : ∀ z ≤ U, f z ≤ f' z) : ∀ x ≤ U, (P M δ)^[t] f x ≤ (P M δ)^[t] f' x := by
  induction t with
  | zero => exact h
  | succ t ih =>
    intro x hx
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', P_eq, P_eq]
    exact Py_mono M (δ x) _ _ (fun z hz => ih z (le_trans hz (hδ x hx)))

lemma iter_add_const (M : Model) (δ : ℤ → ℤ) (c : ℝ≥0∞) (f : ℤ → ℝ≥0∞) :
    ∀ t : ℕ, (P M δ)^[t] (fun z => c + f z) = fun z => c + (P M δ)^[t] f z
  | 0 => rfl
  | t + 1 => by
    funext x
    rw [Function.iterate_succ_apply', iter_add_const M δ c f t, Function.iterate_succ_apply', P_eq, P_eq,
      Py_add, Py_const]

lemma iter_add (M : Model) (δ : ℤ → ℤ) (f f' : ℤ → ℝ≥0∞) :
    ∀ t : ℕ, (P M δ)^[t] (fun z => f z + f' z) = fun z => (P M δ)^[t] f z + (P M δ)^[t] f' z
  | 0 => rfl
  | t + 1 => by
    funext x
    rw [Function.iterate_succ_apply', iter_add M δ f f' t, Function.iterate_succ_apply',
      Function.iterate_succ_apply', P_eq, P_eq, P_eq, Py_add]

lemma iter_cmul (M : Model) (δ : ℤ → ℤ) (c : ℝ≥0∞) (f : ℤ → ℝ≥0∞) :
    ∀ t : ℕ, (P M δ)^[t] (fun z => c * f z) = fun z => c * (P M δ)^[t] f z
  | 0 => rfl
  | t + 1 => by
    funext x
    rw [Function.iterate_succ_apply', iter_cmul M δ c f t, Function.iterate_succ_apply', P_eq, P_eq,
      Py_cmul]

lemma periodCost_const (M : Model) (δ : ℤ → ℤ) :
    ∀ i : ℕ, periodCost M (fun _ => δ) i = (P M δ)^[i] (fun z => ENNReal.ofReal (M.G (δ z)))
  | 0 => by funext x; rfl
  | i + 1 => by
    funext x
    rw [Function.iterate_succ_apply', ← periodCost_const M δ i]
    rfl

/-- average-cost verification for a stationary policy attaining the optimality equation, given a
Lyapunov function for `Δ_L` policies dominating the relative value function. -/
theorem F5 (M : Model) (U L : ℤ) (hLU : L + M.b ≤ U) (g : ℝ) (hg : 0 ≤ g) (v : ℤ → ℝ) (δ : ℤ → ℤ)
    (hfeas : Feasible M U δ) (hδL : ∀ x ≤ L, δ x = x + M.b) (ys : ℤ)
    (hmin : ∀ x ≤ U, v ys ≤ v x) (hsum : ∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j)))
    (hatt : ∀ x ≤ U, g + v x = R M v (δ x))
    (Φ : ℤ → ℝ) (hΦ0 : ∀ x ≤ U, 0 ≤ Φ x)
    (hΦ1 : ∀ x ≤ U, Summable (fun j : ℕ => M.p j * Φ (x + M.b - j)) ∧
      ∑' j : ℕ, M.p j * Φ (x + M.b - j) ≤ Φ x)
    (C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hΦ3 : ∀ y, L < y → y ≤ U → Summable (fun j : ℕ => M.p j * Φ (y - j)) ∧
      ∑' j : ℕ, M.p j * Φ (y - j) ≤ C₁)
    (hW : ∀ ε > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≤ U, v x - v ys ≤ ε * Φ x + C) :
    ∀ x ≤ U, Tendsto (fun t : ℕ => totalCost M (fun _ => δ) t x / (t : ℝ≥0∞)) atTop
      (𝓝 (ENNReal.ofReal g)) := by
  set Φt : ℤ → ℝ≥0∞ := fun z => ENNReal.ofReal (Φ z) with hΦt
  set W : ℤ → ℝ≥0∞ := fun z => ENNReal.ofReal (v z - v ys) with hWdef
  set f0 : ℤ → ℝ≥0∞ := fun z => ENNReal.ofReal (M.G (δ z)) with hf0
  have hδU : ∀ x ≤ U, δ x ≤ U := fun x hx => (hfeas x hx).2.2
  have hPΦ : ∀ x ≤ U, P M δ Φt x ≤ Φt x + ENNReal.ofReal C₁ := by
    intro x hx
    rw [P_eq]
    by_cases hxL : x ≤ L
    · rw [hδL x hxL]
      obtain ⟨hs, hle⟩ := hΦ1 x hx
      have := Py_ofReal M (x + M.b) Φ (fun z hz => hΦ0 z (by omega)) hs
      rw [this]
      exact le_trans (ENNReal.ofReal_le_ofReal hle) le_self_add
    · have h1 := (hfeas x hx).1
      obtain ⟨hs, hle⟩ := hΦ3 (δ x) (by omega) (hδU x hx)
      have := Py_ofReal M (δ x) Φ (fun z hz => hΦ0 z (by have := hδU x hx; omega)) hs
      rw [this]
      exact le_trans (ENNReal.ofReal_le_ofReal hle) le_add_self
  have hPΦt : ∀ t : ℕ, ∀ x ≤ U, (P M δ)^[t] Φt x ≤ Φt x + t * ENNReal.ofReal C₁ := by
    intro t
    induction t with
    | zero => intro x hx; simp
    | succ t ih =>
      intro x hx
      rw [Function.iterate_succ_apply', P_eq]
      calc Py M (δ x) ((P M δ)^[t] Φt) ≤ Py M (δ x) (fun z => Φt z + t * ENNReal.ofReal C₁) :=
            Py_mono _ _ _ _ (fun z hz => ih z (le_trans hz (hδU x hx)))
        _ = Py M (δ x) Φt + t * ENNReal.ofReal C₁ := by rw [Py_add, Py_const]
        _ ≤ Φt x + ENNReal.ofReal C₁ + t * ENNReal.ofReal C₁ := by
            gcongr
            exact hPΦ x hx
        _ = Φt x + ((t + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal C₁ := by push_cast; ring
  have hstep : ∀ x ≤ U, ENNReal.ofReal g + W x = f0 x + P M δ W x := by
    intro x hx
    have hδx := hδU x hx
    have hs := hsum (δ x) hδx
    have hs1 := M.p_sum.summable
    have hsw : Summable (fun j : ℕ => M.p j * (v (δ x - j) - v ys)) :=
      (hs.sub (hs1.mul_right (v ys))).congr (fun j => by ring)
    have hE : ∑' j : ℕ, M.p j * (v (δ x - j) - v ys) = ∑' j : ℕ, M.p j * v (δ x - j) - v ys := by
      rw [show (fun j : ℕ => M.p j * (v (δ x - j) - v ys)) = fun j : ℕ => M.p j * v (δ x - j) - M.p j * v ys
        from funext (fun j => by ring), Summable.tsum_sub hs (hs1.mul_right _), tsum_mul_right,
        M.p_sum.tsum_eq, one_mul]
    have hreal : g + (v x - v ys) = M.G (δ x) + ∑' j : ℕ, M.p j * (v (δ x - j) - v ys) := by
      have := hatt x hx
      unfold R at this
      rw [hE]
      linarith
    have hw0 : 0 ≤ v x - v ys := by linarith [hmin x hx]
    have hE0 : 0 ≤ ∑' j : ℕ, M.p j * (v (δ x - j) - v ys) :=
      tsum_nonneg (fun j => mul_nonneg (M.p_nonneg j) (by linarith [hmin (δ x - j) (by omega)]))
    have hPy := Py_ofReal M (δ x) (fun z => v z - v ys) (fun z hz => by linarith [hmin z (by omega)]) hsw
    rw [P_eq, hWdef, hPy, hf0]
    rw [← ENNReal.ofReal_add hg hw0, ← ENNReal.ofReal_add (M.G_nonneg _) hE0, hreal]
  have htel : ∀ t : ℕ, ∀ x ≤ U, (t : ℝ≥0∞) * ENNReal.ofReal g + W x
      = (∑ i ∈ Finset.range t, (P M δ)^[i] f0 x) + (P M δ)^[t] W x := by
    intro t
    induction t with
    | zero => intro x hx; simp
    | succ t ih =>
      intro x hx
      have h1 : (P M δ)^[t] (fun z => ENNReal.ofReal g + W z) x = (P M δ)^[t] (fun z => f0 z + P M δ W z) x := by
        apply le_antisymm
        · exact iter_mono M U δ hδU t _ _ (fun z hz => (hstep z hz).le) x hx
        · exact iter_mono M U δ hδU t _ _ (fun z hz => (hstep z hz).ge) x hx
      rw [iter_add_const, iter_add] at h1
      simp only at h1
      rw [← Function.iterate_succ_apply (P M δ) t W] at h1
      calc ((t + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal g + W x
          = ENNReal.ofReal g + ((t : ℝ≥0∞) * ENNReal.ofReal g + W x) := by push_cast; ring
        _ = ENNReal.ofReal g + ((∑ i ∈ Finset.range t, (P M δ)^[i] f0 x) + (P M δ)^[t] W x) := by
            rw [ih x hx]
        _ = (∑ i ∈ Finset.range t, (P M δ)^[i] f0 x) + (ENNReal.ofReal g + (P M δ)^[t] W x) := by ring
        _ = (∑ i ∈ Finset.range t, (P M δ)^[i] f0 x) + ((P M δ)^[t] f0 x + (P M δ)^[t.succ] W x) := by
            rw [h1]
        _ = _ := by rw [Finset.sum_range_succ]; ring
  have hPW : ∀ ε > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ, ∀ x ≤ U,
      (P M δ)^[t] W x ≤ ENNReal.ofReal (ε * (Φ x + t * C₁) + C) := by
    intro ε hε
    obtain ⟨C, hC0, hC⟩ := hW ε hε
    refine ⟨C, hC0, fun t x hx => ?_⟩
    have hWle : ∀ z ≤ U, W z ≤ ENNReal.ofReal C + ENNReal.ofReal ε * Φt z := by
      intro z hz
      calc W z ≤ ENNReal.ofReal (C + ε * Φ z) := ENNReal.ofReal_le_ofReal (by linarith [hC z hz])
        _ = _ := by rw [ENNReal.ofReal_add hC0 (mul_nonneg hε.le (hΦ0 z hz)), ENNReal.ofReal_mul hε.le]
    calc (P M δ)^[t] W x ≤ (P M δ)^[t] (fun z => ENNReal.ofReal C + ENNReal.ofReal ε * Φt z) x :=
          iter_mono M U δ hδU t _ _ hWle x hx
      _ = ENNReal.ofReal C + ENNReal.ofReal ε * (P M δ)^[t] Φt x := by rw [iter_add_const, iter_cmul]
      _ ≤ ENNReal.ofReal C + ENNReal.ofReal ε * (Φt x + t * ENNReal.ofReal C₁) := by
          gcongr
          exact hPΦt t x hx
      _ = _ := by
          rw [ENNReal.ofReal_add (by have := hΦ0 x hx; positivity) hC0, ENNReal.ofReal_mul hε.le,
            ENNReal.ofReal_add (hΦ0 x hx) (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
          ring
  -- final real analysis
  intro x hx
  have hw0 : 0 ≤ v x - v ys := by linarith [hmin x hx]
  have htot : ∀ t : ℕ, totalCost M (fun _ => δ) t x = ∑ i ∈ Finset.range t, (P M δ)^[i] f0 x := by
    intro t
    unfold totalCost
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [periodCost_const]
  have hWx : W x = ENNReal.ofReal (v x - v ys) := rfl
  have hfinT : ∀ t : ℕ, totalCost M (fun _ => δ) t x ≠ ⊤ := by
    intro t
    have h := htel t x hx
    rw [← htot] at h
    have : totalCost M (fun _ => δ) t x ≤ (t : ℝ≥0∞) * ENNReal.ofReal g + W x := by rw [h]; exact le_self_add
    exact ne_top_of_le_ne_top (by rw [hWx]; exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) (by simp), by simp⟩) this
  have hfinP : ∀ t : ℕ, (P M δ)^[t] W x ≠ ⊤ := by
    intro t
    have h := htel t x hx
    have : (P M δ)^[t] W x ≤ (t : ℝ≥0∞) * ENNReal.ofReal g + W x := by rw [h]; exact le_add_self
    exact ne_top_of_le_ne_top (by rw [hWx]; exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) (by simp), by simp⟩) this
  set a : ℕ → ℝ := fun t => (totalCost M (fun _ => δ) t x).toReal with ha
  set b : ℕ → ℝ := fun t => ((P M δ)^[t] W x).toReal with hb
  have hab : ∀ t : ℕ, (t : ℝ) * g + (v x - v ys) = a t + b t := by
    intro t
    have h := congrArg ENNReal.toReal (htel t x hx)
    rw [← htot, ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) (by simp)) (by rw [hWx]; simp),
      ENNReal.toReal_add (hfinT t) (hfinP t), ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal hg, hWx, ENNReal.toReal_ofReal hw0] at h
    exact h
  have hb0 : ∀ t, 0 ≤ b t := fun t => ENNReal.toReal_nonneg
  have hbB : ∀ ε > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ, b t ≤ ε * (Φ x + t * C₁) + C := by
    intro ε hε
    obtain ⟨C, hC0, hC⟩ := hPW ε hε
    refine ⟨C, hC0, fun t => ?_⟩
    exact ENNReal.toReal_le_of_le_ofReal (by have := hΦ0 x hx; positivity) (hC t x hx)
  have hreal : Tendsto (fun t : ℕ => a t / t) atTop (𝓝 g) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    set ε := η / (2 * (C₁ + 1)) with hε
    have hεpos : 0 < ε := by positivity
    obtain ⟨C, hC0, hC⟩ := hbB ε hεpos
    have hΦx := hΦ0 x hx
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * ((v x - v ys) + ε * Φ x + C) / η)
    refine ⟨max N 1, fun t ht => ?_⟩
    have ht1 : (1:ℝ) ≤ t := by exact_mod_cast le_trans (le_max_right _ _) ht
    have htN : (N:ℝ) ≤ t := by exact_mod_cast le_trans (le_max_left _ _) ht
    have htpos : (0:ℝ) < t := by linarith
    have e : a t / t - g = (a t - t * g) / t := by field_simp
    rw [Real.dist_eq, e, abs_div, abs_of_pos htpos, div_lt_iff₀ htpos]
    have h1 : a t - t * g = (v x - v ys) - b t := by linarith [hab t]
    rw [h1]
    have h2 := hC t
    have h3 : |(v x - v ys) - b t| ≤ (v x - v ys) + b t := by
      rw [abs_le]; constructor <;> linarith [hb0 t]
    have h4 : ε * C₁ ≤ η / 2 := by
      rw [hε, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h5 : 2 * ((v x - v ys) + ε * Φ x + C) < η * t := by
      rw [div_lt_iff₀ hη] at hN
      nlinarith
    have h6 : ε * (t * C₁) ≤ η / 2 * t := by nlinarith
    nlinarith
  have hcongr : ∀ᶠ t : ℕ in atTop, ENNReal.ofReal (a t / t) = totalCost M (fun _ => δ) t x / (t : ℝ≥0∞) := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    have htpos : (0:ℝ) < t := by exact_mod_cast ht
    rw [ENNReal.ofReal_div_of_pos htpos, ha, ENNReal.ofReal_toReal (hfinT t), ENNReal.ofReal_natCast]
  exact (ENNReal.tendsto_ofReal hreal).congr' hcongr

noncomputable def Ry (M : Model) (W : ℤ → ℝ≥0∞) (y : ℤ) : ℝ≥0∞ := ENNReal.ofReal (M.G y) + Py M y W

noncomputable def Yset (M : Model) (U x : ℤ) : Finset ℤ := (Finset.Icc x (x + M.b)).filter (fun y => y ≤ U)

lemma mem_Yset (M : Model) (U x y : ℤ) : y ∈ Yset M U x ↔ x ≤ y ∧ y ≤ x + M.b ∧ y ≤ U := by
  simp only [Yset, Finset.mem_filter, Finset.mem_Icc]
  tauto

noncomputable def TV (M : Model) (U : ℤ) (W : ℤ → ℝ≥0∞) (x : ℤ) : ℝ≥0∞ := (Yset M U x).inf (fun y => Ry M W y)

noncomputable def Wt (M : Model) (U : ℤ) : ℕ → ℤ → ℝ≥0∞
  | 0 => fun _ => 0
  | n + 1 => TV M U (Wt M U n)

lemma Py_zero (M : Model) (y : ℤ) : Py M y (fun _ => 0) = 0 := Py_const M y 0

lemma Py_sum (M : Model) (y : ℤ) (f : ℕ → ℤ → ℝ≥0∞) :
    ∀ t : ℕ, Py M y (fun z => ∑ i ∈ Finset.range t, f i z) = ∑ i ∈ Finset.range t, Py M y (f i)
  | 0 => by simp only [Finset.range_zero, Finset.sum_empty]; exact Py_zero M y
  | t + 1 => by
    simp only [Finset.sum_range_succ]
    rw [Py_add, Py_sum M y f t]

lemma totalCost_succ (M : Model) (π : ℕ → ℤ → ℤ) (t : ℕ) (x : ℤ) :
    totalCost M π (t + 1) x = ENNReal.ofReal (M.G (π 0 x)) + Py M (π 0 x) (totalCost M (fun s => π (s + 1)) t) := by
  unfold totalCost
  rw [Finset.sum_range_succ']
  have h : ∀ i, periodCost M π (i + 1) x = Py M (π 0 x) (periodCost M (fun s => π (s + 1)) i) := fun i => rfl
  simp only [h]
  rw [← Py_sum M (π 0 x) (fun i => periodCost M (fun s => π (s + 1)) i) t, add_comm]
  rfl

lemma Wt_le_cost (M : Model) (U : ℤ) : ∀ t : ℕ, ∀ π : ℕ → ℤ → ℤ, (∀ s, Feasible M U (π s)) →
    ∀ x ≤ U, Wt M U t x ≤ totalCost M π t x := by
  intro t
  induction t with
  | zero => intro π _ x _; simp [Wt]
  | succ t ih =>
    intro π hπ x hx
    have hy := hπ 0 x hx
    rw [totalCost_succ]
    calc Wt M U (t + 1) x ≤ Ry M (Wt M U t) (π 0 x) :=
          Finset.inf_le ((mem_Yset M U x _).2 ⟨hy.1, hy.2.1, hy.2.2⟩)
      _ ≤ _ := by
          unfold Ry
          gcongr
          exact Py_mono M _ _ _ (fun z hz => ih (fun s => π (s + 1)) (fun s => hπ (s + 1)) z (by omega))

lemma anti_chainE (f : ℤ → ℝ≥0∞) (s : ℤ) (h : ∀ y, y < s → f (y + 1) ≤ f y) :
    ∀ a c, a ≤ c → c ≤ s → f c ≤ f a := by
  have key : ∀ k : ℕ, ∀ a, a + k ≤ s → f (a + k) ≤ f a := by
    intro k
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
      intro a ha
      have h1 := h (a + k) (by push_cast at ha; omega)
      have e : a + ((k + 1 : ℕ) : ℤ) = a + k + 1 := by push_cast; ring
      rw [e]
      exact le_trans h1 (ih a (by push_cast at ha; omega))
  intro a c hac hcs
  have := key (c - a).toNat a (by rw [Int.toNat_of_nonneg (by omega)]; omega)
  rwa [Int.toNat_of_nonneg (by omega), show a + (c - a) = c by ring] at this

lemma Ry_anti (M : Model) (yInf : ℤ) (hGanti : ∀ y, y < yInf → M.G (y + 1) ≤ M.G y)
    (W : ℤ → ℝ≥0∞) (hW : ∀ x, x < yInf → W (x + 1) ≤ W x) :
    ∀ y, y < yInf → Ry M W (y + 1) ≤ Ry M W y := by
  intro y hy
  unfold Ry Py
  gcongr with j
  · exact hGanti y hy
  · have := hW (y - j) (by omega)
    rwa [show y - (j:ℤ) + 1 = y + 1 - j by ring] at this

lemma Wt_anti (M : Model) (U yInf : ℤ) (hyU : yInf ≤ U) (hGanti : ∀ y, y < yInf → M.G (y + 1) ≤ M.G y) :
    ∀ n : ℕ, ∀ x, x < yInf → Wt M U n (x + 1) ≤ Wt M U n x := by
  intro n
  induction n with
  | zero => intro x _; simp [Wt]
  | succ n ih =>
    intro x hx
    have hne : (Yset M U x).Nonempty := ⟨x, (mem_Yset M U x x).2 ⟨le_rfl, by omega, by omega⟩⟩
    obtain ⟨y, hy, heq⟩ := Finset.exists_mem_eq_inf (Yset M U x) hne (fun y => Ry M (Wt M U n) y)
    have hy' := (mem_Yset M U x y).1 hy
    show TV M U (Wt M U n) (x + 1) ≤ TV M U (Wt M U n) x
    unfold TV
    rw [heq]
    by_cases hyI : y < yInf
    · calc (Yset M U (x + 1)).inf (fun y => Ry M (Wt M U n) y) ≤ Ry M (Wt M U n) (y + 1) :=
            Finset.inf_le ((mem_Yset M U _ _).2 ⟨by omega, by omega, by omega⟩)
        _ ≤ _ := Ry_anti M yInf hGanti _ ih y hyI
    · exact Finset.inf_le ((mem_Yset M U _ _).2 ⟨by omega, by omega, hy'.2.2⟩)

lemma opt_ennreal (M : Model) (U : ℤ) (g : ℝ) (hg : 0 ≤ g) (v : ℤ → ℝ) (ys : ℤ)
    (hmin : ∀ x ≤ U, v ys ≤ v x) (hsum : ∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j)))
    (x y : ℤ) (hx : x ≤ U) (hy : y ≤ U) (h : g + v x ≤ R M v y) :
    ENNReal.ofReal g + ENNReal.ofReal (v x - v ys)
      ≤ ENNReal.ofReal (M.G y) + Py M y (fun z => ENNReal.ofReal (v z - v ys)) := by
  have hs := hsum y hy
  have hs1 := M.p_sum.summable
  have hsw : Summable (fun j : ℕ => M.p j * (v (y - j) - v ys)) :=
    (hs.sub (hs1.mul_right (v ys))).congr (fun j => by ring)
  have hE : ∑' j : ℕ, M.p j * (v (y - j) - v ys) = ∑' j : ℕ, M.p j * v (y - j) - v ys := by
    rw [show (fun j : ℕ => M.p j * (v (y - j) - v ys)) = fun j : ℕ => M.p j * v (y - j) - M.p j * v ys
      from funext (fun j => by ring), Summable.tsum_sub hs (hs1.mul_right _), tsum_mul_right,
      M.p_sum.tsum_eq, one_mul]
  have hreal : g + (v x - v ys) ≤ M.G y + ∑' j : ℕ, M.p j * (v (y - j) - v ys) := by
    unfold R at h
    rw [hE]
    linarith
  have hw0 : 0 ≤ v x - v ys := by linarith [hmin x hx]
  have hE0 : 0 ≤ ∑' j : ℕ, M.p j * (v (y - j) - v ys) :=
    tsum_nonneg (fun j => mul_nonneg (M.p_nonneg j) (by linarith [hmin (y - j) (by omega)]))
  have hPy := Py_ofReal M y (fun z => v z - v ys) (fun z hz => by linarith [hmin z (by omega)]) hsw
  rw [hPy, ← ENNReal.ofReal_add hg hw0, ← ENNReal.ofReal_add (M.G_nonneg _) hE0]
  exact ENNReal.ofReal_le_ofReal hreal

theorem F6 (M : Model) (U L yInf : ℤ) (hLy : L + M.b ≤ yInf) (hyU : yInf ≤ U)
    (hGanti : ∀ y, y < yInf → M.G (y + 1) ≤ M.G y)
    (g : ℝ) (hg : 0 ≤ g) (v : ℤ → ℝ) (ys : ℤ)
    (hmin : ∀ x ≤ U, v ys ≤ v x) (hsum : ∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j)))
    (hopt : OptEq M U g v)
    (Φ : ℤ → ℝ) (hΦ0 : ∀ x ≤ U, 0 ≤ Φ x)
    (hΦ1 : ∀ x ≤ U, Summable (fun j : ℕ => M.p j * Φ (x + M.b - j)) ∧
      ∑' j : ℕ, M.p j * Φ (x + M.b - j) ≤ Φ x)
    (C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hΦ3 : ∀ y, L < y → y ≤ U → Summable (fun j : ℕ => M.p j * Φ (y - j)) ∧
      ∑' j : ℕ, M.p j * Φ (y - j) ≤ C₁)
    (hW : ∀ ε > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≤ U, v x - v ys ≤ ε * Φ x + C) :
    ∀ π : ℕ → ℤ → ℤ, (∀ t, Feasible M U (π t)) → ∀ x ≤ U,
      ENNReal.ofReal g ≤ liminf (fun t : ℕ => totalCost M π t x / (t : ℝ≥0∞)) atTop := by
  set Φt : ℤ → ℝ≥0∞ := fun z => ENNReal.ofReal (Φ z) with hΦt
  set Wv : ℤ → ℝ≥0∞ := fun z => ENNReal.ofReal (v z - v ys) with hWv
  -- the Lyapunov step for the action chosen by value iteration
  have hchoose : ∀ n : ℕ, ∀ x ≤ U, ∃ y, x ≤ y ∧ y ≤ x + M.b ∧ y ≤ U ∧
      Wt M U (n + 1) x = Ry M (Wt M U n) y ∧ Py M y Φt ≤ Φt x + ENNReal.ofReal C₁ := by
    intro n x hx
    by_cases hxL : x ≤ L
    · refine ⟨x + M.b, by omega, le_rfl, by omega, ?_, ?_⟩
      · show (Yset M U x).inf (fun y => Ry M (Wt M U n) y) = Ry M (Wt M U n) (x + M.b)
        apply le_antisymm (Finset.inf_le ((mem_Yset M U _ _).2 ⟨by omega, le_rfl, by omega⟩))
        apply Finset.le_inf
        intro y hy
        have hy' := (mem_Yset M U x y).1 hy
        exact anti_chainE (Ry M (Wt M U n)) yInf
          (Ry_anti M yInf hGanti _ (Wt_anti M U yInf hyU hGanti n)) y (x + M.b) hy'.2.1 (by omega)
      · obtain ⟨hs, hle⟩ := hΦ1 x hx
        have := Py_ofReal M (x + M.b) Φ (fun z hz => hΦ0 z (by omega)) hs
        rw [this]
        exact le_trans (ENNReal.ofReal_le_ofReal hle) le_self_add
    · have hne : (Yset M U x).Nonempty := ⟨x, (mem_Yset M U x x).2 ⟨le_rfl, by omega, hx⟩⟩
      obtain ⟨y, hy, heq⟩ := Finset.exists_mem_eq_inf (Yset M U x) hne (fun y => Ry M (Wt M U n) y)
      have hy' := (mem_Yset M U x y).1 hy
      refine ⟨y, hy'.1, hy'.2.1, hy'.2.2, heq, ?_⟩
      obtain ⟨hs, hle⟩ := hΦ3 y (by omega) hy'.2.2
      have := Py_ofReal M y Φ (fun z hz => hΦ0 z (by omega)) hs
      rw [this]
      exact le_trans (ENNReal.ofReal_le_ofReal hle) le_add_self
  have hmain : ∀ ε > 0, ∀ C : ℝ, 0 ≤ C → (∀ x ≤ U, v x - v ys ≤ ε * Φ x + C) →
      ∀ t : ℕ, ∀ x ≤ U, (t : ℝ≥0∞) * ENNReal.ofReal g + Wv x
        ≤ Wt M U t x + (ENNReal.ofReal C + ENNReal.ofReal ε * (Φt x + t * ENNReal.ofReal C₁)) := by
    intro ε hε C hC0 hC t
    induction t with
    | zero =>
      intro x hx
      simp only [Nat.cast_zero, zero_mul, zero_add, Wt]
      calc Wv x ≤ ENNReal.ofReal (C + ε * Φ x) := ENNReal.ofReal_le_ofReal (by linarith [hC x hx])
        _ = _ := by rw [ENNReal.ofReal_add hC0 (mul_nonneg hε.le (hΦ0 x hx)), ENNReal.ofReal_mul hε.le, add_zero]
    | succ t ih =>
      intro x hx
      obtain ⟨y, h1, h2, h3, hWeq, hPΦ⟩ := hchoose t x hx
      have hopt1 := opt_ennreal M U g hg v ys hmin hsum x y hx h3 ((hopt x hx).1 y h1 h2 h3)
      have hIH : Py M y (fun z => (t : ℝ≥0∞) * ENNReal.ofReal g + Wv z)
          ≤ Py M y (fun z => Wt M U t z + (ENNReal.ofReal C + ENNReal.ofReal ε * (Φt z + t * ENNReal.ofReal C₁))) :=
        Py_mono M y _ _ (fun z hz => ih z (by omega))
      rw [Py_add, Py_const, Py_add, Py_add, Py_const, Py_cmul, Py_add, Py_const] at hIH
      rw [hWeq]
      unfold Ry
      calc ((t + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal g + Wv x
          = (t : ℝ≥0∞) * ENNReal.ofReal g + (ENNReal.ofReal g + Wv x) := by push_cast; ring
        _ ≤ (t : ℝ≥0∞) * ENNReal.ofReal g + (ENNReal.ofReal (M.G y) + Py M y Wv) := by gcongr
        _ = ENNReal.ofReal (M.G y) + ((t : ℝ≥0∞) * ENNReal.ofReal g + Py M y Wv) := by ring
        _ ≤ ENNReal.ofReal (M.G y) + (Py M y (Wt M U t) + (ENNReal.ofReal C
              + ENNReal.ofReal ε * (Py M y Φt + t * ENNReal.ofReal C₁))) := by gcongr
        _ ≤ ENNReal.ofReal (M.G y) + (Py M y (Wt M U t) + (ENNReal.ofReal C
              + ENNReal.ofReal ε * (Φt x + ENNReal.ofReal C₁ + t * ENNReal.ofReal C₁))) := by gcongr
        _ = _ := by push_cast; ring
  intro π hπ x hx
  apply le_of_forall_lt
  intro c hc
  have hcT : c ≠ ⊤ := ne_top_of_lt hc
  set β := c.toReal with hβ
  have hβ0 : 0 ≤ β := ENNReal.toReal_nonneg
  have hcβ : c = ENNReal.ofReal β := (ENNReal.ofReal_toReal hcT).symm
  have hβg : β < g := by
    rw [hcβ] at hc
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hβ0).1 hc
  -- pick an intermediate level
  set β' := (β + g) / 2 with hβ'
  have hcβ' : c < ENNReal.ofReal β' := by
    rw [hcβ]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  refine lt_of_lt_of_le hcβ' ?_
  set ε := (g - β') / (2 * (C₁ + 1)) with hε
  have hεpos : 0 < ε := by apply div_pos <;> linarith
  obtain ⟨C, hC0, hC⟩ := hW ε hεpos
  have hΦx := hΦ0 x hx
  have hεC : ε * C₁ ≤ (g - β') / 2 := by
    rw [hε, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (ε * Φ x + C) / (g - β'))
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ge_atTop (max N 1)] with t ht
  have ht1 : (1:ℝ) ≤ t := by exact_mod_cast le_trans (le_max_right _ _) ht
  have htN : (N:ℝ) ≤ t := by exact_mod_cast le_trans (le_max_left _ _) ht
  have htpos : (0:ℝ) < t := by linarith
  have htne : (t : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
  have hkey := hmain ε hεpos C hC0 hC t x hx
  have hcost := Wt_le_cost M U t π hπ x hx
  rw [ENNReal.le_div_iff_mul_le (Or.inl htne) (Or.inl (by simp))]
  by_cases hT : totalCost M π t x = ⊤
  · rw [hT]; exact le_top
  · -- real inequality
    have hb1 : (t : ℝ≥0∞) * ENNReal.ofReal g ≤ totalCost M π t x
        + ENNReal.ofReal (C + ε * (Φ x + t * C₁)) := by
      have e : ENNReal.ofReal (C + ε * (Φ x + t * C₁))
          = ENNReal.ofReal C + ENNReal.ofReal ε * (Φt x + t * ENNReal.ofReal C₁) := by
        rw [ENNReal.ofReal_add hC0 (by positivity), ENNReal.ofReal_mul hεpos.le, ENNReal.ofReal_add hΦx (by positivity),
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      rw [e]
      calc (t : ℝ≥0∞) * ENNReal.ofReal g ≤ (t : ℝ≥0∞) * ENNReal.ofReal g + Wv x := le_self_add
        _ ≤ _ := hkey
        _ ≤ _ := by gcongr
    have h2 := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (ENNReal.natCast_ne_top t) ENNReal.ofReal_ne_top)
      (ENNReal.add_ne_top.2 ⟨hT, ENNReal.ofReal_ne_top⟩)).2 hb1
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hg,
      ENNReal.toReal_add hT (by simp), ENNReal.toReal_ofReal (by positivity)] at h2
    have h3 : ENNReal.ofReal β' * (t : ℝ≥0∞) = ENNReal.ofReal (β' * t) := by
      rw [ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_natCast]
    rw [h3, ← ENNReal.ofReal_toReal hT]
    apply ENNReal.ofReal_le_ofReal
    have h4 : 2 * (ε * Φ x + C) < (g - β') * t := by
      rw [div_lt_iff₀ (by linarith)] at hN
      nlinarith
    have h5 : ε * (t * C₁) ≤ (g - β') / 2 * t := by nlinarith
    nlinarith

end FZE


namespace FZA
open FedergruenZipkin.AvgCost

lemma lam_dom (A A' T T' D ε : ℝ) (k : ℕ) (hA : 0 < A) (hA' : 0 < A') (hε : 0 < ε) (hTT : T ≤ T') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x + 1 ≤ T → A * (T - x) ^ (k + 1) + D ≤ ε * (A' * (T' - x) ^ (k + 2)) + C := by
  set N₀ := A / (ε * A') with hN₀
  have hN0 : 0 < N₀ := by positivity
  refine ⟨A * N₀ ^ (k + 1) + |D|, by positivity, fun x hx => ?_⟩
  set n := T' - x with hn
  have hn1 : 1 ≤ n := by linarith
  have h1 : A * (T - x) ^ (k + 1) ≤ A * n ^ (k + 1) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) _) hA.le
  have hD := le_abs_self D
  have hpos : 0 ≤ ε * (A' * n ^ (k + 2)) := by positivity
  rcases le_or_gt N₀ n with h | h
  · have h2 : A ≤ ε * A' * n := by
      rw [hN₀, div_le_iff₀ (by positivity)] at h
      linarith
    have h3 : A * n ^ (k + 1) ≤ ε * (A' * n ^ (k + 2)) := by
      have : ε * (A' * n ^ (k + 2)) = (ε * A' * n) * n ^ (k + 1) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have : 0 ≤ A * N₀ ^ (k + 1) := by positivity
    linarith
  · have h3 : A * n ^ (k + 1) ≤ A * N₀ ^ (k + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h.le _) hA.le
    linarith

end FZA

open FedergruenZipkin.AvgCost in
theorem solution (M : Model) (U yInf : ℤ)
    (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf) (hU : yInf ≤ U) :
    ∃ (g : ℝ) (v : ℤ → ℝ) (ystar : ℤ),
      (∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j))) ∧
      (∃ A B : ℝ, ∀ x ≤ U, |v x| ≤ A + B * |(x : ℝ)| ^ (M.ρ + 3)) ∧
      0 ≤ g ∧
      OptEq M U g v ∧
      ConvexBelow U v ∧
      ystar ≤ U ∧ yInf ≤ ystar ∧ (∀ x ≤ U, v ystar ≤ v x) ∧
      StronglyOptimal M U (critNum M ystar) g := by
  have hmom := FZ9.moments_finite M
  obtain ⟨T, A, hLy, -⟩ := FZF.lyapOK_exists M U 0
  obtain ⟨g, v, D, hg, hvI, hvs, hopt, hvb⟩ := FZF.F3 M U yInf hyInf hU T A hLy
  obtain ⟨ys, hysU, hys1, hysmin, hfeas, hatt⟩ := FZ9.critNum_attains M U yInf hyInf hU g v hvI hvs hopt
  obtain ⟨T', A', hT', hT'T, hA', hL'⟩ := FZL.lyap M hmom U M.ρ 0 0 T le_rfl le_rfl
  have hb0 : (0:ℝ) ≤ M.b := Nat.cast_nonneg _
  set Φ : ℤ → ℝ := fun x => A' * (T' - x) ^ (M.ρ + 2) with hΦ
  set L : ℤ := yInf - M.b with hL
  have hΦ0' : ∀ x : ℤ, x ≤ U + M.b → 0 ≤ Φ x := by
    intro x hx
    have : (x:ℝ) ≤ U + M.b := by exact_mod_cast hx
    simp only [hΦ]
    have : 0 ≤ T' - x := by linarith
    positivity
  have hΦ0 : ∀ x ≤ U, 0 ≤ Φ x := fun x hx => hΦ0' x (by omega)
  have hΦ1 : ∀ x ≤ U, Summable (fun j : ℕ => M.p j * Φ (x + M.b - j)) ∧
      ∑' j : ℕ, M.p j * Φ (x + M.b - j) ≤ Φ x := by
    intro x hx
    obtain ⟨h1, h2⟩ := hL' x hx
    refine ⟨h1, ?_⟩
    simp only [zero_mul, add_zero, zero_add] at h2
    exact h2
  have hΦs : ∀ y ≤ U + M.b, Summable (fun j : ℕ => M.p j * Φ (y - j)) := by
    intro y hy
    refine (hΦ1 (y - M.b) (by omega)).1.congr (fun j => ?_)
    rw [show y - (M.b:ℤ) + (M.b:ℤ) - (j:ℤ) = y - j by ring]
  set C₁ := ∑' j : ℕ, M.p j * Φ (L - j) with hC₁
  have hC₁0 : 0 ≤ C₁ := tsum_nonneg (fun j => mul_nonneg (M.p_nonneg j) (hΦ0' _ (by omega)))
  have hΦ3 : ∀ y, L < y → y ≤ U → Summable (fun j : ℕ => M.p j * Φ (y - j)) ∧
      ∑' j : ℕ, M.p j * Φ (y - j) ≤ C₁ := by
    intro y hLy' hy
    refine ⟨hΦs y (by omega), ?_⟩
    refine Summable.tsum_le_tsum (fun j => ?_) (hΦs y (by omega)) (hΦs L (by omega))
    apply mul_le_mul_of_nonneg_left _ (M.p_nonneg j)
    simp only [hΦ]
    have hyR : ((y - j : ℤ) : ℝ) ≤ U := by
      have h1 : (y:ℝ) ≤ U := by exact_mod_cast hy
      push_cast
      linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
    have hLyR : ((L - j : ℤ) : ℝ) ≤ ((y - j : ℤ) : ℝ) := by
      have h1 : (L:ℝ) ≤ y := by exact_mod_cast hLy'.le
      push_cast
      linarith
    apply mul_le_mul_of_nonneg_left _ hA'.le
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  have hW : ∀ ε > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≤ U, v x - v ys ≤ ε * Φ x + C := by
    intro ε hε
    obtain ⟨C, hC0, hC⟩ := FZA.lam_dom A A' T T' D ε M.ρ hLy.2.1 hA' hε hT'T
    refine ⟨C, hC0, fun x hx => ?_⟩
    have h1 := (hvb x hx).2
    have h2 := (hvb ys hysU).1
    have hxT : (x:ℝ) + 1 ≤ T := by
      have : (x:ℝ) ≤ U := by exact_mod_cast hx
      linarith [hLy.1]
    have h3 := hC x hxT
    simp only [FZF.Lam] at h1
    simp only [hΦ]
    linarith
  have hδL : ∀ x ≤ L, critNum M ys x = x + M.b := by
    intro x hx
    unfold critNum
    rw [min_eq_right (by omega), max_eq_right (by omega)]
  refine ⟨g, v, ys, hvs, hvI.1, hg, hopt, hvI.2.2, hysU, hys1, hysmin, hfeas, ?_, ?_⟩
  · exact FZE.F5 M U L (by omega) g hg v (critNum M ys) hfeas hδL ys hysmin hvs hatt Φ hΦ0 hΦ1
      C₁ hC₁0 hΦ3 hW
  · exact FZE.F6 M U L yInf (by omega) hU (FZ9.G_anti M yInf hyInf) g hg v ys hysmin hvs hopt Φ hΦ0 hΦ1
      C₁ hC₁0 hΦ3 hW
