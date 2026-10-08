-- Prove2me | solution 1 for ChenBullwhip.Centralized.ar1_moments
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T03:37:51.271649+00:00
-- url     : https://prove2.me/submissions/80e14d83-1574-49ec-957c-9afe0b12d453

import Mathlib
import Definitions.Def_ChenBullwhip_Centralized_AR1Demand
import Definitions.Def_ChenBullwhip_Centralized_Policy

open MeasureTheory ProbabilityTheory

namespace ChenBullwhip.Centralized

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma cb_eps_eq (X : AR1Demand P) (t : ℤ) :
    X.eps t = fun ω => X.D t ω - X.mu - X.rho * X.D (t - 1) ω := by
  funext ω; rw [X.recursion t ω]; ring

lemma cb_eps_meas (X : AR1Demand P) (t : ℤ) : Measurable (X.eps t) := by
  rw [cb_eps_eq]
  exact ((X.measurable_D t).sub_const _).sub ((X.measurable_D (t-1)).const_mul _)

lemma cb_one_sub_rho_pos (X : AR1Demand P) : 0 < 1 - X.rho := by
  have := X.abs_rho_lt_one; have := le_abs_self X.rho; linarith

lemma cb_one_sub_rho_sq_pos (X : AR1Demand P) : 0 < 1 - X.rho ^ 2 := by
  have h := X.abs_rho_lt_one
  have : X.rho ^ 2 = |X.rho| ^ 2 := (sq_abs _).symm
  rw [this]; nlinarith [abs_nonneg X.rho]

noncomputable def cbm (X : AR1Demand P) : ℝ := X.mu / (1 - X.rho)

lemma cb_mean (X : AR1Demand P) (t : ℤ) : ∫ ω, X.D t ω ∂P = cbm X := by
  have h0 : ∀ s, ∫ ω, X.D s ω ∂P = ∫ ω, X.D 0 ω ∂P := fun s => (X.stationary s).integral_eq
  have hi : ∀ s, Integrable (X.D s) P := fun s => (X.D_memLp s).integrable one_le_two
  have hei : Integrable (X.eps 1) P := (X.eps_memLp 1).integrable one_le_two
  have hrec : ∫ ω, X.D 1 ω ∂P = X.mu + X.rho * ∫ ω, X.D 0 ω ∂P + 0 := by
    rw [← X.eps_mean 1, ← integral_const_mul]
    have : (fun ω => X.D 1 ω) = fun ω => X.mu + X.rho * X.D 0 ω + X.eps 1 ω := by
      funext ω; rw [X.recursion 1 ω]; norm_num
    rw [this, integral_add, integral_add, integral_const]
    · simp
    · exact integrable_const _
    · exact (hi 0).const_mul _
    · exact (integrable_const _).add ((hi 0).const_mul _)
    · exact hei
  rw [h0 1] at hrec
  rw [h0 t, cbm, eq_div_iff (cb_one_sub_rho_pos X).ne']
  linarith

/-- centered demand -/
noncomputable def cbW (X : AR1Demand P) (s : ℤ) (ω : Ω) : ℝ := X.D s ω - cbm X

lemma cbW_rec (X : AR1Demand P) (s : ℤ) (ω : Ω) :
    cbW X s ω = X.rho * cbW X (s - 1) ω + X.eps s ω := by
  have h1 := (cb_one_sub_rho_pos X).ne'
  simp only [cbW, cbm]; rw [X.recursion s ω]; field_simp; ring

lemma cbW_memLp (X : AR1Demand P) (s : ℤ) : MemLp (cbW X s) 2 P :=
  (X.D_memLp s).sub (memLp_const _)

lemma cbW_meas (X : AR1Demand P) (s : ℤ) : Measurable (cbW X s) :=
  (X.measurable_D s).sub_const _

lemma cbW_sq (X : AR1Demand P) (s : ℤ) :
    ∫ ω, cbW X s ω ^ 2 ∂P = variance (X.D 0) P := by
  rw [← (X.stationary s).variance_eq, variance_eq_integral (X.measurable_D s).aemeasurable,
    cb_mean]; rfl

lemma cbW_sq_int (X : AR1Demand P) (s : ℤ) : Integrable (fun ω => cbW X s ω ^ 2) P :=
  (cbW_memLp X s).integrable_sq

lemma cb_eps_sq (X : AR1Demand P) (s : ℤ) : ∫ ω, X.eps s ω ^ 2 ∂P = X.sigma ^ 2 := by
  rw [← X.eps_variance s, variance_eq_integral (cb_eps_meas X s).aemeasurable, X.eps_mean]
  simp

lemma cb_int_mul (f g : Ω → ℝ) (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => f ω * g ω) P := hf.integrable_mul hg

/-- W_s - ρ^n W_{s-n} is a finite sum of errors -/
lemma cbW_expand (X : AR1Demand P) (n : ℕ) (s : ℤ) (ω : Ω) :
    cbW X s ω = X.rho ^ n * cbW X (s - n) ω
      + ∑ j ∈ Finset.range n, X.rho ^ j * X.eps (s - j) ω := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [cbW_rec X s ω, ih (s - 1), Finset.sum_range_succ']
    have : s - 1 - (n : ℤ) = s - ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, mul_add, Finset.mul_sum]
    have h2 : ∀ j : ℕ, s - 1 - (j : ℤ) = s - ((j + 1 : ℕ) : ℤ) := by intro j; push_cast; ring
    simp only [h2, pow_succ]
    simp only [Nat.cast_zero, sub_zero, pow_zero, one_mul]
    rw [Finset.sum_congr rfl (fun j _ => by ring :
      ∀ j ∈ Finset.range n, X.rho * (X.rho ^ j * X.eps (s - ((j + 1 : ℕ) : ℤ)) ω)
        = X.rho ^ j * X.rho * X.eps (s - ((j + 1 : ℕ) : ℤ)) ω)]
    ring

lemma cb_zero_of_le_pow (I K r : ℝ) (hr : |r| < 1) (h : ∀ n : ℕ, |I| ≤ |r| ^ n * K) : I = 0 := by
  have ht : Filter.Tendsto (fun n : ℕ => |r| ^ n * K) Filter.atTop (nhds (0 * K)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg r) hr).mul_const K
  rw [zero_mul] at ht
  have : |I| ≤ 0 := ge_of_tendsto' ht h
  exact abs_nonpos_iff.mp this

lemma cb_abs_int_mul_le (f g : Ω → ℝ) (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    |∫ ω, f ω * g ω ∂P| ≤ (∫ ω, f ω ^ 2 ∂P + ∫ ω, g ω ^ 2 ∂P) / 2 := by
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_add hf.integrable_sq hg.integrable_sq, ← integral_div]
  refine integral_mono (cb_int_mul f g hf hg).abs ((hf.integrable_sq.add hg.integrable_sq).div_const _) ?_
  intro ω
  simp only [Pi.add_apply]
  rw [abs_mul]
  nlinarith [sq_abs (f ω), sq_abs (g ω), sq_nonneg (|f ω| - |g ω|)]

lemma cb_eps_eps (X : AR1Demand P) (a b : ℤ) (hab : a ≠ b) :
    ∫ ω, X.eps a ω * X.eps b ω ∂P = 0 := by
  rw [(X.eps_iIndep.indepFun hab).integral_fun_mul_eq_mul_integral
    (cb_eps_meas X a).aestronglyMeasurable (cb_eps_meas X b).aestronglyMeasurable]
  simp [X.eps_mean]

lemma cbW_eps (X : AR1Demand P) (s u : ℤ) (hsu : s < u) :
    ∫ ω, cbW X s ω * X.eps u ω ∂P = 0 := by
  apply cb_zero_of_le_pow _ ((variance (X.D 0) P + X.sigma ^ 2) / 2) X.rho X.abs_rho_lt_one
  intro n
  have he : ∀ v, MemLp (X.eps v) 2 P := X.eps_memLp
  have hexp : (fun ω => cbW X s ω * X.eps u ω) = fun ω =>
      X.rho ^ n * (cbW X (s - n) ω * X.eps u ω)
        + ∑ j ∈ Finset.range n, X.rho ^ j * (X.eps (s - j) ω * X.eps u ω) := by
    funext ω; rw [cbW_expand X n s ω, add_mul, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hexp, integral_add, integral_finsetSum, integral_const_mul]
  · rw [Finset.sum_eq_zero (fun j _ => by
      rw [integral_const_mul, cb_eps_eps X _ _ (by omega), mul_zero]), add_zero, abs_mul,
      abs_pow]
    gcongr
    refine (cb_abs_int_mul_le _ _ (cbW_memLp X _) (he u)).trans (le_of_eq ?_)
    rw [cbW_sq, cb_eps_sq]
  · intro j _; exact (cb_int_mul _ _ (he _) (he u)).const_mul _
  · exact (cb_int_mul _ _ (cbW_memLp X _) (he u)).const_mul _
  · exact integrable_finsetSum _ (fun j _ => (cb_int_mul _ _ (he _) (he u)).const_mul _)

lemma cb_cov_eq (X : AR1Demand P) (a b : ℤ) :
    covariance (X.D a) (X.D b) P = ∫ ω, cbW X a ω * cbW X b ω ∂P := by
  rw [covariance, cb_mean, cb_mean]; rfl

lemma cb_V_eq (X : AR1Demand P) :
    variance (X.D 0) P = X.sigma ^ 2 / (1 - X.rho ^ 2) := by
  have h1 := cbW_sq X 1
  have hx : (fun ω => cbW X 1 ω ^ 2) = fun ω => X.rho ^ 2 * cbW X 0 ω ^ 2
      + 2 * X.rho * (cbW X 0 ω * X.eps 1 ω) + X.eps 1 ω ^ 2 := by
    funext ω; rw [cbW_rec X 1 ω]; norm_num; ring
  rw [hx, integral_add, integral_add, integral_const_mul, integral_const_mul, cbW_sq,
    cbW_eps X 0 1 (by norm_num), cb_eps_sq] at h1
  · rw [eq_div_iff (cb_one_sub_rho_sq_pos X).ne']; linarith
  · exact (cbW_sq_int X 0).const_mul _
  · exact (cb_int_mul _ _ (cbW_memLp X 0) (X.eps_memLp 1)).const_mul _
  · exact ((cbW_sq_int X 0).const_mul _).add
      ((cb_int_mul _ _ (cbW_memLp X 0) (X.eps_memLp 1)).const_mul _)
  · exact (X.eps_memLp 1).integrable_sq

lemma cbW_lag (X : AR1Demand P) (r : ℤ) (k : ℕ) :
    ∫ ω, cbW X (r + k) ω * cbW X r ω ∂P = X.rho ^ k * variance (X.D 0) P := by
  induction k with
  | zero => simp only [Nat.cast_zero, add_zero, pow_zero, one_mul]; rw [← cbW_sq X r]; congr 1; funext ω; ring
  | succ k ih =>
    have hx : (fun ω => cbW X (r + ((k + 1 : ℕ) : ℤ)) ω * cbW X r ω) = fun ω =>
        X.rho * (cbW X (r + k) ω * cbW X r ω) + cbW X r ω * X.eps (r + ((k + 1 : ℕ) : ℤ)) ω := by
      funext ω; rw [cbW_rec X]; push_cast; ring_nf
    rw [hx, integral_add, integral_const_mul, ih, cbW_eps X _ _ (by push_cast; omega)]
    · ring
    · exact (cb_int_mul _ _ (cbW_memLp X _) (cbW_memLp X _)).const_mul _
    · exact cb_int_mul _ _ (cbW_memLp X _) (X.eps_memLp _)

theorem ar1_moments_core (X : AR1Demand P) (p : ℕ) (hp : 1 ≤ p) (t : ℤ) :
    ProbabilityTheory.covariance (X.D (t - 1)) (X.D (t - p - 1)) P
        = X.rho ^ p / (1 - X.rho ^ 2) * X.sigma ^ 2
      ∧ ProbabilityTheory.variance (X.D t) P = X.sigma ^ 2 / (1 - X.rho ^ 2) := by
  refine ⟨?_, ?_⟩
  · rw [cb_cov_eq]
    have := cbW_lag X (t - p - 1) p
    rw [show t - (p : ℤ) - 1 + p = t - 1 by ring] at this
    rw [this, cb_V_eq]; ring
  · rw [(X.stationary t).variance_eq, cb_V_eq]

end ChenBullwhip.Centralized

open ChenBullwhip.Centralized


theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (p : ℕ) (hp : 1 ≤ p) (t : ℤ) :
    ProbabilityTheory.covariance (X.D (t - 1)) (X.D (t - p - 1)) P
        = X.rho ^ p / (1 - X.rho ^ 2) * X.sigma ^ 2
      ∧ ProbabilityTheory.variance (X.D t) P = X.sigma ^ 2 / (1 - X.rho ^ 2) := by
  exact ar1_moments_core X p hp t
