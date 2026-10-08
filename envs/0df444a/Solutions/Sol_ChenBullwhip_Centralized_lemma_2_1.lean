-- Prove2me | solution 1 for ChenBullwhip.Centralized.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T03:46:39.103612+00:00
-- url     : https://prove2.me/submissions/ea8c9d0c-6bb3-4993-b8a8-26ab3d5f9473

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

/-! ## symmetry -/

lemma cb_sym (X : AR1Demand P) (ψ : (ℤ → ℝ) → ℝ) (hψ : Measurable ψ)
    (hodd : ∀ x, ψ (-x) = -ψ x) :
    ∫ ω, ψ (fun u => X.eps u ω) ∂P = 0 := by
  have hm : Measurable (fun ω u => X.eps u ω) := measurable_pi_lambda _ (fun u => cb_eps_meas X u)
  have hm' : Measurable (fun ω u => -X.eps u ω) :=
    measurable_pi_lambda _ (fun u => (cb_eps_meas X u).neg)
  have h1 : P.map (fun ω u => X.eps u ω) = Measure.infinitePi (fun u => P.map (X.eps u)) :=
    X.eps_iIndep.map_fun_eq_infinitePi_map₀ hm.aemeasurable
  have hind' : iIndepFun (fun u ω => -X.eps u ω) P :=
    X.eps_iIndep.comp (fun _ x => -x) (fun _ => measurable_neg)
  have h2 : P.map (fun ω u => -X.eps u ω) =
      Measure.infinitePi (fun u => P.map (fun ω => -X.eps u ω)) :=
    hind'.map_fun_eq_infinitePi_map₀ hm'.aemeasurable
  have h3 : (fun u => P.map (X.eps u)) = (fun u => P.map (fun ω => -X.eps u ω)) := by
    funext u; exact (X.eps_symm u).map_eq
  have hmaps : P.map (fun ω u => X.eps u ω) = P.map (fun ω u => -X.eps u ω) := by
    rw [h1, h2, h3]
  have e1 : ∫ ω, ψ (fun u => X.eps u ω) ∂P = ∫ x, ψ x ∂(P.map (fun ω u => X.eps u ω)) :=
    (integral_map hm.aemeasurable hψ.aestronglyMeasurable).symm
  have e2 : ∫ ω, ψ (fun u => -X.eps u ω) ∂P = ∫ x, ψ x ∂(P.map (fun ω u => -X.eps u ω)) :=
    (integral_map hm'.aemeasurable hψ.aestronglyMeasurable).symm
  have e3 : ∫ ω, ψ (fun u => -X.eps u ω) ∂P = -∫ ω, ψ (fun u => X.eps u ω) ∂P := by
    rw [← integral_neg]; congr 1; funext ω
    rw [← hodd]; rfl
  rw [e1, hmaps, ← e2] at *
  linarith

/-- forecast error on a path -/
noncomputable def cbe (p : ℕ) (t : ℤ) (w : ℤ → ℝ) (i : ℕ) : ℝ :=
  w (t - i) - (∑ j ∈ Finset.Icc 1 p, w (t - i - j)) / p

noncomputable def cbG (C : ℝ) (p : ℕ) (t : ℤ) (w : ℤ → ℝ) : ℝ :=
  C * Real.sqrt ((∑ i ∈ Finset.Icc 1 p, cbe p t w i ^ 2) / p)

noncomputable def cbEn (p : ℕ) (t : ℤ) (w : ℤ → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 p, (w (t - i) ^ 2 + ∑ j ∈ Finset.Icc 1 p, w (t - i - j) ^ 2)

lemma cbe_sub (p : ℕ) (t : ℤ) (w w' : ℤ → ℝ) (i : ℕ) :
    cbe p t w i - cbe p t w' i = cbe p t (w - w') i := by
  simp only [cbe, Pi.sub_apply, Finset.sum_sub_distrib]; ring

lemma cbe_neg (p : ℕ) (t : ℤ) (w : ℤ → ℝ) (i : ℕ) : cbe p t (-w) i = -cbe p t w i := by
  simp only [cbe, Pi.neg_apply, Finset.sum_neg_distrib]; ring

lemma cbG_neg (C : ℝ) (p : ℕ) (t : ℤ) (w : ℤ → ℝ) : cbG C p t (-w) = cbG C p t w := by
  simp only [cbG, cbe_neg, neg_sq]

lemma cbe_sq_le (p : ℕ) (hp : 1 ≤ p) (t : ℤ) (w : ℤ → ℝ) (i : ℕ) :
    cbe p t w i ^ 2 ≤ 2 * (w (t - i) ^ 2 + ∑ j ∈ Finset.Icc 1 p, w (t - i - j) ^ 2) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 p) (f := fun j : ℕ => w (t - i - j))
  simp only [Nat.card_Icc, add_tsub_cancel_right] at hcs
  set S := ∑ j ∈ Finset.Icc 1 p, w (t - i - j)
  set Q := ∑ j ∈ Finset.Icc 1 p, w (t - i - j) ^ 2
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have h1 : (S / p) ^ 2 ≤ Q := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    calc S ^ 2 ≤ p * Q := hcs
      _ ≤ Q * p ^ 2 := by nlinarith
  unfold cbe
  nlinarith [sq_nonneg (w (t - i) + S / p)]

lemma cbG_sq_le (C : ℝ) (p : ℕ) (hp : 1 ≤ p) (t : ℤ) (w : ℤ → ℝ) :
    cbG C p t w ^ 2 ≤ 2 * C ^ 2 * cbEn p t w := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hE : 0 ≤ ∑ i ∈ Finset.Icc 1 p, cbe p t w i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [cbG, mul_pow, Real.sq_sqrt (by positivity)]
  have h1 : (∑ i ∈ Finset.Icc 1 p, cbe p t w i ^ 2) / p ≤ ∑ i ∈ Finset.Icc 1 p, cbe p t w i ^ 2 :=
    div_le_self hE hp'
  have h2 : ∑ i ∈ Finset.Icc 1 p, cbe p t w i ^ 2 ≤ 2 * cbEn p t w := by
    rw [cbEn, Finset.mul_sum]; exact Finset.sum_le_sum (fun i _ => cbe_sq_le p hp t w i)
  have hC := sq_nonneg C
  nlinarith

lemma cb_sqrt_diff (s : Finset ℕ) (f g : ℕ → ℝ) :
    (Real.sqrt (∑ i ∈ s, f i ^ 2) - Real.sqrt (∑ i ∈ s, g i ^ 2)) ^ 2
      ≤ ∑ i ∈ s, (f i - g i) ^ 2 := by
  set A := ∑ i ∈ s, f i ^ 2
  set B := ∑ i ∈ s, g i ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hexp : ∑ i ∈ s, (f i - g i) ^ 2 = A + B - 2 * ∑ i ∈ s, f i * g i := by
    simp only [A, B, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hcs : (∑ i ∈ s, f i * g i) ^ 2 ≤ A * B := Finset.sum_mul_sq_le_sq_mul_sq s f g
  have hZ : ∑ i ∈ s, f i * g i ≤ Real.sqrt A * Real.sqrt B := by
    rw [← Real.sqrt_mul hA]
    exact Real.le_sqrt_of_sq_le hcs
  rw [hexp, sub_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
  linarith

lemma cbG_diff_sq_le (C : ℝ) (p : ℕ) (hp : 1 ≤ p) (t : ℤ) (w w' : ℤ → ℝ) :
    (cbG C p t w - cbG C p t w') ^ 2 ≤ 2 * C ^ 2 * cbEn p t (w - w') := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have hsq : ∀ x : ℝ, Real.sqrt (x / p) = Real.sqrt x / Real.sqrt p := fun x => Real.sqrt_div' _ hp0
  have hsp : 1 ≤ Real.sqrt p := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hp'
  unfold cbG
  rw [hsq, hsq, ← mul_sub, mul_pow, ← sub_div, div_pow]
  have h1 := cb_sqrt_diff (Finset.Icc 1 p) (cbe p t w) (cbe p t w')
  simp only [cbe_sub] at h1
  have h2 : ∑ i ∈ Finset.Icc 1 p, cbe p t (w - w') i ^ 2 ≤ 2 * cbEn p t (w - w') := by
    rw [cbEn, Finset.mul_sum]; exact Finset.sum_le_sum (fun i _ => cbe_sq_le p hp t _ i)
  have hD : 0 ≤ (Real.sqrt (∑ i ∈ Finset.Icc 1 p, cbe p t w i ^ 2) -
      Real.sqrt (∑ i ∈ Finset.Icc 1 p, cbe p t w' i ^ 2)) ^ 2 := sq_nonneg _
  have h3 : (Real.sqrt (∑ i ∈ Finset.Icc 1 p, cbe p t w i ^ 2) -
      Real.sqrt (∑ i ∈ Finset.Icc 1 p, cbe p t w' i ^ 2)) ^ 2 / Real.sqrt p ^ 2 ≤
      (Real.sqrt (∑ i ∈ Finset.Icc 1 p, cbe p t w i ^ 2) -
      Real.sqrt (∑ i ∈ Finset.Icc 1 p, cbe p t w' i ^ 2)) ^ 2 :=
    div_le_self hD (by nlinarith)
  have hC := sq_nonneg C
  calc C ^ 2 * ((Real.sqrt (∑ i ∈ Finset.Icc 1 p, cbe p t w i ^ 2) -
      Real.sqrt (∑ i ∈ Finset.Icc 1 p, cbe p t w' i ^ 2)) ^ 2 / Real.sqrt p ^ 2)
      ≤ C ^ 2 * (2 * cbEn p t (w - w')) := by
        apply mul_le_mul_of_nonneg_left _ hC; linarith
    _ = _ := by ring

lemma cbEn_smul (p : ℕ) (t : ℤ) (r : ℝ) (w : ℤ → ℝ) :
    cbEn p t (fun u => r * w u) = r ^ 2 * cbEn p t w := by
  simp only [cbEn, mul_pow, Finset.mul_sum, mul_add]

lemma sigmaHat_eq (X : AR1Demand P) (C : ℝ) (p : ℕ) (hp : 1 ≤ p) (t : ℤ) (ω : Ω) :
    X.sigmaHat C p t ω = cbG C p t (fun u => cbW X u ω) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp' : (p : ℝ) ≠ 0 := by linarith
  unfold AR1Demand.sigmaHat cbG
  congr 3
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  simp only [AR1Demand.err, AR1Demand.Dhat, cbe, cbW, Finset.sum_sub_distrib, Finset.sum_const,
    Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, Nat.cast_one, one_mul]
  have : ∀ j : ℕ, t - (i : ℤ) - j = t - ((i : ℤ) + j) := fun j => by ring
  field_simp
  ring_nf

lemma cbG_meas (C : ℝ) (p : ℕ) (t : ℤ) : Measurable (cbG C p t) := by
  unfold cbG cbe; fun_prop

lemma cbEn_nonneg (p : ℕ) (t : ℤ) (w : ℤ → ℝ) : 0 ≤ cbEn p t w := by
  unfold cbEn
  exact Finset.sum_nonneg (fun i _ => add_nonneg (sq_nonneg _)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

lemma cbEn_int (X : AR1Demand P) (p : ℕ) (t k : ℤ) :
    Integrable (fun ω => cbEn p t (fun u => cbW X (u - k) ω)) P ∧
    ∫ ω, cbEn p t (fun u => cbW X (u - k) ω) ∂P =
      ∑ i ∈ Finset.Icc 1 p, (variance (X.D 0) P + ∑ j ∈ Finset.Icc 1 p, variance (X.D 0) P) := by
  unfold cbEn
  have hi : ∀ i : ℕ, Integrable (fun ω => cbW X (t - i - k) ω ^ 2 +
      ∑ j ∈ Finset.Icc 1 p, cbW X (t - i - j - k) ω ^ 2) P := fun i =>
    (cbW_sq_int X _).add (integrable_finsetSum _ (fun j _ => cbW_sq_int X _))
  refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hi i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_add (cbW_sq_int X _) (integrable_finsetSum _ (fun j _ => cbW_sq_int X _)),
    integral_finsetSum _ (fun j _ => cbW_sq_int X _), cbW_sq]
  simp only [cbW_sq]

lemma cb_real (A a B B' c r q E1 E2 : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hc : |c| = r)
    (hq0 : 0 ≤ q) (hBB : |B - B'| ≤ r * q) (hB : B ^ 2 ≤ E1) (hq : q ^ 2 ≤ E2) :
    |A * B - (A - c * a) * B'| ≤ r * ((3 / 2) * a ^ 2 + A ^ 2 + E1 / 2 + E2 / 2) := by
  have e : A * B - (A - c * a) * B' = c * a * B + (A - c * a) * (B - B') := by ring
  rw [e]
  have h1 : |c * a * B| ≤ r * ((a ^ 2 + B ^ 2) / 2) := by
    rw [abs_mul, abs_mul, hc, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hr0
    nlinarith [sq_abs a, sq_abs B, sq_nonneg (|a| - |B|)]
  have hca : (A - c * a) ^ 2 ≤ 2 * A ^ 2 + 2 * a ^ 2 := by
    have hc2 : c ^ 2 ≤ 1 := by
      rw [← sq_abs, hc]; nlinarith
    nlinarith [sq_nonneg (A + c * a), sq_nonneg a, mul_le_mul_of_nonneg_right hc2 (sq_nonneg a)]
  have h2 : |(A - c * a) * (B - B')| ≤ r * (((A - c * a) ^ 2 + q ^ 2) / 2) := by
    rw [abs_mul]
    calc |A - c * a| * |B - B'| ≤ |A - c * a| * (r * q) :=
          mul_le_mul_of_nonneg_left hBB (abs_nonneg _)
      _ = r * (|A - c * a| * q) := by ring
      _ ≤ r * (((A - c * a) ^ 2 + q ^ 2) / 2) := by
          apply mul_le_mul_of_nonneg_left _ hr0
          nlinarith [sq_abs (A - c * a), sq_nonneg (|A - c * a| - q)]
  calc |c * a * B + (A - c * a) * (B - B')| ≤ |c * a * B| + |(A - c * a) * (B - B')| :=
        abs_add_le _ _
    _ ≤ r * ((a ^ 2 + B ^ 2) / 2) + r * (((A - c * a) ^ 2 + q ^ 2) / 2) := add_le_add h1 h2
    _ ≤ r * ((3 / 2) * a ^ 2 + A ^ 2 + E1 / 2 + E2 / 2) := by
        rw [← mul_add]; apply mul_le_mul_of_nonneg_left _ hr0; nlinarith

theorem cbW_G (X : AR1Demand P) (C : ℝ) (p : ℕ) (hp : 1 ≤ p) (t s : ℤ) :
    ∫ ω, cbW X s ω * cbG C p t (fun u => cbW X u ω) ∂P = 0 := by
  set V := variance (X.D 0) P
  set Ec := ∑ i ∈ Finset.Icc 1 p, (V + ∑ j ∈ Finset.Icc 1 p, V)
  apply cb_zero_of_le_pow _ ((3 / 2) * V + V + C ^ 2 * Ec + C ^ 2 * Ec) X.rho X.abs_rho_lt_one
  intro n
  set r := |X.rho| ^ n with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := pow_le_one₀ (abs_nonneg _) X.abs_rho_lt_one.le
  have hc : |X.rho ^ n| = r := abs_pow _ _
  have hWp : Measurable (fun ω u => cbW X u ω) := measurable_pi_lambda _ (cbW_meas X)
  have hWsh : Measurable (fun ω u => cbW X (u - n) ω) :=
    measurable_pi_lambda _ (fun u => cbW_meas X _)
  -- the approximating path
  set Λ : (ℤ → ℝ) → (ℤ → ℝ) := fun x u => ∑ j ∈ Finset.range n, X.rho ^ j * x (u - j) with hΛ
  have hΛm : Measurable Λ := by
    apply measurable_pi_lambda; intro u
    apply Finset.measurable_sum; intro j _
    exact (measurable_pi_apply _).const_mul _
  have hY : ∀ ω, Λ (fun u => X.eps u ω) = fun u => cbW X u ω - X.rho ^ n * cbW X (u - n) ω := by
    intro ω; funext u; rw [cbW_expand X n u ω]; ring
  set ψ : (ℤ → ℝ) → ℝ := fun x => Λ x s * cbG C p t (Λ x) with hψ
  have hψm : Measurable ψ := ((measurable_pi_apply s).comp hΛm).mul ((cbG_meas C p t).comp hΛm)
  have hodd : ∀ x, ψ (-x) = -ψ x := by
    intro x
    have : Λ (-x) = -Λ x := by
      funext u; simp only [hΛ, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    simp only [hψ, this, cbG_neg, Pi.neg_apply, neg_mul]
  have hsym := cb_sym X ψ hψm hodd
  simp only [hψ, hY] at hsym
  -- functions
  set F : Ω → ℝ := fun ω => cbW X s ω * cbG C p t (fun u => cbW X u ω) with hF
  set F' : Ω → ℝ := fun ω => (cbW X s ω - X.rho ^ n * cbW X (s - n) ω) *
      cbG C p t (fun u => cbW X u ω - X.rho ^ n * cbW X (u - n) ω) with hF'
  set Z : Ω → ℝ := fun ω => (3 / 2) * cbW X (s - n) ω ^ 2 + cbW X s ω ^ 2
      + (2 * C ^ 2 * cbEn p t (fun u => cbW X (u - 0) ω)) / 2
      + (2 * C ^ 2 * cbEn p t (fun u => cbW X (u - n) ω)) / 2 with hZ
  have hEn0 := cbEn_int X p t 0
  have hEnn := cbEn_int X p t n
  have hZi : Integrable Z P :=
    ((((cbW_sq_int X _).const_mul _).add (cbW_sq_int X _)).add
      ((hEn0.1.const_mul _).div_const _)).add ((hEnn.1.const_mul _).div_const _)
  have hZint : ∫ ω, Z ω ∂P = (3 / 2) * V + V + C ^ 2 * Ec + C ^ 2 * Ec := by
    simp only [hZ]
    rw [integral_add, integral_add, integral_add, integral_const_mul, integral_div,
      integral_div, integral_const_mul, integral_const_mul, hEn0.2, hEnn.2, cbW_sq, cbW_sq]
    · ring
    · exact (cbW_sq_int X _).const_mul _
    · exact cbW_sq_int X _
    · exact ((cbW_sq_int X _).const_mul _).add (cbW_sq_int X _)
    · exact (hEn0.1.const_mul _).div_const _
    · exact (((cbW_sq_int X _).const_mul _).add (cbW_sq_int X _)).add
        ((hEn0.1.const_mul _).div_const _)
    · exact (hEnn.1.const_mul _).div_const _
  have hbound : ∀ ω, |F ω - F' ω| ≤ r * Z ω := by
    intro ω
    have hW0 : (fun u => cbW X (u - 0) ω) = fun u => cbW X u ω := by funext u; simp
    have hdiff : (fun u => cbW X u ω) - (fun u => cbW X u ω - X.rho ^ n * cbW X (u - n) ω)
        = fun u => X.rho ^ n * cbW X (u - n) ω := by funext u; simp
    have hGd := cbG_diff_sq_le C p hp t (fun u => cbW X u ω)
      (fun u => cbW X u ω - X.rho ^ n * cbW X (u - n) ω)
    rw [hdiff, cbEn_smul] at hGd
    set Q := 2 * C ^ 2 * cbEn p t (fun u => cbW X (u - n) ω)
    have hQ0 : 0 ≤ Q := by have := cbEn_nonneg p t (fun u => cbW X (u - n) ω); positivity
    have hBB : |cbG C p t (fun u => cbW X u ω) -
        cbG C p t (fun u => cbW X u ω - X.rho ^ n * cbW X (u - n) ω)| ≤ r * Real.sqrt Q := by
      have h2 : (cbG C p t (fun u => cbW X u ω) -
          cbG C p t (fun u => cbW X u ω - X.rho ^ n * cbW X (u - n) ω)) ^ 2 ≤ r ^ 2 * Q := by
        rw [← hc, sq_abs]; linarith
      calc _ ≤ Real.sqrt (r ^ 2 * Q) := Real.abs_le_sqrt h2
        _ = r * Real.sqrt Q := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr0]
    have hB : cbG C p t (fun u => cbW X u ω) ^ 2 ≤
        2 * C ^ 2 * cbEn p t (fun u => cbW X (u - 0) ω) := by
      rw [hW0]; exact cbG_sq_le C p hp t (fun u => cbW X u ω)
    have := cb_real (cbW X s ω) (cbW X (s - n) ω) (cbG C p t (fun u => cbW X u ω))
      (cbG C p t (fun u => cbW X u ω - X.rho ^ n * cbW X (u - n) ω)) (X.rho ^ n) r
      (Real.sqrt Q) _ _ hr0 hr1 hc (Real.sqrt_nonneg _) hBB hB (Real.sq_sqrt hQ0).le
    simpa [hF, hF', hZ] using this
  have hFm : AEStronglyMeasurable F P :=
    ((cbW_meas X s).mul ((cbG_meas C p t).comp hWp)).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable F' P := by
    have hYm : Measurable (fun ω u => cbW X u ω - X.rho ^ n * cbW X (u - n) ω) :=
      measurable_pi_lambda _ (fun u => (cbW_meas X u).sub ((cbW_meas X _).const_mul _))
    exact (((cbW_meas X s).sub ((cbW_meas X _).const_mul _)).mul
      ((cbG_meas C p t).comp hYm)).aestronglyMeasurable
  have hFi : Integrable F P := by
    refine Integrable.mono' (((cbW_sq_int X s).add (hEn0.1.const_mul (2 * C ^ 2))).div_const 2)
      hFm (Filter.Eventually.of_forall (fun ω => ?_))
    have hB := cbG_sq_le C p hp t (fun u => cbW X u ω)
    simp only [hF, Pi.add_apply, sub_zero, Real.norm_eq_abs, abs_mul]
    nlinarith [sq_abs (cbW X s ω), sq_abs (cbG C p t (fun u => cbW X u ω)),
      sq_nonneg (|cbW X s ω| - |cbG C p t (fun u => cbW X u ω)|)]
  have hDi : Integrable (fun ω => F ω - F' ω) P :=
    Integrable.mono' (hZi.const_mul r) (hFm.sub hF'm)
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hbound ω))
  have hF'i : Integrable F' P := by
    have : F' = fun ω => F ω - (F ω - F' ω) := by funext ω; ring
    rw [this]; exact hFi.sub hDi
  have hsplit : ∫ ω, F ω ∂P = ∫ ω, (F ω - F' ω) ∂P + ∫ ω, F' ω ∂P := by
    rw [← integral_add hDi hF'i]; congr 1; funext ω; ring
  have hF'0 : ∫ ω, F' ω ∂P = 0 := hsym
  change |∫ ω, F ω ∂P| ≤ _
  rw [hsplit, hF'0, add_zero, ← hZint, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono hDi.abs (hZi.const_mul r) hbound)


lemma cbS_memLp (X : AR1Demand P) (C : ℝ) (p : ℕ) (hp : 1 ≤ p) (t : ℤ) :
    MemLp (X.sigmaHat C p t) 2 P := by
  have hWp : Measurable (fun ω u => cbW X u ω) := measurable_pi_lambda _ (cbW_meas X)
  have he : X.sigmaHat C p t = fun ω => cbG C p t (fun u => cbW X u ω) := by
    funext ω; exact sigmaHat_eq X C p hp t ω
  rw [he]
  have hm : AEStronglyMeasurable (fun ω => cbG C p t (fun u => cbW X u ω)) P :=
    ((cbG_meas C p t).comp hWp).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm]
  refine Integrable.mono' ((cbEn_int X p t 0).1.const_mul (2 * C ^ 2)) (hm.pow 2)
    (Filter.Eventually.of_forall (fun ω => ?_))
  simp only [sub_zero, Real.norm_eq_abs]
  rw [abs_of_nonneg (sq_nonneg _)]
  exact cbG_sq_le C p hp t _

theorem cb_cov_DS (X : AR1Demand P) (C : ℝ) (p : ℕ) (hp : 1 ≤ p) (s t : ℤ) :
    covariance (X.D s) (X.sigmaHat C p t) P = 0 := by
  have hS := cbS_memLp X C p hp t
  have he : X.sigmaHat C p t = fun ω => cbG C p t (fun u => cbW X u ω) := by
    funext ω; exact sigmaHat_eq X C p hp t ω
  have hI : Integrable (fun ω => cbW X s ω * X.sigmaHat C p t ω) P :=
    cb_int_mul _ _ (cbW_memLp X s) hS
  have hWi : Integrable (cbW X s) P := (cbW_memLp X s).integrable one_le_two
  have hW0 : ∫ ω, cbW X s ω ∂P = 0 := by
    simp only [cbW]; rw [integral_sub ((X.D_memLp s).integrable one_le_two) (integrable_const _),
      cb_mean]; simp
  rw [covariance, cb_mean]
  change ∫ ω, cbW X s ω * (X.sigmaHat C p t ω - _) ∂P = 0
  simp only [mul_sub]
  rw [integral_sub hI (hWi.mul_const _), integral_mul_const, hW0, zero_mul, sub_zero]
  have := cbW_G X C p hp t s
  rw [he]; exact this

theorem lemma_2_1_core (X : AR1Demand P) (C : ℝ) (p : ℕ) (hp : 1 ≤ p)
    (t : ℤ) :
    ∀ i ∈ Finset.Icc 1 p,
      ProbabilityTheory.covariance (X.D (t - i)) (X.sigmaHat C p t) P = 0 :=
  fun i _ => cb_cov_DS X C p hp _ t

lemma cb_telescope (f : ℤ → ℝ) (t : ℤ) (p : ℕ) :
    ∑ i ∈ Finset.Icc 1 p, f (t - i) - ∑ i ∈ Finset.Icc 1 p, f (t - 1 - i)
      = f (t - 1) - f (t - p - 1) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    have : ∑ i ∈ Finset.Icc 1 p, f (t - i) + f (t - ((p + 1 : ℕ) : ℤ)) -
        (∑ i ∈ Finset.Icc 1 p, f (t - 1 - i) + f (t - 1 - ((p + 1 : ℕ) : ℤ)))
        = (∑ i ∈ Finset.Icc 1 p, f (t - i) - ∑ i ∈ Finset.Icc 1 p, f (t - 1 - i))
          + f (t - ((p + 1 : ℕ) : ℤ)) - f (t - 1 - ((p + 1 : ℕ) : ℤ)) := by ring
    rw [this, ih]
    have h1 : t - ((p + 1 : ℕ) : ℤ) = t - p - 1 := by push_cast; ring
    have h2 : t - 1 - ((p + 1 : ℕ) : ℤ) = t - ((p + 1 : ℕ) : ℤ) - 1 := by ring
    rw [h1, h2, h1]; push_cast; ring_nf

lemma cb_order_eq (X : AR1Demand P) (C z : ℝ) (L p : ℕ) (hp : 1 ≤ p) (t : ℤ) (ω : Ω) :
    X.order C z L p t ω = (1 + (L : ℝ) / p) * X.D (t - 1) ω - ((L : ℝ) / p) * X.D (t - p - 1) ω
      + z * (X.sigmaHat C p t ω - X.sigmaHat C p (t - 1) ω) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp' : (p : ℝ) ≠ 0 := by linarith
  have ht := cb_telescope (fun s => X.D s ω) t p
  simp only [AR1Demand.order, AR1Demand.orderUpTo, AR1Demand.Dhat]
  have : (L : ℝ) * ((∑ i ∈ Finset.Icc 1 p, X.D (t - i) ω) / p) -
      (L : ℝ) * ((∑ i ∈ Finset.Icc 1 p, X.D (t - 1 - i) ω) / p)
      = (L : ℝ) / p * (X.D (t - 1) ω - X.D (t - p - 1) ω) := by
    rw [← ht]; field_simp
  linear_combination this

theorem order_variance_core (X : AR1Demand P) (C z : ℝ) (L p : ℕ) (hp : 1 ≤ p)
    (t : ℤ) :
    ProbabilityTheory.variance (X.order C z L p t) P
      = (1 + (2 * (L : ℝ) / p + 2 * (L : ℝ) ^ 2 / (p : ℝ) ^ 2) * (1 - X.rho ^ p))
            * ProbabilityTheory.variance (X.D t) P
        + 2 * z * (1 + 2 * (L : ℝ) / p)
            * ProbabilityTheory.covariance (X.D (t - 1)) (X.sigmaHat C p t) P
        + z ^ 2 * ProbabilityTheory.variance
            (fun ω => X.sigmaHat C p t ω - X.sigmaHat C p (t - 1) ω) P := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp' : (p : ℝ) ≠ 0 := by linarith
  set a : ℝ := 1 + (L : ℝ) / p
  set b : ℝ := (L : ℝ) / p
  have hD1 := X.D_memLp (t - 1)
  have hD2 := X.D_memLp (t - p - 1)
  have hS1 := cbS_memLp X C p hp t
  have hS0 := cbS_memLp X C p hp (t - 1)
  have hfun : X.order C z L p t = (fun ω => a * X.D (t - 1) ω - b * X.D (t - p - 1) ω) +
      (fun ω => z * (X.sigmaHat C p t ω - X.sigmaHat C p (t - 1) ω)) := by
    funext ω; rw [cb_order_eq X C z L p hp t ω]; rfl
  have hU : MemLp (fun ω => a * X.D (t - 1) ω - b * X.D (t - p - 1) ω) 2 P :=
    (hD1.const_mul a).sub (hD2.const_mul b)
  have hΔ : MemLp (fun ω => X.sigmaHat C p t ω - X.sigmaHat C p (t - 1) ω) 2 P := hS1.sub hS0
  have hV' : MemLp (fun ω => z * (X.sigmaHat C p t ω - X.sigmaHat C p (t - 1) ω)) 2 P :=
    hΔ.const_mul z
  have hcovD : ∀ s, covariance (X.D s)
      (fun ω => X.sigmaHat C p t ω - X.sigmaHat C p (t - 1) ω) P = 0 := by
    intro s
    rw [covariance_fun_sub_right (X.D_memLp s) hS1 hS0, cb_cov_DS X C p hp, cb_cov_DS X C p hp]
    simp
  have hcov : covariance (fun ω => a * X.D (t - 1) ω - b * X.D (t - p - 1) ω)
      (fun ω => z * (X.sigmaHat C p t ω - X.sigmaHat C p (t - 1) ω)) P = 0 := by
    rw [covariance_const_mul_right,
      covariance_fun_sub_left (hD1.const_mul a) (hD2.const_mul b) hΔ,
      covariance_const_mul_left, covariance_const_mul_left, hcovD, hcovD]
    simp
  have hVU : variance (fun ω => a * X.D (t - 1) ω - b * X.D (t - p - 1) ω) P
      = a ^ 2 * variance (X.D 0) P - 2 * (a * b) * (X.rho ^ p * variance (X.D 0) P)
        + b ^ 2 * variance (X.D 0) P := by
    rw [variance_fun_sub (hD1.const_mul a) (hD2.const_mul b), variance_const_mul,
      variance_const_mul, covariance_const_mul_left, covariance_const_mul_right,
      (X.stationary (t - 1)).variance_eq, (X.stationary (t - p - 1)).variance_eq,
      (ar1_moments_core X p hp t).1, cb_V_eq]
    ring
  rw [hfun, variance_add hU hV', hcov, hVU, variance_const_mul, cb_cov_DS X C p hp,
    (X.stationary t).variance_eq]
  simp only [a, b]
  field_simp
  ring


theorem theorem_2_2_core (X : AR1Demand P) (C z : ℝ) (L p : ℕ) (hp : 1 ≤ p)
    (t : ℤ) :
    ProbabilityTheory.variance (X.order C z L p t) P / ProbabilityTheory.variance (X.D t) P
        ≥ 1 + (2 * (L : ℝ) / p + 2 * (L : ℝ) ^ 2 / (p : ℝ) ^ 2) * (1 - X.rho ^ p)
      ∧ (z = 0 →
          ProbabilityTheory.variance (X.order C z L p t) P / ProbabilityTheory.variance (X.D t) P
            = 1 + (2 * (L : ℝ) / p + 2 * (L : ℝ) ^ 2 / (p : ℝ) ^ 2) * (1 - X.rho ^ p)) := by
  have hV : 0 < variance (X.D t) P := by
    rw [(ar1_moments_core X p hp t).2]
    exact div_pos (pow_pos X.sigma_pos 2) (cb_one_sub_rho_sq_pos X)
  rw [order_variance_core X C z L p hp t, cb_cov_DS X C p hp]
  set A := 1 + (2 * (L : ℝ) / p + 2 * (L : ℝ) ^ 2 / (p : ℝ) ^ 2) * (1 - X.rho ^ p)
  have hvn := variance_nonneg (fun ω => X.sigmaHat C p t ω - X.sigmaHat C p (t - 1) ω) P
  refine ⟨?_, ?_⟩
  · rw [ge_iff_le, le_div_iff₀ hV]
    nlinarith [mul_nonneg (sq_nonneg z) hvn]
  · intro hz; subst hz
    rw [div_eq_iff hV.ne']; ring

lemma cb_sigmaHat_mul (X : AR1Demand P) (c : ℝ) (p : ℕ) (t : ℤ) (ω : Ω) :
    X.sigmaHat c p t ω = c * X.sigmaHat 1 p t ω := by
  simp only [AR1Demand.sigmaHat, one_mul]

lemma cb_Dhat_diff (X : AR1Demand P) (L p : ℕ) (hp : 1 ≤ p) (t : ℤ) (ω : Ω) :
    X.Dhat L p t ω - X.Dhat L p (t - 1) ω = (L : ℝ) / p * (X.D (t - 1) ω - X.D (t - p - 1) ω) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp' : (p : ℝ) ≠ 0 := by linarith
  have ht := cb_telescope (fun s => X.D s ω) t p
  simp only [AR1Demand.Dhat]
  rw [← ht]; field_simp

end ChenBullwhip.Centralized

open ChenBullwhip.Centralized


theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (C : ℝ) (p : ℕ) (hp : 1 ≤ p)
    (t : ℤ) :
    ∀ i ∈ Finset.Icc 1 p,
      ProbabilityTheory.covariance (X.D (t - i)) (X.sigmaHat C p t) P = 0 := by
  exact lemma_2_1_core X C p hp t
