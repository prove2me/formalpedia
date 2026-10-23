-- Prove2me | solution 1 for FedergruenZipkin.AvgCost.corollary1_hitting_sums
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:45:46.337252+00:00
-- url     : https://prove2.me/submissions/e5759736-701e-4b1e-8189-b7ac9a7bb199

import Mathlib
import Definitions.Def_FedergruenZipkin_AvgCost_Model



namespace FedergruenZipkin.AvgCost
open scoped ENNReal
open Filter Topology

/-- the characteristic function of the demand, as in `Model.charfun_analytic` -/
noncomputable def cf (M : Model) (θ : ℝ) : ℂ :=
  ∑' j : ℕ, ((M.p j : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ) * (j : ℂ))

lemma cf_term_summable (M : Model) (θ : ℝ) :
    Summable (fun j : ℕ => ((M.p j : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ) * (j : ℂ))) := by
  refine Summable.of_norm_bounded (g := M.p) M.p_sum.summable ?_
  intro j
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (M.p_nonneg j)]
  have : Complex.I * (θ : ℂ) * (j : ℂ) = ((θ * j : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- the symmetric-difference weights -/
def symW (k m : ℕ) : ℤ := (-1 : ℤ) ^ (2 * k - m) * ((2 * k).choose m : ℤ)

lemma abs_symW (k m : ℕ) : |symW k m| = (2 * k).choose m := by
  unfold symW
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]

lemma sum_choose_eq (n : ℕ) : ∑ m ∈ Finset.range (n + 1), ((n.choose m : ℕ) : ℝ) = (2 : ℝ) ^ n := by
  have := Nat.sum_range_choose n
  exact_mod_cast this

/-- the per-term identity: symmetric differences of exponentials give powers of sine -/
lemma sym_sum_exp (k : ℕ) (h : ℝ) (j : ℕ) :
    ∑ m ∈ Finset.range (2 * k + 1), ((symW k m : ℤ) : ℂ) *
        Complex.exp (Complex.I * ((-(k : ℝ) * h + m • h : ℝ) : ℂ) * (j : ℂ))
      = ((-4 : ℝ) ^ k * (Real.sin (h * j / 2)) ^ (2 * k) : ℝ) := by
  set a : ℂ := ((h * j / 2 : ℝ) : ℂ) with ha
  set E : ℂ := Complex.exp (Complex.I * a) with hE
  set F : ℂ := Complex.exp (-(Complex.I * a)) with hF
  have hexp : ∀ m : ℕ, Complex.exp (Complex.I * ((-(k : ℝ) * h + m • h : ℝ) : ℂ) * (j : ℂ))
      = (E ^ 2) ^ m * F ^ (2 * k) := by
    intro m
    rw [hE, hF, ← pow_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    rw [ha]; push_cast; ring
  have hEF : E * F = 1 := by
    rw [hE, hF, Complex.exp_neg, mul_inv_cancel₀ (Complex.exp_ne_zero _)]
  have hsin : E - F = 2 * Complex.I * Complex.sin a := by
    rw [hE, hF, Complex.sin]
    have : Complex.I * a = a * Complex.I := by ring
    rw [this, neg_mul]
    linear_combination (Complex.exp (a * Complex.I) - Complex.exp (-(a * Complex.I))) * Complex.I_sq
  simp_rw [hexp]
  have hbin : ∑ m ∈ Finset.range (2 * k + 1), ((symW k m : ℤ) : ℂ) * ((E ^ 2) ^ m * F ^ (2 * k))
      = (E ^ 2 + (-1)) ^ (2 * k) * F ^ (2 * k) := by
    rw [add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    unfold symW; push_cast; ring
  rw [hbin, ← mul_pow]
  have : (E ^ 2 + -1) * F = E - F := by linear_combination E * hEF
  rw [this, hsin, ha, ← Complex.ofReal_sin]
  push_cast
  rw [pow_mul, pow_mul]
  simp only [mul_pow, Complex.I_sq]
  rw [show (-4 : ℂ) = (-1) * 4 by norm_num, mul_pow]
  ring

lemma cf_sym_eq (M : Model) (k : ℕ) (h : ℝ) :
    ∑ m ∈ Finset.range (2 * k + 1), symW k m • cf M (-(k : ℝ) * h + m • h)
      = (((-4 : ℝ) ^ k * ∑' j : ℕ, M.p j * (Real.sin (h * j / 2)) ^ (2 * k) : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, Complex.ofReal_tsum]
  simp only [cf, zsmul_eq_mul]
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun m _ => (cf_term_summable M _).mul_left _)]
  refine tsum_congr (fun j => ?_)
  trans ((M.p j : ℝ) : ℂ) * ∑ m ∈ Finset.range (2 * k + 1), ((symW k m : ℤ) : ℂ) *
        Complex.exp (Complex.I * ((-(k : ℝ) * h + m • h : ℝ) : ℂ) * (j : ℂ))
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  · rw [sym_sum_exp k h j]
    push_cast; ring

lemma sin_term_summable (M : Model) (k : ℕ) (h : ℝ) :
    Summable (fun j : ℕ => M.p j * (Real.sin (h * j / 2)) ^ (2 * k)) := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) M.p_sum.summable
  · exact mul_nonneg (M.p_nonneg j) (by rw [pow_mul]; positivity)
  · have h1 : (Real.sin (h * j / 2)) ^ (2 * k) ≤ 1 := by
      rw [pow_mul]
      exact pow_le_one₀ (by positivity) (by nlinarith [Real.sin_sq_le_one (h * j / 2)])
    have := M.p_nonneg j
    nlinarith

/-- vanishing of the symmetric difference on monomials of low degree -/
lemma sum_shift_pow_zero (h : ℝ) (hh : h ≠ 0) {j n : ℕ} (hj : j < n) (y : ℝ) :
    ∑ m ∈ Finset.range (n + 1), (((-1 : ℤ) ^ (n - m) * (n.choose m : ℤ)) : ℤ) • (y + m • h) ^ j = 0 := by
  have key := fwdDiff_iter_eq_sum_shift (1 : ℝ) (fun r : ℝ => r ^ j) n (y / h)
  rw [fwdDiff_iter_pow_eq_zero_of_lt hj] at key
  simp only [Pi.zero_apply] at key
  have hm : ∀ m : ℕ, (y + m • h) ^ j = h ^ j * (y / h + m • (1 : ℝ)) ^ j := by
    intro m
    rw [← mul_pow]; congr 1; field_simp; ring
  simp_rw [hm, zsmul_eq_mul, nsmul_eq_mul] at key ⊢
  have : ∑ m ∈ Finset.range (n + 1), (((-1 : ℤ) ^ (n - m) * (n.choose m : ℤ) : ℤ) : ℝ) * (h ^ j * (y / h + m * 1) ^ j)
      = h ^ j * ∑ m ∈ Finset.range (n + 1), (((-1 : ℤ) ^ (n - m) * (n.choose m : ℤ) : ℤ) : ℝ) * (y / h + m * 1) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  rw [this, ← key, mul_zero]

lemma partialSum_eq (pf : FormalMultilinearSeries ℝ ℝ ℂ) (n : ℕ) (y : ℝ) :
    pf.partialSum n y = ∑ i ∈ Finset.range n, y ^ i • pf.coeff i := by
  unfold FormalMultilinearSeries.partialSum
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact FormalMultilinearSeries.apply_eq_pow_smul_coeff

lemma sym_partialSum_zero (pf : FormalMultilinearSeries ℝ ℝ ℂ) (k : ℕ) (h : ℝ) (hh : h ≠ 0) (y : ℝ) :
    ∑ m ∈ Finset.range (2 * k + 1), symW k m • pf.partialSum (2 * k) (y + m • h) = 0 := by
  simp_rw [partialSum_eq, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun i hi => ?_)
  have hi' := Finset.mem_range.1 hi
  simp_rw [← smul_assoc, ← Finset.sum_smul]
  have := sum_shift_pow_zero h hh hi' y
  unfold symW
  rw [this, zero_smul]

lemma cf_sym_bound (M : Model) (k : ℕ) (hk : 0 < k) : ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ∀ h : ℝ, |h| < ε →
    ‖∑ m ∈ Finset.range (2 * k + 1), symW k m • cf M (-(k : ℝ) * h + m • h)‖ ≤ C * |h| ^ (2 * k) := by
  have hA : AnalyticAt ℝ (cf M) 0 := M.charfun_analytic
  obtain ⟨pf, hpf⟩ := hA
  obtain ⟨C₁, hC₁⟩ := Asymptotics.isBigO_iff.1 (hpf.isBigO_sub_partialSum_pow (2 * k))
  obtain ⟨ε, hε, hb₁⟩ := Metric.eventually_nhds_iff.1 hC₁
  set C₀ : ℝ := max C₁ 0 with hC₀def
  have hC₀ : 0 ≤ C₀ := le_max_right _ _
  have hb : ∀ ⦃y : ℝ⦄, dist y 0 < ε →
      ‖cf M (0 + y) - pf.partialSum (2 * k) y‖ ≤ C₀ * ‖‖y‖ ^ (2 * k)‖ := by
    intro y hy
    refine (hb₁ hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  refine ⟨C₀ * 4 ^ k * ((k : ℝ) + 1) ^ (2 * k), ε / ((k : ℝ) + 1), by positivity, by positivity, ?_⟩
  intro h hh
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hh' : ((k : ℝ) + 1) * |h| < ε := by
    rw [lt_div_iff₀ hk1] at hh; linarith
  by_cases hh0 : h = 0
  · subst hh0
    have : ∀ m : ℕ, -(k : ℝ) * 0 + m • (0 : ℝ) = 0 := fun m => by simp
    simp only [this, ← Finset.sum_smul]
    have hz : ∑ m ∈ Finset.range (2 * k + 1), symW k m = 0 := by
      have := sum_shift_pow_zero (1 : ℝ) one_ne_zero (j := 0) (n := 2 * k) (by omega) 0
      simp only [pow_zero, zsmul_eq_mul, mul_one] at this
      unfold symW
      exact_mod_cast this
    rw [hz, zero_smul, norm_zero]
    positivity
  -- split cf = (cf - P) + P
  have hsplit : ∑ m ∈ Finset.range (2 * k + 1), symW k m •
          (cf M (0 + (-(k : ℝ) * h + m • h)) - pf.partialSum (2 * k) (-(k : ℝ) * h + m • h))
      = ∑ m ∈ Finset.range (2 * k + 1), symW k m • cf M (-(k : ℝ) * h + m • h) := by
    simp_rw [smul_sub, zero_add]
    rw [Finset.sum_sub_distrib, sym_partialSum_zero pf k h hh0, sub_zero]
  rw [← hsplit]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ m ∈ Finset.range (2 * k + 1),
      ‖symW k m • (cf M (0 + (-(k : ℝ) * h + m • h)) - pf.partialSum (2 * k) (-(k : ℝ) * h + m • h))‖
        ≤ ((2 * k).choose m : ℝ) * (C₀ * (((k : ℝ) + 1) * |h|) ^ (2 * k)) := by
    intro m hm
    have hm' : m ≤ 2 * k := by have := Finset.mem_range.1 hm; omega
    rw [norm_zsmul ℝ, Real.norm_eq_abs, ← Int.cast_abs, abs_symW]
    push_cast
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hy : dist (-(k : ℝ) * h + m • h) 0 < ε := by
      rw [dist_zero_right, Real.norm_eq_abs, nsmul_eq_mul]
      refine lt_of_le_of_lt ?_ hh'
      rw [show -(k : ℝ) * h + m * h = ((m : ℝ) - k) * h by ring, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rw [abs_le]
      constructor
      · have : (0 : ℝ) ≤ m := by positivity
        linarith
      · have : (m : ℝ) ≤ 2 * k := by exact_mod_cast hm'
        linarith
    refine (hb hy).trans ?_
    rw [Real.norm_eq_abs, abs_pow, Real.norm_eq_abs, abs_abs]
    refine mul_le_mul_of_nonneg_left ?_ hC₀
    · refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
      rw [nsmul_eq_mul, show -(k : ℝ) * h + m * h = ((m : ℝ) - k) * h by ring, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rw [abs_le]
      constructor
      · have : (0 : ℝ) ≤ m := by positivity
        linarith
      · have : (m : ℝ) ≤ 2 * k := by exact_mod_cast hm'
        linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul, sum_choose_eq, mul_pow, pow_mul, show ((2 : ℝ) ^ 2) = 4 by norm_num]
  apply le_of_eq
  ring


lemma sin_div_tendsto (j : ℕ) :
    Tendsto (fun h : ℝ => Real.sin (h * j / 2) / h) (𝓝[>] 0) (𝓝 ((j : ℝ) / 2)) := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp only [Nat.cast_zero, mul_zero, zero_div, Real.sin_zero]
    exact tendsto_const_nhds
  · have hj' : (0 : ℝ) < j := by exact_mod_cast hj
    have h1 : Tendsto (slope Real.sin 0) (𝓝[≠] 0) (𝓝 1) := by
      have := hasDerivAt_iff_tendsto_slope.1 (Real.hasDerivAt_sin 0)
      simpa using this
    have h2 : Tendsto (fun h : ℝ => h * j / 2) (𝓝[>] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun h : ℝ => h * j / 2) (𝓝 0) (𝓝 (0 * j / 2)) :=
          ((continuous_id.mul continuous_const).div_const _).tendsto 0
        simp only [zero_mul, zero_div] at this
        exact this.mono_left nhdsWithin_le_nhds
      · refine eventually_nhdsWithin_of_forall (fun h hh => ?_)
        simp only [Set.mem_Ioi] at hh
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        positivity
    have h3 := (h1.comp h2).const_mul ((j : ℝ) / 2)
    rw [mul_one] at h3
    refine h3.congr' ?_
    refine eventually_nhdsWithin_of_forall (fun h hh => ?_)
    simp only [Set.mem_Ioi] at hh
    simp only [Function.comp, slope_def_field, Real.sin_zero, sub_zero]
    field_simp

theorem even_moment_bound (M : Model) (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, ∀ N : ℕ, ∑ j ∈ Finset.range N, M.p j * (j : ℝ) ^ (2 * k) ≤ C := by
  obtain ⟨C, ε, hC, hε, hb⟩ := cf_sym_bound M k hk
  refine ⟨C, fun N => ?_⟩
  have hnn : ∀ (h : ℝ) (j : ℕ), 0 ≤ M.p j * (Real.sin (h * j / 2)) ^ (2 * k) :=
    fun h j => mul_nonneg (M.p_nonneg j) (by rw [pow_mul]; positivity)
  have key : ∀ h : ℝ, 0 < h → h < ε →
      ∑ j ∈ Finset.range N, M.p j * (Real.sin (h * j / 2) / h) ^ (2 * k) ≤ C / 4 ^ k := by
    intro h h0 hε'
    have hb' := hb h (by rw [abs_of_pos h0]; exact hε')
    rw [cf_sym_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0] at hb'
    have hS : 0 ≤ ∑' j : ℕ, M.p j * (Real.sin (h * j / 2)) ^ (2 * k) := tsum_nonneg (hnn h)
    have h4 : (4 : ℝ) ^ k * ∑' j : ℕ, M.p j * (Real.sin (h * j / 2)) ^ (2 * k) ≤ C * h ^ (2 * k) := by
      rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg hS] at hb'
      norm_num at hb'
      exact hb'
    have hpart : ∑ j ∈ Finset.range N, M.p j * (Real.sin (h * j / 2)) ^ (2 * k)
        ≤ ∑' j : ℕ, M.p j * (Real.sin (h * j / 2)) ^ (2 * k) :=
      Summable.sum_le_tsum _ (fun j _ => hnn h j) (sin_term_summable M k h)
    have hh : 0 < h ^ (2 * k) := by positivity
    have h4k : (0 : ℝ) < 4 ^ k := by positivity
    have hrw : ∑ j ∈ Finset.range N, M.p j * (Real.sin (h * j / 2) / h) ^ (2 * k)
        = (∑ j ∈ Finset.range N, M.p j * (Real.sin (h * j / 2)) ^ (2 * k)) / h ^ (2 * k) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [div_pow]; ring
    rw [hrw, div_le_div_iff₀ hh h4k]
    have := mul_le_mul_of_nonneg_right hpart h4k.le
    linarith
  have hlim : Tendsto (fun h : ℝ => ∑ j ∈ Finset.range N, M.p j * (Real.sin (h * j / 2) / h) ^ (2 * k))
      (𝓝[>] 0) (𝓝 (∑ j ∈ Finset.range N, M.p j * ((j : ℝ) / 2) ^ (2 * k))) := by
    refine tendsto_finset_sum _ (fun j _ => ?_)
    exact ((sin_div_tendsto j).pow (2 * k)).const_mul (M.p j)
  have hle : ∑ j ∈ Finset.range N, M.p j * ((j : ℝ) / 2) ^ (2 * k) ≤ C / 4 ^ k := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hε] with h hh
    exact key h hh.1 hh.2
  have h2 : ((2 : ℝ)) ^ (2 * k) = 4 ^ k := by rw [pow_mul]; norm_num
  have hrw : ∑ j ∈ Finset.range N, M.p j * (j : ℝ) ^ (2 * k)
      = 4 ^ k * ∑ j ∈ Finset.range N, M.p j * ((j : ℝ) / 2) ^ (2 * k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [div_pow, h2]
    field_simp
  rw [hrw]
  have h4k : (0 : ℝ) < 4 ^ k := by positivity
  calc 4 ^ k * ∑ j ∈ Finset.range N, M.p j * ((j : ℝ) / 2) ^ (2 * k) ≤ 4 ^ k * (C / 4 ^ k) := by gcongr
    _ = C := by field_simp

/-- all moments of the demand are finite (Assumption 2) -/
theorem moment_summable (M : Model) (i : ℕ) : Summable (fun j : ℕ => M.p j * (j : ℝ) ^ i) := by
  obtain ⟨C, hC⟩ := even_moment_bound M (i + 1) (by omega)
  have hle : ∀ j : ℕ, M.p j * (j : ℝ) ^ i ≤ M.p j * (1 + (j : ℝ) ^ (2 * (i + 1))) := by
    intro j
    refine mul_le_mul_of_nonneg_left ?_ (M.p_nonneg j)
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have : ((0 : ℕ) : ℝ) ^ i ≤ 1 := pow_le_one₀ (by simp) (by simp)
      have : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) ^ (2 * (i + 1)) := by positivity
      linarith
    · have : (1 : ℝ) ≤ j := by exact_mod_cast hj
      have := pow_le_pow_right₀ this (show i ≤ 2 * (i + 1) by omega)
      linarith
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (M.p_nonneg j) (by positivity)) hle ?_
  have h1 : Summable (fun j : ℕ => M.p j * (j : ℝ) ^ (2 * (i + 1))) :=
    summable_of_sum_range_le (fun j => mul_nonneg (M.p_nonneg j) (by positivity)) hC
  have h2 := M.p_sum.summable.add h1
  refine h2.congr (fun j => ?_)
  ring

/-- moments of shifted demand -/
theorem summable_p_mul_pow_add (M : Model) (c : ℝ) (m : ℕ) :
    Summable (fun j : ℕ => M.p j * ((j : ℝ) + c) ^ m) := by
  have : (fun j : ℕ => M.p j * ((j : ℝ) + c) ^ m)
      = fun j : ℕ => ∑ i ∈ Finset.range (m + 1), (c ^ (m - i) * (m.choose i : ℝ)) * (M.p j * (j : ℝ) ^ i) := by
    funext j
    rw [add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [this]
  exact summable_sum (fun i _ => (moment_summable M i).mul_left _)


/-! ### Comparison theorem for the taboo operator -/

lemma tabooP_mono (M : Model) (δ : ℤ → ℤ) (ι : Set ℤ) {w w' : ℤ → ℝ≥0∞} (U : ℤ)
    (hδ : ∀ x ≤ U, δ x ≤ U) (h : ∀ z ≤ U, w z ≤ w' z) :
    ∀ x ≤ U, tabooP M δ ι w x ≤ tabooP M δ ι w' x := by
  intro x hx
  unfold tabooP
  refine ENNReal.tsum_le_tsum (fun j => ?_)
  gcongr
  have hz : δ x - j ≤ U := by have := hδ x hx; omega
  exact h _ hz

lemma tabooP_finset_sum (M : Model) (δ : ℤ → ℤ) (ι : Set ℤ) (n : ℕ) (g : ℕ → ℤ → ℝ≥0∞) (x : ℤ) :
    tabooP M δ ι (fun z => ∑ t ∈ Finset.range n, g t z) x
      = ∑ t ∈ Finset.range n, tabooP M δ ι (g t) x := by
  unfold tabooP
  have : ∀ j : ℕ, ENNReal.ofReal (M.p j) * Set.indicator ιᶜ (fun z => ∑ t ∈ Finset.range n, g t z) (δ x - j)
      = ∑ t ∈ Finset.range n, ENNReal.ofReal (M.p j) * Set.indicator ιᶜ (g t) (δ x - j) := by
    intro j
    by_cases hmem : δ x - j ∈ ιᶜ
    · simp only [Set.indicator_of_mem hmem, Finset.mul_sum]
    · simp only [Set.indicator_of_notMem hmem, Finset.sum_const_zero, mul_zero]
  simp_rw [this]
  exact Summable.tsum_finsetSum (fun t _ => ENNReal.summable)

lemma comparison (M : Model) (δ : ℤ → ℤ) (ι : Set ℤ) (U : ℤ) (hδ : ∀ x ≤ U, δ x ≤ U)
    (f W : ℤ → ℝ≥0∞) (hW : ∀ x ≤ U, f x + tabooP M δ ι W x ≤ W x) :
    ∀ n : ℕ, ∀ x ≤ U, ∑ t ∈ Finset.range n, (tabooP M δ ι)^[t] f x ≤ W x := by
  intro n
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    rw [Finset.sum_range_succ']
    simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply']
    have e := tabooP_finset_sum M δ ι n (fun t => (tabooP M δ ι)^[t] f) x
    rw [← e, add_comm]
    calc f x + tabooP M δ ι (fun z => ∑ t ∈ Finset.range n, (tabooP M δ ι)^[t] f z) x
        ≤ f x + tabooP M δ ι W x :=
          add_le_add le_rfl (tabooP_mono M δ ι U hδ (fun z hz => ih z hz) x hx)
      _ ≤ W x := hW x hx

lemma hitSum_le (M : Model) (δ : ℤ → ℤ) (ι : Set ℤ) (U : ℤ) (hδ : ∀ x ≤ U, δ x ≤ U)
    (v W : ℤ → ℝ≥0∞) (hW : ∀ x ≤ U, v (δ x) + tabooP M δ ι W x ≤ W x) :
    ∀ x ≤ U, hitSum M δ ι v x ≤ W x := by
  intro x hx
  unfold hitSum
  rw [ENNReal.tsum_eq_iSup_nat]
  exact iSup_le (fun n => comparison M δ ι U hδ (fun z => v (δ z)) W hW n x hx)

lemma H_le (M : Model) (U l u : ℤ) (v W : ℤ → ℝ≥0∞)
    (hW : ∀ δ, DeltaIota M U l u δ → ∀ x ≤ U, v (δ x) + tabooP M δ (Set.Icc l u) W x ≤ W x) :
    ∀ x ≤ U, H M U l u v x ≤ W x := by
  intro x hx
  unfold H
  refine iSup_le (fun δ => iSup_le (fun hδ => ?_))
  exact hitSum_le M δ _ U (fun z hz => (hδ.1 z hz).2.2) v W (hW δ hδ) x hx

/-! ### Real-analysis helpers -/

lemma pow_sub_le (n : ℕ) (a t : ℝ) (ht : 0 ≤ t) (hta : t ≤ a) :
    (a - t) ^ (n + 1) ≤ a ^ (n + 1) - t * a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0 : 0 ≤ a - t := by linarith
    have han : 0 ≤ a ^ n := pow_nonneg (by linarith) n
    calc (a - t) ^ (n + 1 + 1) = (a - t) ^ (n + 1) * (a - t) := pow_succ _ _
      _ ≤ (a ^ (n + 1) - t * a ^ n) * (a - t) := mul_le_mul_of_nonneg_right ih h0
      _ = a ^ (n + 2) - t * a ^ (n + 1) - t * a ^ n * (a - t) := by ring
      _ ≤ a ^ (n + 1 + 1) - t * a ^ (n + 1) := by
          have : 0 ≤ t * a ^ n * (a - t) := mul_nonneg (mul_nonneg ht han) h0
          linarith

lemma poly_bound (n : ℕ) (a t : ℝ) (ha : 1 ≤ a) :
    (a + t) ^ (n + 2) ≤ a ^ (n + 2) + (n + 2) * a ^ (n + 1) * t
      + (n + 1) * 2 ^ (n + 2) * a ^ n * (1 + |t|) ^ (n + 2) := by
  have ha0 : 0 ≤ a := by linarith
  have hT : 0 ≤ 1 + |t| := by linarith [abs_nonneg t]
  rw [add_comm a t, add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
  have e0 : t ^ 0 * a ^ (n + 2 - 0) * ((n + 2).choose 0 : ℝ) = a ^ (n + 2) := by simp
  have e1 : t ^ (0 + 1) * a ^ (n + 2 - (0 + 1)) * ((n + 2).choose (0 + 1) : ℝ)
      = (n + 2) * a ^ (n + 1) * t := by
    rw [show n + 2 - (0 + 1) = n + 1 by omega, zero_add, pow_one, Nat.choose_one_right]
    push_cast; ring
  rw [e0, e1]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      t ^ (i + 1 + 1) * a ^ (n + 2 - (i + 1 + 1)) * ((n + 2).choose (i + 1 + 1) : ℝ)
        ≤ 2 ^ (n + 2) * a ^ n * (1 + |t|) ^ (n + 2) := by
    intro i hi
    have hi' : i ≤ n := by have := Finset.mem_range.1 hi; omega
    have h1 : t ^ (i + 1 + 1) ≤ (1 + |t|) ^ (n + 2) := by
      calc t ^ (i + 1 + 1) ≤ |t ^ (i + 1 + 1)| := le_abs_self _
        _ = |t| ^ (i + 1 + 1) := abs_pow _ _
        _ ≤ (1 + |t|) ^ (i + 1 + 1) := pow_le_pow_left₀ (abs_nonneg _) (by linarith) _
        _ ≤ (1 + |t|) ^ (n + 2) := pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega)
    have h2 : a ^ (n + 2 - (i + 1 + 1)) ≤ a ^ n := pow_le_pow_right₀ ha (by omega)
    have h3 : ((n + 2).choose (i + 1 + 1) : ℝ) ≤ 2 ^ (n + 2) := by
      exact_mod_cast Nat.choose_le_two_pow _ _
    have h4 : 0 ≤ a ^ (n + 2 - (i + 1 + 1)) := by positivity
    have h5 : (0:ℝ) ≤ (n + 2).choose (i + 1 + 1) := by positivity
    calc t ^ (i + 1 + 1) * a ^ (n + 2 - (i + 1 + 1)) * ((n + 2).choose (i + 1 + 1) : ℝ)
        = t ^ (i + 1 + 1) * (a ^ (n + 2 - (i + 1 + 1)) * ((n + 2).choose (i + 1 + 1) : ℝ)) := by ring
      _ ≤ (1 + |t|) ^ (n + 2) * (a ^ n * 2 ^ (n + 2)) :=
          mul_le_mul h1 (mul_le_mul h2 h3 h5 (pow_nonneg ha0 n)) (mul_nonneg h4 h5) (pow_nonneg hT _)
      _ = 2 ^ (n + 2) * a ^ n * (1 + |t|) ^ (n + 2) := by ring
  have hsum := Finset.sum_le_sum hterm
  have hcast : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hcast] at hsum
  linarith

lemma pow_add_le_two_pow (m : ℕ) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (r + s) ^ m ≤ 2 ^ m * (r ^ m + s ^ m) := by
  have h1 : r + s ≤ 2 * max r s := by
    have := le_max_left r s; have := le_max_right r s; linarith
  have h2 : (max r s) ^ m ≤ r ^ m + s ^ m := by
    rcases le_total r s with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg hr m]
    · rw [max_eq_left h]; linarith [pow_nonneg hs m]
  calc (r + s) ^ m ≤ (2 * max r s) ^ m := pow_le_pow_left₀ (by linarith) h1 _
    _ = 2 ^ m * (max r s) ^ m := mul_pow _ _ _
    _ ≤ 2 ^ m * (r ^ m + s ^ m) := by gcongr

lemma abs_pow_le_one_add (q : ℕ) (x : ℝ) : |x| ^ (q + 1) ≤ 1 + |x| ^ (q + 3) := by
  rcases le_or_gt 1 |x| with h | h
  · have := pow_le_pow_right₀ h (show q + 1 ≤ q + 3 by omega)
    linarith
  · have := pow_le_one₀ (abs_nonneg x) h.le (n := q + 1)
    have := pow_nonneg (abs_nonneg x) (q + 3)
    linarith



/-! ### Lyapunov step in `ℝ≥0∞` -/

lemma lyap_step (M : Model) (ι : Set ℤ) (Wr : ℤ → ℝ) (wy : ℝ) (hwy : 0 ≤ wy) (y : ℤ) (Wx : ℝ)
    (g : ℕ → ℝ) (hg0 : ∀ j, 0 ≤ g j) (hgs : Summable (fun j => M.p j * g j))
    (hWr : ∀ j : ℕ, Set.indicator ιᶜ Wr (y - j) ≤ g j)
    (hmain : wy + ∑' j, M.p j * g j ≤ Wx) :
    ENNReal.ofReal wy + ∑' j : ℕ, ENNReal.ofReal (M.p j) *
        Set.indicator ιᶜ (fun z => ENNReal.ofReal (Wr z)) (y - j) ≤ ENNReal.ofReal Wx := by
  have hpg : ∀ j, 0 ≤ M.p j * g j := fun j => mul_nonneg (M.p_nonneg j) (hg0 j)
  have h1 : ∀ j : ℕ, ENNReal.ofReal (M.p j) * Set.indicator ιᶜ (fun z => ENNReal.ofReal (Wr z)) (y - j)
      ≤ ENNReal.ofReal (M.p j * g j) := by
    intro j
    rw [ENNReal.ofReal_mul (M.p_nonneg j)]
    gcongr
    have : Set.indicator ιᶜ (fun z => ENNReal.ofReal (Wr z)) (y - j)
        = ENNReal.ofReal (Set.indicator ιᶜ Wr (y - j)) := by
      by_cases hmem : y - j ∈ ιᶜ
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, ENNReal.ofReal_zero]
    rw [this]
    exact ENNReal.ofReal_le_ofReal (hWr j)
  calc ENNReal.ofReal wy + ∑' j : ℕ, ENNReal.ofReal (M.p j) *
          Set.indicator ιᶜ (fun z => ENNReal.ofReal (Wr z)) (y - j)
      ≤ ENNReal.ofReal wy + ∑' j : ℕ, ENNReal.ofReal (M.p j * g j) :=
        add_le_add le_rfl (ENNReal.tsum_le_tsum h1)
    _ = ENNReal.ofReal (wy + ∑' j, M.p j * g j) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg hpg hgs, ENNReal.ofReal_add hwy (tsum_nonneg hpg)]
    _ ≤ ENNReal.ofReal Wx := ENNReal.ofReal_le_ofReal hmain

lemma mean_summable (M : Model) : Summable (fun j : ℕ => (j : ℝ) * M.p j) :=
  (moment_summable M 1).congr (fun j => by ring)

lemma p0_lt_one (M : Model) : M.p 0 < 1 := by
  have h := M.cdf_b_lt_one
  have : M.p 0 ≤ ∑ j ∈ Finset.range (M.b + 1), M.p j :=
    Finset.single_le_sum (fun j _ => M.p_nonneg j) (Finset.mem_range.2 (by omega))
  linarith

lemma kappa_pos (M : Model) : 0 < (M.b : ℝ) - ∑' j : ℕ, (j : ℝ) * M.p j := by
  have := M.mean_lt_b; linarith

/-- the drift inequality below the taboo interval -/
lemma drift_below (M : Model) (N : ℕ) (a : ℝ) (ha : 1 ≤ a) :
    ∑' j : ℕ, M.p j * (a + ((j : ℝ) - M.b)) ^ (N + 2)
      ≤ a ^ (N + 2) + (N + 2) * a ^ (N + 1) * ((∑' j : ℕ, (j : ℝ) * M.p j) - M.b)
        + (N + 1) * 2 ^ (N + 2) * a ^ N * ∑' j : ℕ, M.p j * ((j : ℝ) + (1 + M.b)) ^ (N + 2) := by
  have hterm : ∀ j : ℕ, M.p j * (a + ((j : ℝ) - M.b)) ^ (N + 2)
      ≤ (a ^ (N + 2) - (N + 2) * a ^ (N + 1) * M.b) * M.p j
        + ((N + 2) * a ^ (N + 1)) * ((j : ℝ) * M.p j)
        + ((N + 1) * 2 ^ (N + 2) * a ^ N) * (M.p j * ((j : ℝ) + (1 + M.b)) ^ (N + 2)) := by
    intro j
    have h1 := poly_bound N a ((j : ℝ) - M.b) ha
    have h2 : (1 + |(j : ℝ) - M.b|) ^ (N + 2) ≤ ((j : ℝ) + (1 + M.b)) ^ (N + 2) := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have hj : (0 : ℝ) ≤ j := by positivity
      have hb : (0 : ℝ) ≤ M.b := by positivity
      have : |(j : ℝ) - M.b| ≤ j + M.b := by
        rw [abs_le]; constructor <;> linarith
      linarith
    have h3 : (a + ((j : ℝ) - M.b)) ^ (N + 2)
        ≤ a ^ (N + 2) + (N + 2) * a ^ (N + 1) * ((j : ℝ) - M.b)
          + (N + 1) * 2 ^ (N + 2) * a ^ N * ((j : ℝ) + (1 + M.b)) ^ (N + 2) := by
      refine h1.trans ?_
      have : 0 ≤ (N + 1 : ℝ) * 2 ^ (N + 2) * a ^ N := by positivity
      have := mul_le_mul_of_nonneg_left h2 this
      linarith
    calc M.p j * (a + ((j : ℝ) - M.b)) ^ (N + 2)
        ≤ M.p j * (a ^ (N + 2) + (N + 2) * a ^ (N + 1) * ((j : ℝ) - M.b)
          + (N + 1) * 2 ^ (N + 2) * a ^ N * ((j : ℝ) + (1 + M.b)) ^ (N + 2)) :=
          mul_le_mul_of_nonneg_left h3 (M.p_nonneg j)
      _ = _ := by ring
  have s1 : Summable (fun j : ℕ => (a ^ (N + 2) - (N + 2) * a ^ (N + 1) * M.b) * M.p j) :=
    M.p_sum.summable.mul_left _
  have s2 : Summable (fun j : ℕ => ((N + 2) * a ^ (N + 1)) * ((j : ℝ) * M.p j)) :=
    (mean_summable M).mul_left _
  have s3 : Summable (fun j : ℕ => ((N + 1) * 2 ^ (N + 2) * a ^ N) *
      (M.p j * ((j : ℝ) + (1 + M.b)) ^ (N + 2))) :=
    (summable_p_mul_pow_add M (1 + M.b) (N + 2)).mul_left _
  have sL : Summable (fun j : ℕ => M.p j * (a + ((j : ℝ) - M.b)) ^ (N + 2)) :=
    (summable_p_mul_pow_add M (a - M.b) (N + 2)).congr (fun j => by ring_nf)
  refine le_trans (Summable.tsum_le_tsum hterm sL ((s1.add s2).add s3)) (le_of_eq ?_)
  rw [Summable.tsum_add (s1.add s2) s3, Summable.tsum_add s1 s2, tsum_mul_left, tsum_mul_left,
    tsum_mul_left, M.p_sum.tsum_eq]
  ring

/-- the real Lyapunov function -/
noncomputable def Wfun (l u : ℤ) (N : ℕ) (c K c₂ Cι : ℝ) (z : ℤ) : ℝ :=
  if z < l then c * ((l : ℝ) - z + K) ^ (N + 2)
  else if z ≤ u then Cι else c₂ * ((z : ℝ) - u + 1) ^ (N + 2)

lemma Wfun_lo (l u : ℤ) (N : ℕ) (c K c₂ Cι : ℝ) (z : ℤ) (hz : z < l) :
    Wfun l u N c K c₂ Cι z = c * ((l : ℝ) - z + K) ^ (N + 2) := by
  unfold Wfun; rw [if_pos hz]

lemma Wfun_mid (l u : ℤ) (N : ℕ) (c K c₂ Cι : ℝ) (z : ℤ) (hz1 : l ≤ z) (hz2 : z ≤ u) :
    Wfun l u N c K c₂ Cι z = Cι := by
  unfold Wfun; rw [if_neg (by omega), if_pos hz2]

lemma Wfun_hi (l u : ℤ) (N : ℕ) (c K c₂ Cι : ℝ) (z : ℤ) (hz : u < z) (hlu : l ≤ u) :
    Wfun l u N c K c₂ Cι z = c₂ * ((z : ℝ) - u + 1) ^ (N + 2) := by
  unfold Wfun; rw [if_neg (by omega), if_neg (by omega)]

lemma Wfun_nonneg (l u : ℤ) (N : ℕ) (c K c₂ Cι : ℝ) (hc : 0 ≤ c) (hK : 0 ≤ K) (hc₂ : 0 ≤ c₂)
    (hCι : 0 ≤ Cι) (hlu : l ≤ u) (z : ℤ) : 0 ≤ Wfun l u N c K c₂ Cι z := by
  unfold Wfun
  split_ifs with h1 h2
  · have : (z : ℝ) < l := by exact_mod_cast h1
    have : 0 ≤ (l : ℝ) - z + K := by linarith
    positivity
  · exact hCι
  · have : (u : ℝ) < z := by exact_mod_cast (not_le.1 h2)
    have : 0 ≤ (z : ℝ) - u + 1 := by linarith
    positivity

/-- the growth bound of the Lyapunov function -/
lemma Wfun_growth (l u : ℤ) (N : ℕ) (c K c₂ Cι : ℝ) (hc : 0 ≤ c) (hK : 0 ≤ K) (hc₂ : 0 ≤ c₂)
    (hCι : 0 ≤ Cι) (hlu : l ≤ u) (z : ℤ) :
    Wfun l u N c K c₂ Cι z ≤
      (c * 2 ^ (N + 2) * (|(l : ℝ)| + K) ^ (N + 2) + Cι + c₂ * 2 ^ (N + 2) * (|(u : ℝ)| + 1) ^ (N + 2))
        + (c * 2 ^ (N + 2) + c₂ * 2 ^ (N + 2)) * |(z : ℝ)| ^ (N + 2) := by
  have hA1 : 0 ≤ c * 2 ^ (N + 2) * (|(l : ℝ)| + K) ^ (N + 2) := by positivity
  have hA2 : 0 ≤ c₂ * 2 ^ (N + 2) * (|(u : ℝ)| + 1) ^ (N + 2) := by positivity
  have hB1 : 0 ≤ c * 2 ^ (N + 2) * |(z : ℝ)| ^ (N + 2) := by positivity
  have hB2 : 0 ≤ c₂ * 2 ^ (N + 2) * |(z : ℝ)| ^ (N + 2) := by positivity
  unfold Wfun
  split_ifs with h1 h2
  · have hz : (z : ℝ) < l := by exact_mod_cast h1
    have h0 : 0 ≤ (l : ℝ) - z + K := by linarith
    have hle : (l : ℝ) - z + K ≤ (|(l : ℝ)| + K) + |(z : ℝ)| := by
      linarith [le_abs_self (l : ℝ), neg_le_abs (z : ℝ)]
    have := pow_add_le_two_pow (N + 2) (|(l : ℝ)| + K) |(z : ℝ)| (by positivity) (abs_nonneg _)
    have := pow_le_pow_left₀ h0 hle (N + 2)
    nlinarith
  · nlinarith
  · have hz : (u : ℝ) < z := by exact_mod_cast (not_le.1 h2)
    have h0 : 0 ≤ (z : ℝ) - u + 1 := by linarith
    have hle : (z : ℝ) - u + 1 ≤ (|(u : ℝ)| + 1) + |(z : ℝ)| := by
      linarith [le_abs_self (z : ℝ), neg_le_abs (u : ℝ)]
    have := pow_add_le_two_pow (N + 2) (|(u : ℝ)| + 1) |(z : ℝ)| (by positivity) (abs_nonneg _)
    have := pow_le_pow_left₀ h0 hle (N + 2)
    nlinarith

/-- region below `l` -/
lemma region_below (M : Model) (U l u : ℤ) (N : ℕ) (w : ℤ → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw : ∀ x ≤ U, |w x| ≤ A + B * |(x : ℝ)| ^ (N + 1))
    (hlu : l ≤ u - M.b) (huU : u ≤ U)
    (c K c₂ Cι : ℝ) (hc : 0 ≤ c) (hK1 : 1 ≤ K) (hKb : (M.b : ℝ) ≤ K)
    (hdrift : ∀ a : ℝ, K ≤ a →
      c * ∑' j : ℕ, M.p j * (a + ((j : ℝ) - M.b)) ^ (N + 2)
        + (A + B * (|(l : ℝ) + M.b| + 1) ^ (N + 1)) * a ^ (N + 1) ≤ c * a ^ (N + 2))
    (x : ℤ) (hx : x < l) :
    ENNReal.ofReal (w (x + M.b)) + tabooP M (fun _ => x + M.b) (Set.Icc l u)
        (fun z => ENNReal.ofReal (Wfun l u N c K c₂ Cι z)) x
      ≤ ENNReal.ofReal (Wfun l u N c K c₂ Cι x) := by
  unfold tabooP
  set a : ℝ := (l : ℝ) - x + K with ha
  have hxl : (x : ℝ) < l := by exact_mod_cast hx
  have hd1 : 1 ≤ (l : ℝ) - x := by
    have : x + 1 ≤ l := hx
    have : ((x : ℝ) + 1) ≤ l := by exact_mod_cast this
    linarith
  have haK : K ≤ a := by rw [ha]; linarith
  have ha1 : 1 ≤ a := le_trans hK1 haK
  have hab : (M.b : ℝ) ≤ a := le_trans hKb haK
  have hxb : x + M.b ≤ U := by omega
  refine le_trans (add_le_add (ENNReal.ofReal_le_ofReal (le_abs_self _)) le_rfl) ?_
  refine lyap_step M (Set.Icc l u) _ |w (x + M.b)| (abs_nonneg _) (x + M.b) _
    (fun j => c * (a + ((j : ℝ) - M.b)) ^ (N + 2)) ?_ ?_ ?_ ?_
  · intro j
    have : 0 ≤ a + ((j : ℝ) - M.b) := by
      have : (0 : ℝ) ≤ j := by positivity
      linarith
    positivity
  · refine ((summable_p_mul_pow_add M (a - M.b) (N + 2)).mul_left c).congr (fun j => ?_)
    ring_nf
  · intro j
    by_cases hmem : x + M.b - j ∈ Set.Icc l u
    · rw [Set.indicator_of_notMem (by simpa using hmem)]
      have : 0 ≤ a + ((j : ℝ) - M.b) := by
        have : (0 : ℝ) ≤ j := by positivity
        linarith
      positivity
    · rw [Set.indicator_of_mem (by simpa using hmem)]
      have hlt : x + M.b - j < l := by
        rw [Set.mem_Icc] at hmem
        omega
      rw [Wfun_lo _ _ _ _ _ _ _ _ hlt]
      apply le_of_eq
      congr 1
      rw [ha]; push_cast; ring
  · have hwx := hw (x + M.b) hxb
    have hsum : ∑' j : ℕ, M.p j * (c * (a + ((j : ℝ) - M.b)) ^ (N + 2))
        = c * ∑' j : ℕ, M.p j * (a + ((j : ℝ) - M.b)) ^ (N + 2) := by
      rw [← tsum_mul_left]
      exact tsum_congr (fun j => by ring)
    rw [hsum, Wfun_lo _ _ _ _ _ _ _ _ hx]
    have hd := hdrift a haK
    -- |x + b| ≤ (|l + b| + 1) * a
    have habs : |((x + M.b : ℤ) : ℝ)| ≤ (|(l : ℝ) + M.b| + 1) * a := by
      push_cast
      have h1 : |(x : ℝ) + M.b| ≤ |(l : ℝ) + M.b| + ((l : ℝ) - x) := by
        have : (x : ℝ) + M.b = ((l : ℝ) + M.b) - ((l : ℝ) - x) := by ring
        rw [this]
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (l : ℝ) - x)]
      have h2 : (l : ℝ) - x ≤ a := by rw [ha]; linarith
      have h3 : 0 ≤ |(l : ℝ) + M.b| := abs_nonneg _
      nlinarith
    have hpow : |((x + M.b : ℤ) : ℝ)| ^ (N + 1) ≤ (|(l : ℝ) + M.b| + 1) ^ (N + 1) * a ^ (N + 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) habs _
    have haN : 1 ≤ a ^ (N + 1) := one_le_pow₀ ha1
    have hwx' : |w (x + M.b)| ≤ (A + B * (|(l : ℝ) + M.b| + 1) ^ (N + 1)) * a ^ (N + 1) := by
      refine hwx.trans ?_
      have := mul_le_mul_of_nonneg_left hpow hB
      nlinarith
    linarith

/-- region inside `[l, u]` -/
lemma region_mid (M : Model) (U l u : ℤ) (N : ℕ) (w : ℤ → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw : ∀ x ≤ U, |w x| ≤ A + B * |(x : ℝ)| ^ (N + 1))
    (hu0 : 0 ≤ u) (hlu : l ≤ u - M.b)
    (c K c₂ : ℝ) (hc : 0 ≤ c) (hK : 0 ≤ K) (hc₂ : 0 ≤ c₂)
    (x y : ℤ) (hlx : l ≤ x) (hxu : x ≤ u) (hxy : x ≤ y) (hyb : y ≤ x + M.b) (hyU : y ≤ U) :
    ENNReal.ofReal (w y) + tabooP M (fun _ => y) (Set.Icc l u)
        (fun z => ENNReal.ofReal (Wfun l u N c K c₂
          (A + B * (|(l : ℝ)| + u + M.b) ^ (N + 1) + c * (∑' j : ℕ, M.p j * ((j : ℝ) + K) ^ (N + 2))
            + c₂ * ((M.b : ℝ) + 1) ^ (N + 2)) z)) x
      ≤ ENNReal.ofReal (Wfun l u N c K c₂
          (A + B * (|(l : ℝ)| + u + M.b) ^ (N + 1) + c * (∑' j : ℕ, M.p j * ((j : ℝ) + K) ^ (N + 2))
            + c₂ * ((M.b : ℝ) + 1) ^ (N + 2)) x) := by
  unfold tabooP
  set MK : ℝ := ∑' j : ℕ, M.p j * ((j : ℝ) + K) ^ (N + 2) with hMK
  set Cι : ℝ := A + B * (|(l : ℝ)| + u + M.b) ^ (N + 1) + c * MK + c₂ * ((M.b : ℝ) + 1) ^ (N + 2)
    with hCι
  have hlu' : l ≤ u := by have := M.b_pos; omega
  refine le_trans (add_le_add (ENNReal.ofReal_le_ofReal (le_abs_self _)) le_rfl) ?_
  refine lyap_step M (Set.Icc l u) _ |w y| (abs_nonneg _) y _
    (fun j => c * ((j : ℝ) + K) ^ (N + 2) + c₂ * ((M.b : ℝ) + 1) ^ (N + 2)) ?_ ?_ ?_ ?_
  · intro j; positivity
  · have h1 : Summable (fun j : ℕ => c * (M.p j * ((j : ℝ) + K) ^ (N + 2))) :=
      (summable_p_mul_pow_add M K (N + 2)).mul_left c
    have h2 : Summable (fun j : ℕ => (c₂ * ((M.b : ℝ) + 1) ^ (N + 2)) * M.p j) :=
      M.p_sum.summable.mul_left _
    refine (h1.add h2).congr (fun j => ?_)
    ring
  · intro j
    by_cases hmem : y - j ∈ Set.Icc l u
    · rw [Set.indicator_of_notMem (by simpa using hmem)]
      positivity
    · rw [Set.indicator_of_mem (by simpa using hmem)]
      rw [Set.mem_Icc] at hmem
      have hj : (0 : ℝ) ≤ j := by positivity
      have hjz : ((y - (j : ℤ) : ℤ) : ℝ) = (y : ℝ) - j := by push_cast; ring
      rcases (show y - j < l ∨ u < y - j by omega) with hlt | hgt
      · rw [Wfun_lo _ _ _ _ _ _ _ _ hlt]
        have hlt' : ((y - (j : ℤ) : ℤ) : ℝ) < l := by exact_mod_cast hlt
        have hly : (l : ℝ) ≤ y := by
          have : l ≤ y := by omega
          exact_mod_cast this
        have h0 : 0 ≤ (l : ℝ) - ((y - (j : ℤ) : ℤ) : ℝ) + K := by linarith
        have hle : (l : ℝ) - ((y - (j : ℤ) : ℤ) : ℝ) + K ≤ (j : ℝ) + K := by rw [hjz]; linarith
        have := pow_le_pow_left₀ h0 hle (N + 2)
        have : 0 ≤ c₂ * ((M.b : ℝ) + 1) ^ (N + 2) := by positivity
        nlinarith
      · rw [Wfun_hi _ _ _ _ _ _ _ _ hgt hlu']
        have hgt' : (u : ℝ) < ((y - (j : ℤ) : ℤ) : ℝ) := by exact_mod_cast hgt
        have hyu : (y : ℝ) ≤ u + M.b := by
          have : y ≤ u + M.b := by omega
          exact_mod_cast this
        have h0 : 0 ≤ ((y - (j : ℤ) : ℤ) : ℝ) - u + 1 := by linarith
        have hle : ((y - (j : ℤ) : ℤ) : ℝ) - u + 1 ≤ (M.b : ℝ) + 1 := by rw [hjz]; linarith
        have := pow_le_pow_left₀ h0 hle (N + 2)
        have : 0 ≤ c * ((j : ℝ) + K) ^ (N + 2) := by positivity
        nlinarith
  · have hwy := hw y hyU
    have hsum : ∑' j : ℕ, M.p j * (c * ((j : ℝ) + K) ^ (N + 2) + c₂ * ((M.b : ℝ) + 1) ^ (N + 2))
        = c * MK + c₂ * ((M.b : ℝ) + 1) ^ (N + 2) := by
      have h1 : Summable (fun j : ℕ => c * (M.p j * ((j : ℝ) + K) ^ (N + 2))) :=
        (summable_p_mul_pow_add M K (N + 2)).mul_left c
      have h2 : Summable (fun j : ℕ => (c₂ * ((M.b : ℝ) + 1) ^ (N + 2)) * M.p j) :=
        M.p_sum.summable.mul_left _
      rw [tsum_congr (fun j => show M.p j * (c * ((j : ℝ) + K) ^ (N + 2) + c₂ * ((M.b : ℝ) + 1) ^ (N + 2))
          = c * (M.p j * ((j : ℝ) + K) ^ (N + 2)) + (c₂ * ((M.b : ℝ) + 1) ^ (N + 2)) * M.p j by ring)]
      rw [Summable.tsum_add h1 h2, tsum_mul_left, tsum_mul_left, M.p_sum.tsum_eq, mul_one]
    rw [hsum, Wfun_mid _ _ _ _ _ _ _ _ hlx hxu]
    have habs : |(y : ℝ)| ≤ |(l : ℝ)| + u + M.b := by
      have hly : (l : ℝ) ≤ y := by
        have : l ≤ y := by omega
        exact_mod_cast this
      have hyu : (y : ℝ) ≤ u + M.b := by
        have : y ≤ u + M.b := by omega
        exact_mod_cast this
      have hu : (0 : ℝ) ≤ u := by exact_mod_cast hu0
      have hb : (0 : ℝ) ≤ M.b := by positivity
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (l : ℝ)]
      · linarith [le_abs_self (l : ℝ), abs_nonneg (l : ℝ)]
    have hpow : |(y : ℝ)| ^ (N + 1) ≤ (|(l : ℝ)| + u + M.b) ^ (N + 1) :=
      pow_le_pow_left₀ (abs_nonneg _) habs _
    have := mul_le_mul_of_nonneg_left hpow hB
    rw [hCι]
    linarith

/-- region above `u` -/
lemma region_above (M : Model) (U l u : ℤ) (N : ℕ) (w : ℤ → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw : ∀ x ≤ U, |w x| ≤ A + B * |(x : ℝ)| ^ (N + 1))
    (hu0 : 0 ≤ u) (hlu : l ≤ u - M.b)
    (c K c₂ Cι : ℝ) (hc : 0 ≤ c) (hK : 0 ≤ K) (hc₂ : 0 ≤ c₂)
    (hc₂' : A + B * ((u : ℝ) + 1) ^ (N + 1) + c * (∑' j : ℕ, M.p j * ((j : ℝ) + K) ^ (N + 2))
      ≤ c₂ * (1 - M.p 0))
    (x : ℤ) (hux : u < x) (hxU : x ≤ U) :
    ENNReal.ofReal (w x) + tabooP M (fun _ => x) (Set.Icc l u)
        (fun z => ENNReal.ofReal (Wfun l u N c K c₂ Cι z)) x
      ≤ ENNReal.ofReal (Wfun l u N c K c₂ Cι x) := by
  unfold tabooP
  set MK : ℝ := ∑' j : ℕ, M.p j * ((j : ℝ) + K) ^ (N + 2) with hMK
  set a : ℝ := (x : ℝ) - u + 1 with ha
  have hlu' : l ≤ u := by have := M.b_pos; omega
  have hux' : (u : ℝ) < x := by exact_mod_cast hux
  have he1 : 1 ≤ (x : ℝ) - u := by
    have : u + 1 ≤ x := hux
    have : ((u : ℝ) + 1) ≤ x := by exact_mod_cast this
    linarith
  have ha1 : 1 ≤ a := by rw [ha]; linarith
  have ha0 : 0 ≤ a := by linarith
  have haN : a ^ (N + 1) ≤ a ^ (N + 2) := pow_le_pow_right₀ ha1 (by omega)
  have haN1 : 1 ≤ a ^ (N + 1) := one_le_pow₀ ha1
  have hp0 : 0 ≤ M.p 0 := M.p_nonneg 0
  refine le_trans (add_le_add (ENNReal.ofReal_le_ofReal (le_abs_self _)) le_rfl) ?_
  refine lyap_step M (Set.Icc l u) _ |w x| (abs_nonneg _) x _
    (fun j => c₂ * (a ^ (N + 2) - a ^ (N + 1)) + (if j = 0 then c₂ * a ^ (N + 1) else 0)
      + c * ((j : ℝ) + K) ^ (N + 2)) ?_ ?_ ?_ ?_
  · intro j
    have : 0 ≤ (if j = 0 then c₂ * a ^ (N + 1) else 0) := by split_ifs <;> positivity
    have : 0 ≤ c₂ * (a ^ (N + 2) - a ^ (N + 1)) := mul_nonneg hc₂ (by linarith)
    have : 0 ≤ c * ((j : ℝ) + K) ^ (N + 2) := by positivity
    linarith
  · have h1 : Summable (fun j : ℕ => (c₂ * (a ^ (N + 2) - a ^ (N + 1))) * M.p j) :=
      M.p_sum.summable.mul_left _
    have h2 : Summable (fun j : ℕ => if j = 0 then M.p 0 * (c₂ * a ^ (N + 1)) else 0) :=
      (hasSum_ite_eq 0 (M.p 0 * (c₂ * a ^ (N + 1)))).summable
    have h3 : Summable (fun j : ℕ => c * (M.p j * ((j : ℝ) + K) ^ (N + 2))) :=
      (summable_p_mul_pow_add M K (N + 2)).mul_left c
    refine ((h1.add h2).add h3).congr (fun j => ?_)
    by_cases hj : j = 0
    · subst hj; simp only [if_true]; ring
    · simp only [hj, if_false]; ring
  · intro j
    have hj : (0 : ℝ) ≤ j := by positivity
    have hjz : ((x - (j : ℤ) : ℤ) : ℝ) = (x : ℝ) - j := by push_cast; ring
    have hite : 0 ≤ (if j = 0 then c₂ * a ^ (N + 1) else 0) := by split_ifs <;> positivity
    have hc₂a : 0 ≤ c₂ * (a ^ (N + 2) - a ^ (N + 1)) := mul_nonneg hc₂ (by linarith)
    have hcK : 0 ≤ c * ((j : ℝ) + K) ^ (N + 2) := by positivity
    by_cases hmem : x - j ∈ Set.Icc l u
    · rw [Set.indicator_of_notMem (by simpa using hmem)]
      linarith
    · rw [Set.indicator_of_mem (by simpa using hmem)]
      rw [Set.mem_Icc] at hmem
      rcases (show x - j < l ∨ u < x - j by omega) with hlt | hgt
      · rw [Wfun_lo _ _ _ _ _ _ _ _ hlt]
        have hlt' : ((x - (j : ℤ) : ℤ) : ℝ) < l := by exact_mod_cast hlt
        have hlx : (l : ℝ) ≤ x := by
          have : l ≤ x := by omega
          exact_mod_cast this
        have h0 : 0 ≤ (l : ℝ) - ((x - (j : ℤ) : ℤ) : ℝ) + K := by linarith
        have hle : (l : ℝ) - ((x - (j : ℤ) : ℤ) : ℝ) + K ≤ (j : ℝ) + K := by rw [hjz]; linarith
        have := pow_le_pow_left₀ h0 hle (N + 2)
        nlinarith
      · rw [Wfun_hi _ _ _ _ _ _ _ _ hgt hlu']
        have hgt' : (u : ℝ) < ((x - (j : ℤ) : ℤ) : ℝ) := by exact_mod_cast hgt
        have hja : (j : ℝ) ≤ a := by rw [ha]; linarith
        have heq : ((x - (j : ℤ) : ℤ) : ℝ) - u + 1 = a - j := by rw [hjz, ha]; ring
        rw [heq]
        by_cases hj0 : j = 0
        · subst hj0
          simp only [if_true, Nat.cast_zero, sub_zero, zero_add] at hcK hite hc₂a ⊢
          linarith
        · simp only [hj0, if_false, add_zero]
          have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj0
          have := pow_sub_le (N + 1) a (j : ℝ) hj hja
          have : (a - j) ^ (N + 2) ≤ a ^ (N + 2) - a ^ (N + 1) := by
            have : a ^ (N + 1) ≤ (j : ℝ) * a ^ (N + 1) := by nlinarith [pow_nonneg ha0 (N + 1)]
            linarith
          nlinarith
  · have hwx := hw x hxU
    have hsum : ∑' j : ℕ, M.p j * (c₂ * (a ^ (N + 2) - a ^ (N + 1))
          + (if j = 0 then c₂ * a ^ (N + 1) else 0) + c * ((j : ℝ) + K) ^ (N + 2))
        = c₂ * (a ^ (N + 2) - a ^ (N + 1)) + M.p 0 * (c₂ * a ^ (N + 1)) + c * MK := by
      have h1 : Summable (fun j : ℕ => (c₂ * (a ^ (N + 2) - a ^ (N + 1))) * M.p j) :=
        M.p_sum.summable.mul_left _
      have h2 : HasSum (fun j : ℕ => if j = 0 then M.p 0 * (c₂ * a ^ (N + 1)) else 0)
          (M.p 0 * (c₂ * a ^ (N + 1))) := hasSum_ite_eq 0 _
      have h3 : Summable (fun j : ℕ => c * (M.p j * ((j : ℝ) + K) ^ (N + 2))) :=
        (summable_p_mul_pow_add M K (N + 2)).mul_left c
      have hre : (fun j : ℕ => M.p j * (c₂ * (a ^ (N + 2) - a ^ (N + 1))
            + (if j = 0 then c₂ * a ^ (N + 1) else 0) + c * ((j : ℝ) + K) ^ (N + 2)))
          = fun j : ℕ => ((c₂ * (a ^ (N + 2) - a ^ (N + 1))) * M.p j
            + (if j = 0 then M.p 0 * (c₂ * a ^ (N + 1)) else 0))
            + c * (M.p j * ((j : ℝ) + K) ^ (N + 2)) := by
        funext j
        by_cases hj : j = 0
        · subst hj; simp only [if_true]; ring
        · simp only [hj, if_false]; ring
      rw [hre, Summable.tsum_add (h1.add h2.summable) h3, Summable.tsum_add h1 h2.summable,
        tsum_mul_left, tsum_mul_left, M.p_sum.tsum_eq, h2.tsum_eq]
      ring
    rw [hsum, Wfun_hi _ _ _ _ _ _ _ _ hux hlu']
    -- |x| ≤ (u + 1) * a
    have hu : (0 : ℝ) ≤ u := by exact_mod_cast hu0
    have habs : |(x : ℝ)| ≤ ((u : ℝ) + 1) * a := by
      rw [abs_of_pos (by linarith), ha]
      nlinarith
    have hpow : |(x : ℝ)| ^ (N + 1) ≤ ((u : ℝ) + 1) ^ (N + 1) * a ^ (N + 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) habs _
    have hwx' : |w x| ≤ (A + B * ((u : ℝ) + 1) ^ (N + 1)) * a ^ (N + 1) := by
      refine hwx.trans ?_
      have := mul_le_mul_of_nonneg_left hpow hB
      nlinarith
    have hMK0 : 0 ≤ MK := tsum_nonneg (fun j => mul_nonneg (M.p_nonneg j) (pow_nonneg (add_nonneg (Nat.cast_nonneg j) hK) _))
    have key : (A + B * ((u : ℝ) + 1) ^ (N + 1) + c * MK) * a ^ (N + 1) ≤ c₂ * (1 - M.p 0) * a ^ (N + 1) :=
      mul_le_mul_of_nonneg_right hc₂' (by positivity)
    have : c * MK ≤ c * MK * a ^ (N + 1) := by nlinarith [mul_nonneg hc hMK0]
    nlinarith

/-- The core growth lemma: `H_ι` of a function of polynomial growth `|x|^{N+1}` has growth
`|x|^{N+2}` on `x ≤ U`. -/
theorem H_growth_core (M : Model) (U : ℤ) (N : ℕ) (w : ℤ → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw : ∀ x ≤ U, |w x| ≤ A + B * |(x : ℝ)| ^ (N + 1))
    (l u : ℤ) (hu0 : 0 ≤ u) (huU : u ≤ U) (hlu : l ≤ u - M.b) :
    ∃ A' B' : ℝ, 0 ≤ A' ∧ 0 ≤ B' ∧ ∀ x ≤ U,
      H M U l u (fun z => ENNReal.ofReal (w z)) x ≤ ENNReal.ofReal (A' + B' * |(x : ℝ)| ^ (N + 2)) := by
  have hκ := kappa_pos M
  set κ : ℝ := (M.b : ℝ) - ∑' j : ℕ, (j : ℝ) * M.p j with hκdef
  clear_value κ
  have hb0 : (0 : ℝ) ≤ M.b := by positivity
  obtain ⟨Mm, hMm⟩ : ∃ Mm : ℝ, Mm = ∑' j : ℕ, M.p j * ((j : ℝ) + (1 + M.b)) ^ (N + 2) := ⟨_, rfl⟩
  have hMm0 : 0 ≤ Mm := by
    rw [hMm]
    exact tsum_nonneg (fun j => mul_nonneg (M.p_nonneg j) (pow_nonneg (add_nonneg (Nat.cast_nonneg j) (by positivity)) _))
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = (N + 1) * 2 ^ (N + 2) := ⟨_, rfl⟩
  have hCm0 : 0 ≤ Cm := by rw [hCm]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (M.b : ℝ) + 1 + 2 * Cm * Mm / ((N + 2) * κ) := ⟨_, rfl⟩
  have hNκ : 0 < ((N : ℝ) + 2) * κ := by positivity
  have hKq : 0 ≤ 2 * Cm * Mm / ((N + 2) * κ) := by positivity
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  have hKb : (M.b : ℝ) ≤ K := by rw [hK]; linarith
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = A + B * (|(l : ℝ) + M.b| + 1) ^ (N + 1) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * X / ((N + 2) * κ) + 1 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  obtain ⟨MK, hMK⟩ : ∃ MK : ℝ, MK = ∑' j : ℕ, M.p j * ((j : ℝ) + K) ^ (N + 2) := ⟨_, rfl⟩
  have hMK0 : 0 ≤ MK := by
    rw [hMK]
    exact tsum_nonneg (fun j => mul_nonneg (M.p_nonneg j) (pow_nonneg (add_nonneg (Nat.cast_nonneg j) hK0) _))
  have hp0 := p0_lt_one M
  have hp0' : 0 < 1 - M.p 0 := by linarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = A + B * ((u : ℝ) + 1) ^ (N + 1) + c * MK := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℝ, c₂ = Y / (1 - M.p 0) + 1 := ⟨_, rfl⟩
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; positivity
  have hc₂' : Y ≤ c₂ * (1 - M.p 0) := by
    rw [hc₂, add_mul, div_mul_cancel₀ _ hp0'.ne']
    linarith
  obtain ⟨Cι, hCι⟩ : ∃ Cι : ℝ, Cι = A + B * (|(l : ℝ)| + u + M.b) ^ (N + 1) + c * MK
    + c₂ * ((M.b : ℝ) + 1) ^ (N + 2) := ⟨_, rfl⟩
  have hCι0 : 0 ≤ Cι := by rw [hCι]; positivity
  have hlu' : l ≤ u := by have := M.b_pos; omega
  -- the drift inequality below
  have hdrift : ∀ a : ℝ, K ≤ a →
      c * ∑' j : ℕ, M.p j * (a + ((j : ℝ) - M.b)) ^ (N + 2)
        + (A + B * (|(l : ℝ) + M.b| + 1) ^ (N + 1)) * a ^ (N + 1) ≤ c * a ^ (N + 2) := by
    intro a haK
    rw [← hX]
    have ha1 : 1 ≤ a := le_trans hK1 haK
    have ha0 : 0 ≤ a := by linarith
    have hd := drift_below M N a ha1
    rw [← hMm, show (∑' j : ℕ, (j : ℝ) * M.p j) - M.b = -κ by rw [hκdef]; ring] at hd
    have hA2 : 2 * Cm * Mm ≤ a * (((N : ℝ) + 2) * κ) := by
      have : 2 * Cm * Mm / (((N : ℝ) + 2) * κ) ≤ a := by rw [hK] at haK; linarith
      rwa [div_le_iff₀ hNκ] at this
    have hA1 : 2 * X ≤ c * (((N : ℝ) + 2) * κ) := by
      rw [hc, add_mul, div_mul_cancel₀ _ hNκ.ne']
      linarith
    have haN : 0 ≤ a ^ N := pow_nonneg ha0 N
    have haN1 : 0 ≤ a ^ (N + 1) := pow_nonneg ha0 _
    have h1 : c * (((N : ℝ) + 1) * 2 ^ (N + 2) * a ^ N * Mm)
        ≤ c * (((N : ℝ) + 2) * κ * a ^ (N + 1)) / 2 := by
      have h := mul_le_mul_of_nonneg_left hA2 (mul_nonneg hc0 haN)
      calc c * (((N : ℝ) + 1) * 2 ^ (N + 2) * a ^ N * Mm)
          = (c * a ^ N * (2 * Cm * Mm)) / 2 := by rw [hCm]; ring
        _ ≤ (c * a ^ N * (a * (((N : ℝ) + 2) * κ))) / 2 := by gcongr
        _ = c * (((N : ℝ) + 2) * κ * a ^ (N + 1)) / 2 := by ring
    have h2 : X * a ^ (N + 1) ≤ c * (((N : ℝ) + 2) * κ * a ^ (N + 1)) / 2 := by
      have h := mul_le_mul_of_nonneg_right hA1 haN1
      calc X * a ^ (N + 1) = (2 * X * a ^ (N + 1)) / 2 := by ring
        _ ≤ (c * (((N : ℝ) + 2) * κ) * a ^ (N + 1)) / 2 := by gcongr
        _ = _ := by ring
    have h3 := mul_le_mul_of_nonneg_left hd hc0
    linarith
  -- the Lyapunov inequality for every policy in Δ_ι
  have hW : ∀ δ, DeltaIota M U l u δ → ∀ x ≤ U,
      (fun z => ENNReal.ofReal (w z)) (δ x)
        + tabooP M δ (Set.Icc l u) (fun z => ENNReal.ofReal (Wfun l u N c K c₂ Cι z)) x
        ≤ ENNReal.ofReal (Wfun l u N c K c₂ Cι x) := by
    intro δ hδ x hx
    obtain ⟨hfeas, hlo, hhi⟩ := hδ
    have htab : ∀ y, δ x = y →
        tabooP M δ (Set.Icc l u) (fun z => ENNReal.ofReal (Wfun l u N c K c₂ Cι z)) x
          = tabooP M (fun _ => y) (Set.Icc l u) (fun z => ENNReal.ofReal (Wfun l u N c K c₂ Cι z)) x := by
      intro y hy; unfold tabooP; rw [hy]
    rcases lt_or_ge x l with hxl | hxl
    · have hy := hlo x hxl.le
      rw [htab _ hy]
      simp only [hy]
      exact region_below M U l u N w A B hA hB hw hlu huU c K c₂ Cι hc0 hK1 hKb hdrift x hxl
    rcases le_or_gt x u with hxu | hxu
    · obtain ⟨h1, h2, h3⟩ := hfeas x hx
      rw [htab _ rfl, hCι, hMK]
      exact region_mid M U l u N w A B hA hB hw hu0 hlu c K c₂ hc0 hK0 hc₂0 x (δ x) hxl hxu h1 h2 h3
    · have hy := hhi x hxu.le hx
      rw [htab _ hy]
      simp only [hy]
      rw [hY, hMK] at hc₂'
      exact region_above M U l u N w A B hA hB hw hu0 hlu c K c₂ Cι hc0 hK0 hc₂0 hc₂' x hxu hx
  refine ⟨c * 2 ^ (N + 2) * (|(l : ℝ)| + K) ^ (N + 2) + Cι + c₂ * 2 ^ (N + 2) * (|(u : ℝ)| + 1) ^ (N + 2),
    c * 2 ^ (N + 2) + c₂ * 2 ^ (N + 2), by positivity, by positivity, ?_⟩
  intro x hx
  refine (H_le M U l u _ _ hW x hx).trans ?_
  exact ENNReal.ofReal_le_ofReal (Wfun_growth l u N c K c₂ Cι hc0 hK0 hc₂0 hCι0 hlu' x)


lemma pow_le_one_add_pow (m n : ℕ) (h : m ≤ n) (x : ℝ) : |x| ^ m ≤ 1 + |x| ^ n := by
  rcases le_or_gt 1 |x| with h1 | h1
  · have := pow_le_pow_right₀ h1 h
    linarith
  · have := pow_le_one₀ (abs_nonneg x) h1.le (n := m)
    have := pow_nonneg (abs_nonneg x) n
    linarith

theorem lemma3_core (M : Model) (U : ℤ) (q : ℕ) (hq : 0 < q) (v : ℤ → ℝ)
    (hv : ∃ A B : ℝ, ∀ x ≤ U, |v x| ≤ A + B * |(x : ℝ)| ^ q)
    (l u : ℤ) (hu0 : 0 ≤ u) (huU : u ≤ U) (hlu : l ≤ u - M.b) :
    ∃ A' B' : ℝ, ∀ x ≤ U,
      H M U l u (fun z => ENNReal.ofReal |v z|) x ≤ ENNReal.ofReal (A' + B' * |(x : ℝ)| ^ (q + 3)) := by
  obtain ⟨A, B, hAB⟩ := hv
  obtain ⟨N, rfl⟩ : ∃ N, q = N + 1 := ⟨q - 1, by omega⟩
  have hw : ∀ x ≤ U, |(fun z => |v z|) x| ≤ |A| + |B| * |(x : ℝ)| ^ (N + 1) := by
    intro x hx
    simp only [abs_abs]
    refine (hAB x hx).trans ?_
    have := mul_le_mul_of_nonneg_right (le_abs_self B) (pow_nonneg (abs_nonneg (x : ℝ)) (N + 1))
    linarith [le_abs_self A]
  obtain ⟨A', B', hA', hB', h⟩ := H_growth_core M U N (fun z => |v z|) |A| |B| (abs_nonneg _)
    (abs_nonneg _) hw l u hu0 huU hlu
  refine ⟨A' + B', B', fun x hx => ?_⟩
  refine (h x hx).trans (ENNReal.ofReal_le_ofReal ?_)
  have := pow_le_one_add_pow (N + 2) (N + 1 + 3) (by omega) (x : ℝ)
  have := mul_le_mul_of_nonneg_left this hB'
  linarith

theorem corollary1_core (M : Model) (U l u : ℤ) (hu0 : 0 ≤ u) (huU : u ≤ U)
    (hlu : l ≤ u - M.b) :
    (∃ A B : ℝ, ∀ x ≤ U,
      H M U l u (fun _ => (1 : ℝ≥0∞)) x ≤ ENNReal.ofReal (A + B * |(x : ℝ)| ^ 3)) ∧
    (∃ A B : ℝ, ∀ x ≤ U,
      H M U l u (fun y => ENNReal.ofReal (M.G y)) x ≤
        ENNReal.ofReal (A + B * |(x : ℝ)| ^ (M.ρ + 3))) ∧
    ∀ x ≤ U, H M U l u (fun _ => (1 : ℝ≥0∞)) x ≠ ⊤ ∧
      H M U l u (fun y => ENNReal.ofReal (M.G y)) x ≠ ⊤ := by
  have h1 : ∃ A B : ℝ, ∀ x ≤ U,
      H M U l u (fun _ => (1 : ℝ≥0∞)) x ≤ ENNReal.ofReal (A + B * |(x : ℝ)| ^ 3) := by
    have hw : ∀ x ≤ U, |(fun _ : ℤ => (1 : ℝ)) x| ≤ 1 + 0 * |(x : ℝ)| ^ (0 + 1) := by
      intro x _; simp
    obtain ⟨A', B', hA', hB', h⟩ := H_growth_core M U 0 (fun _ => (1 : ℝ)) 1 0 zero_le_one le_rfl
      hw l u hu0 huU hlu
    refine ⟨A' + B', B', fun x hx => ?_⟩
    have e : (fun _ : ℤ => (1 : ℝ≥0∞)) = fun z => ENNReal.ofReal ((fun _ : ℤ => (1 : ℝ)) z) := by
      funext z; simp
    rw [e]
    refine (h x hx).trans (ENNReal.ofReal_le_ofReal ?_)
    have := pow_le_one_add_pow (0 + 2) 3 (by omega) (x : ℝ)
    have := mul_le_mul_of_nonneg_left this hB'
    linarith
  have h2 : ∃ A B : ℝ, ∀ x ≤ U,
      H M U l u (fun y => ENNReal.ofReal (M.G y)) x ≤
        ENNReal.ofReal (A + B * |(x : ℝ)| ^ (M.ρ + 3)) := by
    obtain ⟨A, B, hA, hB, hG⟩ := M.G_growth
    obtain ⟨N, hN⟩ : ∃ N, M.ρ = N + 1 := ⟨M.ρ - 1, by have := M.ρ_pos; omega⟩
    have hw : ∀ x ≤ U, |M.G x| ≤ A + B * |(x : ℝ)| ^ (N + 1) := by
      intro x _
      rw [abs_of_nonneg (M.G_nonneg x), ← hN]
      exact hG x
    obtain ⟨A', B', hA', hB', h⟩ := H_growth_core M U N M.G A B hA.le hB.le hw l u hu0 huU hlu
    refine ⟨A' + B', B', fun x hx => ?_⟩
    rw [hN]
    refine (h x hx).trans (ENNReal.ofReal_le_ofReal ?_)
    have := pow_le_one_add_pow (N + 2) (N + 1 + 3) (by omega) (x : ℝ)
    have := mul_le_mul_of_nonneg_left this hB'
    linarith
  refine ⟨h1, h2, fun x hx => ⟨?_, ?_⟩⟩
  · obtain ⟨A, B, h⟩ := h1
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h x hx)
  · obtain ⟨A, B, h⟩ := h2
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h x hx)

end FedergruenZipkin.AvgCost

open FedergruenZipkin.AvgCost
open scoped ENNReal

theorem solution (M : Model) (U l u : ℤ) (hu0 : 0 ≤ u) (huU : u ≤ U)
    (hlu : l ≤ u - M.b) :
    (∃ A B : ℝ, ∀ x ≤ U,
      H M U l u (fun _ => (1 : ℝ≥0∞)) x ≤ ENNReal.ofReal (A + B * |(x : ℝ)| ^ 3)) ∧
    (∃ A B : ℝ, ∀ x ≤ U,
      H M U l u (fun y => ENNReal.ofReal (M.G y)) x ≤
        ENNReal.ofReal (A + B * |(x : ℝ)| ^ (M.ρ + 3))) ∧
    ∀ x ≤ U, H M U l u (fun _ => (1 : ℝ≥0∞)) x ≠ ⊤ ∧
      H M U l u (fun y => ENNReal.ofReal (M.G y)) x ≠ ⊤ := by
  exact corollary1_core M U l u hu0 huU hlu
