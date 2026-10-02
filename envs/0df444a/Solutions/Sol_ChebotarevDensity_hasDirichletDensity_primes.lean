-- Prove2me | solution 1 for ChebotarevDensity.hasDirichletDensity_primes
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T13:36:12.462497+00:00
-- url     : https://prove2.me/submissions/a22aad65-2e8a-4e1f-bcd5-088e4e194bec

import Definitions.Def_ChebotarevDensity_Defs

open Polynomial NumberField
open ChebotarevDensity

private lemma neglog_bounds {x : ℝ} (_h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    x ≤ -Real.log (1 - x) ∧ -Real.log (1 - x) ≤ x + 2 * x ^ 2 := by
  have hpos : 0 < 1 - x := by linarith
  constructor
  · have := Real.log_le_sub_one_of_pos hpos
    linarith
  · have h := Real.one_sub_inv_le_log_of_pos hpos
    have h2 : (1 - x)⁻¹ ≤ 1 + x + 2 * x ^ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ hpos]
      nlinarith [sq_nonneg x]
    linarith

private lemma x_le_inv {s : ℝ} (hs : 1 ≤ s) (p : Nat.Primes) :
    (p : ℝ) ^ (-s) ≤ (p : ℝ)⁻¹ := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_lt.le
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hp (by linarith)

private lemma inv_le_half (p : Nat.Primes) : (p : ℝ)⁻¹ ≤ 1 / 2 := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
  rw [one_div]
  exact inv_anti₀ (by norm_num) hp

private lemma summable_sq : Summable (fun p : Nat.Primes => ((p : ℝ)⁻¹) ^ 2) := by
  have := (Nat.Primes.summable_rpow (r := -2)).mpr (by norm_num)
  refine this.congr (fun p => ?_)
  rw [Real.rpow_neg (by positivity), Real.rpow_two, inv_pow]

private noncomputable def Tf (s : ℝ) : ℝ := ∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-s))
private noncomputable def Pf (s : ℝ) : ℝ := ∑' p : Nat.Primes, (p : ℝ) ^ (-s)

private lemma summable_P {s : ℝ} (hs : 1 < s) : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-s)) :=
  Nat.Primes.summable_rpow.mpr (by linarith)

private lemma summable_T {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes => -Real.log (1 - (p : ℝ) ^ (-s))) := by
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) ((summable_P hs).mul_left 2)
  · have := (neglog_bounds (Real.rpow_nonneg (Nat.cast_nonneg _) (-s))
      ((x_le_inv hs.le p).trans (inv_le_half p))).1
    exact (Real.rpow_nonneg (Nat.cast_nonneg _) (-s)).trans this
  · have h := neglog_bounds (Real.rpow_nonneg (Nat.cast_nonneg _) (-s))
      ((x_le_inv hs.le p).trans (inv_le_half p))
    have h0 := Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) p) (-s)
    have h1 := (x_le_inv hs.le p).trans (inv_le_half p)
    nlinarith [h.2]

private noncomputable def Cf : ℝ := ∑' p : Nat.Primes, ((p : ℝ)⁻¹) ^ 2

private lemma P_le_T {s : ℝ} (hs : 1 < s) : Pf s ≤ Tf s := by
  refine Summable.tsum_le_tsum (fun p => ?_) (summable_P hs) (summable_T hs)
  exact (neglog_bounds (Real.rpow_nonneg (Nat.cast_nonneg _) (-s))
      ((x_le_inv hs.le p).trans (inv_le_half p))).1

private lemma T_le_P {s : ℝ} (hs : 1 < s) : Tf s ≤ Pf s + 2 * Cf := by
  have hsum : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-s) + 2 * ((p : ℝ)⁻¹) ^ 2) :=
    (summable_P hs).add (summable_sq.mul_left 2)
  calc Tf s ≤ ∑' p : Nat.Primes, ((p : ℝ) ^ (-s) + 2 * ((p : ℝ)⁻¹) ^ 2) := by
        refine Summable.tsum_le_tsum (fun p => ?_) (summable_T hs) hsum
        have h := (neglog_bounds (Real.rpow_nonneg (Nat.cast_nonneg _) (-s))
          ((x_le_inv hs.le p).trans (inv_le_half p))).2
        have h0 := Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) p) (-s)
        have h1 := x_le_inv hs.le p
        have : ((p : ℝ) ^ (-s)) ^ 2 ≤ ((p : ℝ)⁻¹) ^ 2 := pow_le_pow_left₀ h0 h1 2
        linarith
    _ = Pf s + 2 * Cf := by
        rw [Summable.tsum_add (summable_P hs) (summable_sq.mul_left 2), tsum_mul_left]
        rfl

private lemma zeta_eq_exp {s : ℝ} (hs : 1 < s) :
    riemannZeta (s : ℂ) = ((Real.exp (Tf s) : ℝ) : ℂ) := by
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  rw [← riemannZeta_eulerProduct_exp_log hs']
  have : ∀ p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) =
      ((-Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ) := by
    intro p
    have hx := Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) p) (-s)
    have h1 := (x_le_inv hs.le p).trans (inv_le_half p)
    rw [Complex.ofReal_neg, Complex.ofReal_log (by linarith), Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg]
    simp
  simp_rw [this]
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_exp]
  rfl

private lemma tendsto_T_sub :
    Filter.Tendsto (fun s : ℝ => Tf s - Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have hres := riemannZeta_residue_one
  have hc : Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
      (nhdsWithin (1 : ℂ) {1}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := (Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have := congrArg Complex.re h
      simp at this
      exact absurd this (ne_of_gt hs)
  have h1 := (Complex.continuous_re.tendsto 1).comp (hres.comp hc)
  have h2 : Filter.Tendsto (fun s : ℝ => (s - 1) * Real.exp (Tf s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
    refine Filter.Tendsto.congr' ?_ h1
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Function.comp]
    rw [zeta_eq_exp hs]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h3 := h2.log (by norm_num)
  rw [Real.log_one] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 0 < s - 1 := sub_pos.mpr hs
  rw [Real.log_mul hs'.ne' (Real.exp_pos _).ne', Real.log_exp, one_div, Real.log_inv]
  ring

private lemma tendsto_L :
    Filter.Tendsto (fun s : ℝ => Real.log (1 / (s - 1))) (nhdsWithin 1 (Set.Ioi 1))
      Filter.atTop := by
  refine Real.tendsto_log_atTop.comp ?_
  have h : Filter.Tendsto (fun s : ℝ => s - 1) (nhdsWithin 1 (Set.Ioi 1)) (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Filter.Tendsto (fun s : ℝ => s - 1) (nhds 1) (nhds (1 - 1)) :=
        (continuous_id.sub continuous_const).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using hs
  simpa [one_div, Function.comp_def] using tendsto_inv_nhdsGT_zero.comp h

private lemma tendsto_shift (c : ℝ) :
    Filter.Tendsto (fun s : ℝ => (Tf s - c) / Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have h : Filter.Tendsto (fun s : ℝ => (Tf s - Real.log (1 / (s - 1)) - c) /
      Real.log (1 / (s - 1))) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    have h0 : Filter.Tendsto (fun s : ℝ => Tf s - Real.log (1 / (s - 1)) - c)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (-c)) := by
      simpa using tendsto_T_sub.sub_const c
    exact Filter.Tendsto.div_atTop h0 tendsto_L
  have h2 := h.const_add 1
  rw [add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [tendsto_L.eventually_gt_atTop 0] with s hs
  field_simp
  ring

theorem solution : HasDirichletDensity {p : ℕ | p.Prime} 1 := by
  have hE : ∀ s : ℝ, ∑' p : {p : ℕ // p.Prime ∧ p ∈ {p : ℕ | p.Prime}}, ((p : ℕ) : ℝ) ^ (-s)
      = Pf s := by
    intro s
    exact (Equiv.subtypeEquivRight (fun p => by simp) :
      {p : ℕ // p.Prime ∧ p ∈ {p : ℕ | p.Prime}} ≃ Nat.Primes).tsum_eq
        (fun p : Nat.Primes => (p : ℝ) ^ (-s))
  unfold HasDirichletDensity
  simp_rw [hE]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_shift (2 * Cf)) (tendsto_shift 0)
    ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, tendsto_L.eventually_gt_atTop 0] with s hs hL
    have := T_le_P (show 1 < s from hs)
    exact div_le_div_of_nonneg_right (by linarith) hL.le
  · filter_upwards [self_mem_nhdsWithin, tendsto_L.eventually_gt_atTop 0] with s hs hL
    have := P_le_T (show 1 < s from hs)
    exact div_le_div_of_nonneg_right (by linarith) hL.le
