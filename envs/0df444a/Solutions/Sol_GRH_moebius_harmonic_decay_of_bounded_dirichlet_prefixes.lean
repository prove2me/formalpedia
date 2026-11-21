-- Prove2me | solution 1 for GRH.moebius_harmonic_decay_of_bounded_dirichlet_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:39:35.67006+00:00
-- url     : https://prove2.me/submissions/1edf8363-8864-4851-a9d2-fdf1bb5ea929

import Mathlib

open Finset Filter Topology ArithmeticFunction


private theorem abel_interval (f g : ℕ → ℝ) (C : ℝ) (hG : ∀ n, |∑ i ∈ range n, g i| ≤ C)
    (m n : ℕ) (hmn : m < n) (hf : ∀ i, m ≤ i → 0 ≤ f i)
    (hmono : ∀ i, m ≤ i → f (i+1) ≤ f i) :
    |∑ i ∈ Ico m n, f i * g i| ≤ 2*C*f m := by
  let G (i : ℕ) := ∑ k ∈ range i, g k
  have he := sum_Ico_by_parts f g hmn
  simp only [smul_eq_mul] at he
  change _ = f (n-1)*G n - f m*G m -
    ∑ i ∈ Ico m (n-1), (f (i+1)-f i)*G (i+1) at he
  have hmn' : m ≤ n-1 := by omega
  have hdiff :
      |∑ i ∈ Ico m (n-1), (f (i+1)-f i)*G (i+1)| ≤ (f m - f (n-1))*C := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ i ∈ Ico m (n-1), (f i-f (i+1))*C := by
            apply sum_le_sum
            intro i hi
            have hm := hmono i (mem_Ico.mp hi).1
            rw [abs_mul,abs_of_nonpos (sub_nonpos.mpr hm),neg_sub]
            exact mul_le_mul_of_nonneg_left (hG _) (sub_nonneg.mpr hm)
         _ = _ := by
            rw [←sum_mul,←neg_sub (f (n-1)) (f m),←sum_Ico_sub f hmn',←sum_neg_distrib]
            simp only [neg_sub]
  rw [he]
  apply (abs_sub _ _).trans
  have endpoint (j l : ℕ) (hj : m ≤ j) : |f j * G l| ≤ f j * C := by
    rw [abs_mul, abs_of_nonneg (hf j hj)]
    exact mul_le_mul_of_nonneg_left (hG l) (hf j hj)
  apply (add_le_add ((abs_sub _ _).trans (add_le_add (endpoint _ _ hmn')
    (endpoint _ _ le_rfl))) hdiff).trans_eq
  ring

private theorem mu_series_real (s : ℝ) (hs : 1 < s) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, (moebius n : ℝ) * (n : ℝ)^(-s))
      atTop (𝓝 ((riemannZeta (s:ℂ))⁻¹).re) := by
  have hs' : 1 < (s:ℂ).re := hs
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs'
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs'] at h
  have hb := (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs').LSeriesHasSum
  rw [eq_inv_of_mul_eq_one_right h] at hb
  have hr := (Complex.hasSum_re hb).tendsto_sum_nat
  apply hr.congr
  intro n
  apply sum_congr rfl
  intro j _
  by_cases hj : j = 0
  · simp [hj]
  rw [LSeries.term_of_ne_zero hj]
  rw [←Complex.ofReal_natCast,←Complex.ofReal_cpow (Nat.cast_nonneg j)]
  norm_cast
  rw [Real.rpow_neg (Nat.cast_nonneg j),div_eq_mul_inv]

private theorem zeta_inv_real_boundary :
    Tendsto (fun s : ℝ => ((riemannZeta (s:ℂ))⁻¹).re) (𝓝[>] 1) (𝓝 0) := by
  have h := ((tendsto_id.sub_const (1 : ℂ)).mono_left nhdsWithin_le_nhds).div
    riemannZeta_residue_one (by norm_num)
  norm_num at h
  have hz : Tendsto (fun z : ℂ => (riemannZeta z)⁻¹) (𝓝[≠] 1) (𝓝 0) := by
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hn : z-1 ≠ 0 := sub_ne_zero.mpr hz
    simp [div_eq_mul_inv,hn,mul_comm,mul_left_comm]
  have hc : Tendsto (fun s : ℝ => (s:ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa using Complex.continuous_ofReal.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (1:ℝ) ≤ 𝓝 1)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa [Set.mem_compl_iff] using ne_of_gt (show 1 < s from hs)
  exact (Complex.continuous_re.continuousAt.tendsto.comp (hz.comp hc))

theorem solution
    (σ C : ℝ) (hσ : σ ≤ 1) (hC : 0 ≤ C)
    (H : ∀ N : ℕ, |∑ n ∈ range N, (moebius n : ℝ) * (n : ℝ)^(-σ)| ≤ C)
    (U : ℕ) :
    |∑ n ∈ range (U+1), (moebius n : ℝ) / (n:ℝ)| ≤
      2*C*((U:ℝ)+1)^(σ-1) := by
  let P (s : ℝ) (N : ℕ) := ∑ n ∈ range N, (moebius n : ℝ) * (n:ℝ)^(-s)
  have htail (s : ℝ) (hs : 1 < s) :
      |((riemannZeta (s:ℂ))⁻¹).re - P s (U+1)| ≤ 2*C*((U:ℝ)+1)^(σ-1) := by
    apply le_of_tendsto (((mu_series_real s hs).sub_const (P s (U+1))).abs)
    filter_upwards [eventually_gt_atTop (U+1)] with N hN
    have h := abel_interval (fun i : ℕ => (i:ℝ)^(σ-s))
      (fun i : ℕ => (moebius i:ℝ)*(i:ℝ)^(-σ)) C H (U+1) N hN
      (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)
      (fun i hi => Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < i by omega))
        (by exact_mod_cast Nat.le_succ i) (by linarith))
    have he : ∑ i ∈ Ico (U+1) N, ((i:ℝ)^(σ-s))*((moebius i:ℝ)*(i:ℝ)^(-σ)) =
        P s N-P s (U+1) := by
      dsimp [P]
      rw [←sum_Ico_eq_sub _ hN.le]
      apply sum_congr rfl
      intro i hi
      have hip : (0:ℝ) < i := by exact_mod_cast (show 0 < i by have := (mem_Ico.mp hi).1; omega)
      rw [mul_left_comm,←Real.rpow_add hip]
      congr 2; ring
    rw [he,Nat.cast_add_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α:=ℝ) U] : 1 ≤ (U:ℝ)+1) (by linarith))
      (by positivity))
  have hc : Continuous (fun s : ℝ => P s (U+1)) := by
    apply continuous_finsetSum
    intro i _
    by_cases hi : i = 0
    · simpa [hi] using (continuous_const : Continuous (fun _ : ℝ => (0:ℝ)))
    · exact continuous_const.mul ((Real.continuous_const_rpow (by exact_mod_cast hi)).comp continuous_neg)
  have hb := le_of_tendsto ((zeta_inv_real_boundary.sub
    ((hc.continuousAt (x:=1)).tendsto.mono_left nhdsWithin_le_nhds)).abs)
    (Filter.mem_of_superset self_mem_nhdsWithin (fun s hs => htail s hs))
  simpa [P, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv] using hb

