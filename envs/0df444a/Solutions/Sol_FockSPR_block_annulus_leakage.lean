-- Prove2me | solution 1 for FockSPR.block_annulus_leakage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:50.360963+00:00
-- url     : https://prove2.me/submissions/66e30319-e2b9-4c1a-b735-b4957773571d

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LaplaceFactorial
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LeakageEstimate
public import Theorems.Thm_FockSPR_monomial_integral_bound
public import Theorems.Thm_FockSPR_monomial_peak_localization

section
@[expose] public section
open MeasureTheory Real Finset Complex
noncomputable section
namespace FockSPR
private lemma fourier_pow (n : ℕ) (t : AddCircle T) :
    ((fourier 1 t : ℂ) ^ n : ℂ) = (fourier (n : ℤ) t : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← fourier_add]; push_cast; ring
private lemma integral_fourier (n : ℤ) :
    ∫ t : AddCircle T, (fourier n t : ℂ) ∂AddCircle.haarAddCircle =
    if n = 0 then 1 else 0 := by
  have h := fourierCoeff_fourier (T := T) 0
  have h1 := congr_fun h (-n)
  simp only [Pi.single_apply] at h1
  rw [fourierCoeff] at h1
  simp_all
private lemma fourier_orthogonality (m n : ℤ) :
    ∫ t : AddCircle T, (fourier m t : ℂ) * (starRingEnd ℂ) (fourier n t : ℂ)
      ∂AddCircle.haarAddCircle =
    if m = n then 1 else 0 := by
  have key : ∀ t : AddCircle T,
      (fourier m t : ℂ) * (starRingEnd ℂ) (fourier n t : ℂ) = (fourier (m - n) t : ℂ) := by
    intro t; rw [← fourier_neg (n := n), ← fourier_add]; ring_nf
  simp_rw [key]; rw [integral_fourier]; simp [sub_eq_zero]
private lemma blockPoly_fourier_expansion {D : ℕ} (a : Fin D → ℂ) (ℓ : ℕ)
    (r : ℝ) (t : AddCircle T) :
    blockPoly a ℓ (↑r * (fourier 1 t : ℂ)) =
    ∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
      then (a k * (r : ℂ) ^ (k.val + 1)) * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)
      else 0 := by
  unfold blockPoly
  congr 1; ext k; split_ifs with h
  · have : (↑r * (fourier 1 t : ℂ)) ^ (k.val + 1) =
        (r : ℂ) ^ (k.val + 1) * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ) := by
      rw [mul_pow, ← fourier_pow]
    rw [this]; ring
  · rfl
private lemma dist_peak_to_interval {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hn : n ∈ freqBlock ℓ) (j : ℕ) :
    distToInterval (rStar n) j ≥ max ((j : ℤ) - ℓ - 1) (ℓ - j - 1) := by
  obtain ⟨hlo, hhi⟩ := monomial_peak_localization hℓ hn
  unfold distToInterval rStar at *
  push_cast
  simp only [le_max_iff, max_le_iff]
  by_cases hjl : j ≥ ℓ + 1
  · left; left
    constructor
    · linarith only [hhi]
    · have : (j : ℝ) ≥ ℓ + 1 := by exact_mod_cast hjl
      linarith only [hlo, hhi, this]
  · push Not at hjl
    by_cases hjl2 : j + 1 ≤ ℓ
    · left; right
      constructor
      · have : (j : ℝ) + 1 ≤ ℓ := by exact_mod_cast hjl2
        linarith only [hlo, hhi, this]
      · have : (j : ℝ) + 1 ≤ ℓ := by exact_mod_cast hjl2
        linarith only [hlo]
    · push Not at hjl2
      have hje : j = ℓ := by omega
      simp_all
private lemma distToInterval_nonneg (x : ℝ) (j : ℕ) : 0 ≤ distToInterval x j := by
  unfold distToInterval; exact le_max_right _ _
private lemma dist_peak_ge_max_zero {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hn : n ∈ freqBlock ℓ) (j : ℕ) :
    distToInterval (rStar n) j ≥ max ((j : ℤ) - ℓ - 1) 0 := by
  have hdist := dist_peak_to_interval hℓ hn j
  have hnonneg := distToInterval_nonneg (rStar n) j
  -- From hdist: distToInterval ≥ max(j-ℓ-1, ℓ-j-1) ≥ j-ℓ-1
  -- From hnonneg: distToInterval ≥ 0
  -- Together: distToInterval ≥ max(j-ℓ-1, 0)
  simp_all
private lemma blockPoly_circle_norm_sq {D : ℕ} (a : Fin D → ℂ) (ℓ : ℕ) (r : ℝ) :
    ∫ t : AddCircle T, ‖blockPoly a ℓ (↑r * (fourier 1 t : ℂ))‖ ^ 2
      ∂AddCircle.haarAddCircle =
    ∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
      then ‖a k‖ ^ 2 * (r : ℝ) ^ (2 * (k.val + 1)) else 0 := by
  -- Define coefficients and rewrite blockPoly as Fourier series
  set c : Fin D → ℂ := fun k =>
    if (k.val + 1) ∈ freqBlock ℓ then a k * (r : ℂ) ^ (k.val + 1) else 0 with hc_def
  have hbp : ∀ t : AddCircle T,
      blockPoly a ℓ (↑r * (fourier 1 t : ℂ)) =
      ∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ) := by
    intro t; rw [blockPoly_fourier_expansion]
    congr 1; ext k; simp only [hc_def]; split_ifs <;> simp
  simp_rw [hbp]
  -- The RHS can be rewritten in terms of ‖c k‖
  suffices h : ∀ k : Fin D,
      (if (k.val + 1) ∈ freqBlock ℓ then ‖a k‖ ^ 2 * r ^ (2 * (k.val + 1)) else 0) =
      ‖c k‖ ^ 2 by
    simp_rw [h]
    -- Now need: ∫ ‖∑ c_k fourier(k+1)‖² = ∑ ‖c_k‖²
    -- Helper: continuous functions on AddCircle are integrable (compact + finite measure)
    have hci : ∀ (g : AddCircle T → ℂ), Continuous g → Integrable g AddCircle.haarAddCircle :=
      fun g hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hfc : Continuous (fun t : AddCircle T =>
        ∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)) :=
      continuous_finsetSum _ fun k _ => continuous_const.mul (fourier _).continuous
    -- Integrability for pairs
    have hint_pair : ∀ (k1 k2 : Fin D), Integrable (fun t : AddCircle T =>
        (c k1 * (starRingEnd ℂ) (c k2)) *
        ((fourier ((k1.val + 1 : ℕ) : ℤ) t : ℂ) *
         (starRingEnd ℂ) (fourier ((k2.val + 1 : ℕ) : ℤ) t : ℂ)))
        AddCircle.haarAddCircle :=
      fun k1 k2 => hci _ (continuous_const.mul
        ((fourier _).continuous.mul (continuous_star.comp (fourier _).continuous)))
    -- Compute complex integral of f * conj f
    have hcx_int : ∫ t : AddCircle T,
        (∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)) *
        (starRingEnd ℂ) (∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ))
        ∂AddCircle.haarAddCircle =
        ↑(∑ k : Fin D, ‖c k‖ ^ 2) := by
      -- Expand
      simp_rw [map_sum, Finset.mul_sum, Finset.sum_mul, map_mul]
      -- Rearrange each term
      simp_rw [show ∀ (k1 k2 : Fin D) (t : AddCircle T),
          c k1 * (fourier ((k1.val + 1 : ℕ) : ℤ) t : ℂ) *
          ((starRingEnd ℂ) (c k2) *
           (starRingEnd ℂ) (fourier ((k2.val + 1 : ℕ) : ℤ) t : ℂ)) =
          (c k1 * (starRingEnd ℂ) (c k2)) *
          ((fourier ((k1.val + 1 : ℕ) : ℤ) t : ℂ) *
           (starRingEnd ℂ) (fourier ((k2.val + 1 : ℕ) : ℤ) t : ℂ))
        from fun k1 k2 t => by ring]
      -- Exchange integral and double sum
      rw [integral_finsetSum _ (fun k2 _ =>
        integrable_finsetSum _ (fun k1 _ => hint_pair k1 k2))]
      simp_rw [integral_finsetSum _ (fun k1 _ => hint_pair k1 _)]
      -- Each term: const * ∫ fourier * conj(fourier)
      -- Each integral: ∫ const * (fourier * conj(fourier)) = const * ∫ (fourier * conj(fourier))
      -- = const * δ(k1, k2) by fourier_orthogonality
      -- Evaluate each integral and collapse
      have heval : ∀ (k1 k2 : Fin D),
          ∫ (a : AddCircle T),
            c k1 * (starRingEnd ℂ) (c k2) *
            ((fourier ((k1.val + 1 : ℕ) : ℤ) a : ℂ) *
             (starRingEnd ℂ) (fourier ((k2.val + 1 : ℕ) : ℤ) a : ℂ))
          ∂AddCircle.haarAddCircle =
          if k1 = k2 then (↑(‖c k1‖ ^ 2) : ℂ) else 0 := by
        intro k1 k2
        have : ∫ (t : AddCircle T),
            c k1 * (starRingEnd ℂ) (c k2) *
            ((fourier ((k1.val + 1 : ℕ) : ℤ) t : ℂ) *
             (starRingEnd ℂ) (fourier ((k2.val + 1 : ℕ) : ℤ) t : ℂ))
            ∂AddCircle.haarAddCircle =
            c k1 * (starRingEnd ℂ) (c k2) *
            ∫ (t : AddCircle T),
              (fourier ((k1.val + 1 : ℕ) : ℤ) t : ℂ) *
              (starRingEnd ℂ) (fourier ((k2.val + 1 : ℕ) : ℤ) t : ℂ)
            ∂AddCircle.haarAddCircle :=
          MeasureTheory.integral_const_mul _ _
        rw [this, fourier_orthogonality]
        by_cases hkk : k1 = k2
        · subst hkk
          simp only [ite_true, mul_one, Complex.mul_conj']; push_cast; rfl
        · have hne : ¬((k1.val + 1 : ℕ) : ℤ) = ((k2.val + 1 : ℕ) : ℤ) := by push_cast; omega
          simp only [hne, ite_false, mul_zero, hkk]
      simp_all
    -- From complex integral to real integral:
    -- ‖f t‖² = re(f t * conj(f t)), so ∫ ‖f‖² = re(∫ f * conj f) = ∑ ‖c_k‖²
    have hfconj : ∀ t : AddCircle T,
        (‖∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)‖ ^ 2 : ℝ) =
        ((∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)) *
         (starRingEnd ℂ) (∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ))).re := by
      intro t; rw [Complex.mul_conj']; norm_cast
    conv_lhs => arg 2; ext t; rw [hfconj t]
    have hfci : Integrable (fun t : AddCircle T =>
        (∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)) *
        (starRingEnd ℂ) (∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)))
        AddCircle.haarAddCircle :=
      hci _ (hfc.mul (continuous_star.comp hfc))
    -- ∫ re(g) = re(∫ g) for integrable g
    have key : ∫ (t : AddCircle T),
        ((∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)) *
          (starRingEnd ℂ) (∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ))).re
        ∂AddCircle.haarAddCircle =
      (∫ (t : AddCircle T),
        (∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)) *
        (starRingEnd ℂ) (∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ))
        ∂AddCircle.haarAddCircle).re := by
      change (∫ (t : AddCircle T),
          RCLike.re ((∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)) *
            (starRingEnd ℂ) (∑ k : Fin D, c k * (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ)))
          ∂AddCircle.haarAddCircle) = _
      exact integral_re hfci
    rw [key, hcx_int]; norm_cast
  intro k; simp only [hc_def]
  split_ifs with h
  · -- Goal: ‖a k‖² * r^{2(k+1)} = ‖a k * (↑r)^{k+1}‖²
    rw [Complex.norm_mul, mul_pow, Complex.norm_pow, Complex.norm_real,
      Real.norm_eq_abs, ← pow_mul]
    congr 1
    rw [show (k.val + 1) * 2 = 2 * (k.val + 1) from by ring]
    exact (Even.pow_abs ⟨k.val + 1, by ring⟩ r).symm
  · simp
end FockSPR
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Real Finset Complex
noncomputable section
open FockSPR
namespace FockSPR
theorem _root_.solution {D : ℕ} (a : Fin D → ℂ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (j : ℕ) :
    2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
      (∫ t : AddCircle T, ‖blockPoly a ℓ (↑r * (fourier 1 t : ℂ))‖ ^ 2
        ∂AddCircle.haarAddCircle) ≤
      Real.exp (1 / 4) *
        Real.exp (-(max ((j : ℤ) - ℓ - 1) 0 : ℤ) ^ 2) *
        (∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
          then ‖a k‖ ^ 2 * (Nat.factorial (k.val + 1) : ℝ) else 0) := by
  -- Step 1: Substitute the circle Parseval identity
  simp_rw [blockPoly_circle_norm_sq]
  -- Step 2: Rewrite each radial integrand to factor per-k
  have integrand_eq : ∀ (r : ℝ),
      r * Real.exp (-r ^ 2) *
        (∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
          then ‖a k‖ ^ 2 * r ^ (2 * (k.val + 1)) else 0) =
      ∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
        then ‖a k‖ ^ 2 * (r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) else 0 := by
    intro r
    rw [Finset.mul_sum]
    congr 1; ext k; split_ifs with h
    · ring
    · simp
  simp_rw [integrand_eq]
  -- Step 3: Bound each radial integral using monomial_integral_bound
  -- For each k with k+1 ∈ I_ℓ:
  --   ∫ r^{2(k+1)+1} exp(-r²) ≤ exp(1/4) * (k+1)!/2 * exp(-dist(r_{k+1},[j,j+1])²)
  -- Then: ‖a_k‖² * ∫ ... ≤ ‖a_k‖² * exp(1/4) * (k+1)!/2 * exp(-max(j-ℓ-1,0)²)
  -- (using dist_peak_ge_max_zero)
  -- Note: 2 * ∑ (‖a_k‖² * exp(1/4) * (k+1)!/2 * exp(-d²))
  --      = exp(1/4) * exp(-d²) * ∑ ‖a_k‖² * (k+1)!

  -- Establish per-k bounds
  have hk_bound : ∀ k : Fin D, (k.val + 1) ∈ freqBlock ℓ →
      2 * (‖a k‖ ^ 2 * ∫ r in (j : ℝ)..(j + 1 : ℝ),
        r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) ≤
      Real.exp (1 / 4) * Real.exp (-(max ((j : ℤ) - ℓ - 1) 0 : ℤ) ^ 2) *
        (‖a k‖ ^ 2 * (Nat.factorial (k.val + 1) : ℝ)) := by
    intro k hk
    have hn : 1 ≤ k.val + 1 := Nat.succ_le_succ (Nat.zero_le _)
    -- Apply monomial_integral_bound
    have hmib := monomial_integral_bound hn j
    -- hmib : ∫ r^{2*(k+1)+1} exp(-r²) ≤ exp(1/4) * (k+1)!/2 * exp(-dist²)
    -- Bound distance: dist(r_{k+1}, [j,j+1]) ≥ max(j-ℓ-1, 0)
    have hdist := dist_peak_ge_max_zero hℓ hk j
    -- exp(-dist²) ≤ exp(-max(j-ℓ-1,0)²)
    have hexp_mono : Real.exp (-(distToInterval (rStar (k.val + 1)) j) ^ 2) ≤
        Real.exp (-(max ((j : ℤ) - ℓ - 1) 0 : ℤ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      have h0 : (0 : ℝ) ≤ (max ((j : ℤ) - ℓ - 1) 0 : ℤ) := by
        exact_mod_cast le_max_right ((j : ℤ) - ℓ - 1) 0
      exact pow_le_pow_left₀ h0 (by exact_mod_cast hdist) 2
    -- Now: 2 * ‖a_k‖² * ∫ ≤ 2 * ‖a_k‖² * exp(1/4) * (k+1)!/2 * exp(-max(...)²)
    --    = ‖a_k‖² * exp(1/4) * (k+1)! * exp(-max(...)²)
    --    = exp(1/4) * exp(-max(...)²) * (‖a_k‖² * (k+1)!)
    have hint_bound : ∫ r in (j : ℝ)..(j + 1 : ℝ),
        r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2) ≤
        Real.exp (1 / 4) * (Nat.factorial (k.val + 1) : ℝ) / 2 *
        Real.exp (-(max ((j : ℤ) - ℓ - 1) 0 : ℤ) ^ 2) := by
      calc ∫ r in (j : ℝ)..(j + 1 : ℝ),
            r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)
        ≤ Real.exp (1 / 4) * (Nat.factorial (k.val + 1) : ℝ) / 2 *
            Real.exp (-(distToInterval (rStar (k.val + 1)) j) ^ 2) :=
          monomial_integral_bound hn j
        _ ≤ Real.exp (1 / 4) * (Nat.factorial (k.val + 1) : ℝ) / 2 *
            Real.exp (-(max ((j : ℤ) - ℓ - 1) 0 : ℤ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left hexp_mono
          apply div_nonneg
          · apply mul_nonneg (le_of_lt (Real.exp_pos _))
            exact_mod_cast (Nat.factorial_pos (k.val + 1)).le
          · norm_num
    -- Combine: 2 * ‖a_k‖² * ∫ ≤ exp(1/4) * exp(-d²) * ‖a_k‖² * (k+1)!
    nlinarith only [hint_bound, sq_nonneg (‖a k‖), Real.exp_pos (1 / 4 : ℝ),
        Real.exp_pos (-(max ((j : ℤ) - ℓ - 1) 0 : ℤ) ^ 2 : ℝ), Nat.factorial_pos (k.val + 1)]
  -- Step 4: Exchange integral and sum, then apply per-k bounds
  -- First, prove integrability of each summand
  have hint : ∀ k : Fin D, IntervalIntegrable
      (fun r : ℝ => if (k.val + 1) ∈ freqBlock ℓ
        then ‖a k‖ ^ 2 * (r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) else 0)
      (volume : Measure ℝ) (j : ℝ) (j + 1 : ℝ) := by
    intro k
    by_cases h : (k.val + 1) ∈ freqBlock ℓ
    · simp only [h, ite_true]
      apply Continuous.intervalIntegrable
      exact continuous_const.mul ((continuous_pow _).mul
        (Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))))
    · simp_all
  -- Exchange integral and sum: ∫ ∑ f_k = ∑ ∫ f_k
  rw [intervalIntegral.integral_finsetSum (μ := volume) (fun k _ => hint k)]
  -- Pull the if outside each integral
  have hpull_if : ∀ k : Fin D,
      ∫ (r : ℝ) in (j : ℝ)..(j + 1 : ℝ),
        (if (k.val + 1) ∈ freqBlock ℓ
          then ‖a k‖ ^ 2 * (r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) else 0) =
      if (k.val + 1) ∈ freqBlock ℓ
        then ‖a k‖ ^ 2 * ∫ (r : ℝ) in (j : ℝ)..(j + 1 : ℝ),
          r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)
        else 0 := by
    intro k
    split_ifs with h
    · rw [intervalIntegral.integral_const_mul]
    · simp
  simp_rw [hpull_if]
  -- Now: 2 * ∑_k [h] ‖a_k‖² * ∫ f_k ≤ exp(1/4) * exp(-d²) * ∑_k [h] ‖a_k‖² * (k+1)!
  rw [mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  split_ifs with h
  · exact hk_bound k h
  · simp
end FockSPR
