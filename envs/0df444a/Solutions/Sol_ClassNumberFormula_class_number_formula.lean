-- Prove2me | solution 1 for ClassNumberFormula.class_number_formula
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T15:52:42.851195+00:00
-- url     : https://prove2.me/submissions/b80d53c4-e503-4a47-b11d-9b80c7d76f32
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_ClassNumberFormula_dedekindZeta_entire_factor

open Ideal Finset Filter Asymptotics Topology NumberField
open NumberField.InfinitePlace NumberField.Units NumberField.Ideal
open scoped Real

set_option autoImplicit false

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

private def idealCoeff (n : ℕ) : ℝ :=
  (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ)

private lemma idealCoeff_nonneg (n : ℕ) : 0 ≤ idealCoeff (K := K) n :=
  Nat.cast_nonneg _

private lemma zeroIdeal_mem_norm_le (n : ℕ) :
    (⊥ : Ideal (𝓞 K)) ∈ {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ n} := by
  simp [Ideal.absNorm_bot]

private lemma norm_zero_subset_norm_le (n : ℕ) :
    {I : Ideal (𝓞 K) | Ideal.absNorm I = 0} ⊆ {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ n} := by
  intro I hI
  have hzero : Ideal.absNorm I = 0 := by simp [Set.mem_ofPred_eq] at hI; exact hI
  have hbot : I = ⊥ := (Ideal.absNorm_eq_zero_iff).mp hzero
  simp [hbot, zeroIdeal_mem_norm_le (K := K) n]

private lemma sum_range_idealCoeff (n : ℕ) :
    ∑ k ∈ Icc 0 n, Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} =
      Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} := by
  classical
  rw [← Finset.card_preimage_eq_sum_card_image_eq
    (fun k (_ : k ∈ Icc 0 n) => Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) k)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun I => ?_)
  simp

private lemma sum_idealCoeff (n : ℕ) :
    ∑ k ∈ Icc 1 n, idealCoeff (K := K) k =
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} : ℝ) - 1 := by
  have h0 : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} = 1 := by
    simp [Ideal.absNorm_eq_zero_iff]
  have hsplit : ∑ k ∈ Icc 0 n, Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} =
      Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} +
        ∑ k ∈ Icc 1 n, Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} := by
    have hmem : (0 : ℕ) ∈ Icc 0 n := mem_Icc.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩
    rw [← Finset.sum_erase_add (f := fun k => Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k})
      _ hmem]
    have herase : (Icc (0 : ℕ) n).erase 0 = Icc 1 n := by
      ext k
      simp [mem_Icc]
      omega
    rw [herase, add_comm]
  have hnat := sum_range_idealCoeff (K := K) n
  rw [hsplit, h0] at hnat
  have hsub : ∑ k ∈ Icc 1 n, Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} =
      Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} - 1 := by
    omega
  have hone : (1 : ℕ) ≤ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} := by
    rw [← h0]
    exact Nat.card_mono (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) n)
      (norm_zero_subset_norm_le (K := K) n)
  rw [show ∑ k ∈ Icc 1 n, idealCoeff (K := K) k =
      (∑ k ∈ Icc 1 n, Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ) by
    simp [idealCoeff]]
  rw [← Nat.cast_sum, hsub, Nat.cast_sub hone]
  simp

private lemma idealCoeff_partial_isBigO :
    (fun n : ℕ => ∑ k ∈ Icc 1 n, idealCoeff (K := K) k) =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
  have hcard : Tendsto (fun n : ℕ =>
      (Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ (n : ℝ)} : ℝ) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue K)) :=
    (tendsto_norm_le_div_atTop K).comp tendsto_natCast_atTop_atTop
  have hsame : ∀ n : ℕ,
      Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ (n : ℝ)} =
        Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} := by
    intro n
    refine Nat.card_congr (Equiv.subtypeEquivRight fun I => ?_)
    simp [Nat.cast_le]
  have hcardNat : Tendsto (fun n : ℕ =>
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} : ℝ) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue K)) :=
    hcard.congr fun n => by rw [hsame n]
  have hbig : (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} : ℝ)) =O[atTop]
      fun n => (n : ℝ) :=
    isBigO_of_div_tendsto_nhds
      (by
        filter_upwards [eventually_gt_atTop 0] with n hn h0
        exact absurd h0 (by positivity : (n : ℝ) ≠ 0))
      (dedekindZeta_residue K) hcardNat
  have hsum : (fun n : ℕ => ∑ k ∈ Icc 1 n, idealCoeff (K := K) k) =O[atTop]
      fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} : ℝ) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards with n
    rw [sum_idealCoeff (K := K) n, Real.norm_eq_abs, one_mul]
    have hnn : 0 ≤ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} : ℝ) - 1 := by
      have hone : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} = 1 := by
        simp [Ideal.absNorm_eq_zero_iff]
      have hle : 1 ≤ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} := by
        rw [← hone]
        exact Nat.card_mono (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) n)
          (norm_zero_subset_norm_le (K := K) n)
      have hleR : (1 : ℝ) ≤ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} := by
        exact_mod_cast hle
      linarith
    have hcard_nn : 0 ≤ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} : ℝ) :=
      Nat.cast_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_nonneg hcard_nn]
    linarith
  exact (hsum.trans hbig).congr_right (fun n => by simp)

private lemma dedekindZeta_norm_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖LSeries.term
      (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s n‖) := by
  have hL : LSeriesSummable (fun n => (idealCoeff (K := K) n : ℂ)) (s.re : ℂ) :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg idealCoeff_partial_isBigO
      idealCoeff_nonneg zero_le_one (by simpa using hs)
  have hnorm : ∀ n, ‖LSeries.term
      (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s n‖ =
      (LSeries.term (fun n => (idealCoeff (K := K) n : ℂ)) (s.re : ℂ) n).re := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.term]
    by_cases hn : n = 0
    · simp [hn]
    · have hpow : (n : ℂ) ^ (s.re : ℂ) = Complex.ofReal ((n : ℝ) ^ s.re) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_cpow (Nat.cast_nonneg n) s.re]
      simp only [if_neg hn, idealCoeff, hpow, Complex.norm_natCast]
      rw [← Complex.ofReal_div (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ)
        ((n : ℝ) ^ s.re), Complex.ofReal_re]
  have hcoe : ∀ n, LSeries.term (fun n => (idealCoeff (K := K) n : ℂ)) (s.re : ℂ) n =
      (‖LSeries.term (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s n‖ : ℂ) := by
    intro n
    rw [hnorm n]
    by_cases hn0 : n = 0
    · simp [hn0, LSeries.term]
    · rw [LSeries.term, if_neg hn0]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n), ← Complex.ofReal_div]
      simp
  unfold LSeriesSummable at hL
  rw [show LSeries.term (fun n => (idealCoeff (K := K) n : ℂ)) (s.re : ℂ) =
      fun n => (‖LSeries.term
        (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s n‖ : ℂ) from
    funext hcoe] at hL
  exact (Complex.summable_ofReal).mp hL

theorem solution (K : Type*) [Field K] [NumberField K] :
    (∀ s : ℂ, 1 < s.re → Summable (fun n : ℕ => ‖LSeries.term
      (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s n‖)) ∧
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      G 1 = (((2 : ℝ) ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K *
          classNumber K / (torsionOrder K * Real.sqrt |(discr K : ℝ)|) : ℝ) : ℂ) ∧
      ∀ s : ℂ, 1 < s.re → dedekindZeta K s = G s / (s - 1) := by
  refine ⟨fun s hs => dedekindZeta_norm_summable (K := K) hs, ?_⟩
  obtain ⟨G, hG, hAgree⟩ := ClassNumberFormula.dedekindZeta_entire_factor K
  refine ⟨G, hG, ?_, ?_⟩
  · have hlim : Tendsto (fun s : ℝ => (s - 1) * dedekindZeta K s) (𝓝[>] 1)
        (𝓝 (dedekindZeta_residue K)) :=
      tendsto_sub_one_mul_dedekindZeta_nhdsGT K
    have hGlim : Tendsto (fun s : ℝ => G (s : ℂ)) (𝓝[>] 1) (𝓝 (G 1)) := by
      refine (hG.continuous.tendsto (1 : ℂ)).comp ?_
      exact (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    have hevent : (fun s : ℝ => G (s : ℂ)) =ᶠ[𝓝[>] 1]
        fun s : ℝ => (s - 1) * dedekindZeta K s := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hre : 1 < (s : ℂ).re := by simpa using hs
      exact hAgree s hre
    have hunique := tendsto_nhds_unique (hGlim.congr' hevent) hlim
    rw [dedekindZeta_residue_def] at hunique
    exact hunique
  · intro s hs
    have hne : s - 1 ≠ 0 := by
      intro h
      have : s.re = 1 := by
        have hs1 : s = 1 := sub_eq_zero.mp h
        simp [hs1]
      linarith
    rw [hAgree s hs, mul_div_cancel_left₀ _ hne]
