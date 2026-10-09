-- Prove2me | solution 1 for ConnesGreen.canonical_picard_half_iff_integral_gram_certificates
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T21:44:46.662081+00:00
-- url     : https://prove2.me/submissions/011bc857-fb9f-4763-8450-87bab72adc6e

import Theorems.Thm_ConnesGreen_canonical_source_gram_eq_green_integral
import Theorems.Thm_ConnesGreen_canonical_picard_half_iff_finite_gram_certificates
import Definitions.Def_ConnesGreen_integral_certificate_kernel
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative MeasureTheory Matrix
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
namespace ConnesGreen
private theorem reflected_mult_helper (ρ : CriticalZeros) :
    ConnesRZ.zeroMult (reflectedZero ρ).1 = ConnesRZ.zeroMult ρ.1 := by
  change Zeta23.zeroMult (Zeta23.reflect ρ.1) = Zeta23.zeroMult ρ.1
  exact Zeta23.zeta_mult_reflect ρ.1 ρ.2

theorem canonical_pair_gram_eq_kernel (t : ℝ) (ht : 0 < t) (ε η : ℝ)
    (ρ σ : CriticalZeros) :
    let w := weightedGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ))
    ⟪(1 / 2 : ℂ) • (w ρ + ε • w (reflectedZero ρ)),
      (1 / 2 : ℂ) • (w σ + η • w (reflectedZero σ))⟫_ℂ =
      canonicalPairGramKernel t ε η ρ σ := by
  dsimp only
  simp only [weightedGreenColumn, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, RCLike.real_smul_eq_coe_smul (K := ℂ),
    RCLike.conj_ofReal, canonical_source_gram_eq_green_integral t ht,
    reflected_mult_helper, canonicalPairGramKernel, map_div₀, map_one, map_ofNat]
  have hc (r : ℝ) : (starRingEnd ℂ) (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  simp only [hc]
  ring!

theorem canonicalFiniteColumnKernel_eq_gram (t : ℝ) (ht : 0 < t)
    (S F : Finset CriticalZeros) :
    canonicalFiniteColumnKernel t S F =
      fun i j => ⟪canonicalFiniteActorFamily t S F i, canonicalFiniteActorFamily t S F j⟫_ℂ := by
  ext i j
  cases i with
  | inl ρ =>
    cases j with
    | inl σ =>
      simpa only [canonicalFiniteColumnKernel, canonicalFiniteActorFamily, Sum.elim_inl,
        positiveGreenColumn, one_smul] using (canonical_pair_gram_eq_kernel t ht 1 1 ρ.1 σ.1).symm
    | inr σ =>
      simpa only [canonicalFiniteColumnKernel, canonicalFiniteActorFamily, Sum.elim_inl,
        Sum.elim_inr, positiveGreenColumn, negativeGreenColumn, one_smul,
        neg_one_smul, sub_eq_add_neg] using (canonical_pair_gram_eq_kernel t ht 1 (-1) ρ.1 σ.1).symm
  | inr ρ =>
    cases j with
    | inl σ =>
      simpa only [canonicalFiniteColumnKernel, canonicalFiniteActorFamily, Sum.elim_inl,
        Sum.elim_inr, positiveGreenColumn, negativeGreenColumn, one_smul,
        neg_one_smul, sub_eq_add_neg] using (canonical_pair_gram_eq_kernel t ht (-1) 1 ρ.1 σ.1).symm
    | inr σ =>
      simpa only [canonicalFiniteColumnKernel, canonicalFiniteActorFamily, Sum.elim_inr,
        negativeGreenColumn, neg_one_smul, sub_eq_add_neg] using
          (canonical_pair_gram_eq_kernel t ht (-1) (-1) ρ.1 σ.1).symm

theorem canonical_finite_gram_eq_integral_certificate (t : ℝ) (ht : 0 < t)
    (S F : Finset CriticalZeros) (δ : ℝ) :
    canonicalFiniteCertificateGram t S F δ = canonicalFiniteIntegralCertificate t S F δ := by
  unfold canonicalFiniteIntegralCertificate
  rw [canonicalFiniteColumnKernel_eq_gram t ht S F]
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply]
  simp only [canonicalFiniteCertificateGram, canonicalFiniteCertificateOperator,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.sum_apply, inner_sub_right, inner_add_right, inner_sum,
    RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right,
    InnerProductSpace.inner_right_rankOne_apply,
    smul_eq_mul, Matrix.mul_diagonal, Fintype.sum_sum_type,
    canonicalFiniteActorFamily, Sum.elim_inl, Sum.elim_inr, mul_one, mul_neg_one]
  change (δ : ℂ) * ⟪canonicalFiniteActorFamily t S F i,
      canonicalFiniteActorFamily t S F j⟫_ℂ +
    (∑ ρ ∈ F, ⟪canonicalFiniteActorFamily t S F i,
      positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ⟫_ℂ *
      ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ,
        canonicalFiniteActorFamily t S F j⟫_ℂ) -
    (∑ ρ ∈ S, ⟪canonicalFiniteActorFamily t S F i,
      negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ⟫_ℂ *
      ⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ,
        canonicalFiniteActorFamily t S F j⟫_ℂ) =
    (δ : ℂ) * ⟪canonicalFiniteActorFamily t S F i,
      canonicalFiniteActorFamily t S F j⟫_ℂ +
    ((∑ ρ : {ρ : CriticalZeros // ρ ∈ F}, ⟪canonicalFiniteActorFamily t S F i,
      positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1⟫_ℂ *
      ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1,
        canonicalFiniteActorFamily t S F j⟫_ℂ) +
    (∑ ρ : {ρ : CriticalZeros // ρ ∈ S}, -⟪canonicalFiniteActorFamily t S F i,
      negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1⟫_ℂ *
      ⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1,
        canonicalFiniteActorFamily t S F j⟫_ℂ))
  rw [Finset.sum_subtype (F := inferInstance) (p := fun ρ : CriticalZeros => ρ ∈ F) F (fun _ => Iff.rfl) (fun ρ =>
    ⟪canonicalFiniteActorFamily t S F i,
      positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ⟫_ℂ *
    ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ,
      canonicalFiniteActorFamily t S F j⟫_ℂ)]
  rw [Finset.sum_subtype (F := inferInstance) (p := fun ρ : CriticalZeros => ρ ∈ S) S (fun _ => Iff.rfl) (fun ρ =>
    ⟪canonicalFiniteActorFamily t S F i,
      negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ⟫_ℂ *
    ⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ,
      canonicalFiniteActorFamily t S F j⟫_ℂ)]
  simp only [neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg, add_assoc]

theorem canonical_positive_column_norm_sq_eq_kernel (t : ℝ) (ht : 0 < t)
    (ρ : CriticalZeros) :
    ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ‖ ^ 2 =
      (canonicalPairGramKernel t 1 1 ρ ρ).re := by
  have h := congrArg Complex.re (canonical_pair_gram_eq_kernel t ht 1 1 ρ ρ)
  simp only [one_smul] at h
  change RCLike.re ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ,
    positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ⟫_ℂ = _ at h
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ)] at h
  exact h

theorem canonical_positive_kernel_diagonal_nonnegative (t : ℝ) (ht : 0 < t)
    (ρ : CriticalZeros) : 0 ≤ (canonicalPairGramKernel t 1 1 ρ ρ).re := by
  rw [← canonical_positive_column_norm_sq_eq_kernel t ht]
  exact sq_nonneg _

theorem canonical_positive_kernel_diagonal_summable (t : ℝ) (ht : 0 < t) :
    Summable (fun ρ : CriticalZeros => (canonicalPairGramKernel t 1 1 ρ ρ).re) := by
  simpa only [canonical_positive_column_norm_sq_eq_kernel t ht] using
    (canonical_actor_columns_summable t ht).1


end ConnesGreen
theorem solution
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S) ↔
    ∀ δ : ℝ, 0 < δ → ∃ F : Finset CriticalZeros,
      S ⊆ F ∧ (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
      (∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
        (canonicalPairGramKernel t 1 1 ρ.1 ρ.1).re) < δ ∧
      (canonicalFiniteIntegralCertificate t S F δ).PosSemidef := by
  rw [canonical_picard_half_iff_finite_gram_certificates]
  simp only [canonical_positive_column_norm_sq_eq_kernel t ht,
    canonical_finite_gram_eq_integral_certificate t ht]
