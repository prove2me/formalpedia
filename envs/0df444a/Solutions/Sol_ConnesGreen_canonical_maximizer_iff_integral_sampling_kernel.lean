-- Prove2me | solution 1 for ConnesGreen.canonical_maximizer_iff_integral_sampling_kernel
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T16:34:09.534796+00:00
-- url     : https://prove2.me/submissions/a19c3a5f-6854-4922-b4d4-48bc4941ef76

import Definitions.Def_ConnesGreen_positive_endpoint_support
import Definitions.Def_ConnesGreen_integral_certificate_kernel

import Theorems.Thm_ConnesGreen_canonical_source_gram_eq_green_integral
import Theorems.Thm_ConnesGreen_canonical_maximizer_mem_finite_actor_span
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative
namespace ConnesGreen
theorem canonical_mem_maximizingSpace_iff (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (x : Physical t) :
    x ∈ canonicalMaximizingSpace t ht S ↔
      canonicalLossCovariance t ht S x = (canonicalCertificateThreshold t ht S : ℂ) • x :=
  Module.End.mem_eigenspace_iff
theorem canonical_positive_covariance_of_finite_profile
    (t : ℝ) (ht : 0 < t) (F : Finset CriticalZeros) (x : Physical t)
    (hc : ∀ ρ : CriticalZeros, ρ ∉ F →
      ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) :
    canonicalPositiveCovariance t ht x =
      ∑ ρ ∈ F, ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ •
        positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ := by
  simp only [canonicalPositiveCovariance, ContinuousLinearMap.comp_apply,
    canonicalPositiveSynthesis]
  rw [columnSynthesis_apply]
  simp_rw [columnSynthesis_adjoint_coordinate]
  exact tsum_eq_sum (fun ρ hρ => by rw [hc ρ hρ, zero_smul])
theorem canonical_selected_covariance_finite_sum
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) (x : Physical t) :
    (canonicalSelectedSynthesis t ht S) ((canonicalSelectedSynthesis t ht S).adjoint x) =
      ∑ ρ ∈ S, ⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ •
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ := by
  unfold canonicalSelectedSynthesis
  rw [columnSynthesis_apply]
  simp_rw [columnSynthesis_adjoint_coordinate]
  exact Finset.tsum_subtype S (fun ρ : CriticalZeros =>
    ⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ •
      negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ)
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
private theorem span_zero_of_column_orthogonal
    {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype I]
    (u : I → H) (x : H) (hx : x ∈ Submodule.span ℂ (Set.range u))
    (hz : ∀ i, ⟪u i, x⟫_ℂ = 0) : x = 0 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).mp hx
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  calc
    ⟪x, x⟫_ℂ = ⟪∑ i, c i • u i, x⟫_ℂ := by rw [hc]
    _ = 0 := by simp only [sum_inner, inner_smul_left, hz, mul_zero, Finset.sum_const_zero]
theorem canonical_integral_gram_mulVec_coordinate
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ)
    (i : {ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) :
    (canonicalFiniteColumnKernel t S F *ᵥ c) i =
      ⟪canonicalFiniteActorFamily t S F i, ∑ j, c j • canonicalFiniteActorFamily t S F j⟫_ℂ := by
  rw [canonicalFiniteColumnKernel_eq_gram t ht S F]
  simp only [Matrix.mulVec, dotProduct, inner_sum, inner_smul_right, mul_comm]
theorem canonical_finite_actor_sum_ne_zero_iff
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ) :
    (∑ j, c j • canonicalFiniteActorFamily t S F j) ≠ 0 ↔
      canonicalFiniteColumnKernel t S F *ᵥ c ≠ 0 := by
  have he : (∑ j, c j • canonicalFiniteActorFamily t S F j) = 0 ↔
      canonicalFiniteColumnKernel t S F *ᵥ c = 0 := by
    constructor
    · intro h
      funext i
      rw [canonical_integral_gram_mulVec_coordinate t ht S F c i, h, inner_zero_right]
      rfl
    · intro h
      apply span_zero_of_column_orthogonal (canonicalFiniteActorFamily t S F)
      · exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
          (Submodule.subset_span ⟨i, rfl⟩))
      · intro i
        rw [← canonical_integral_gram_mulVec_coordinate t ht S F c i, h]
        rfl
  exact not_congr he
theorem canonical_integral_certificate_kernel_iff
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros) (δ : ℝ)
    (c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ) :
    canonicalFiniteIntegralCertificate t S F δ *ᵥ c = 0 ↔
      canonicalFiniteCertificateOperator t S F δ
        (∑ j, c j • canonicalFiniteActorFamily t S F j) = 0 := by
  let x := ∑ j, c j • canonicalFiniteActorFamily t S F j
  let V := Submodule.span ℂ (Set.range (canonicalFiniteActorFamily t S F))
  have hx : x ∈ V := Submodule.sum_mem V (fun i _ => V.smul_mem _
    (Submodule.subset_span ⟨i, rfl⟩))
  have hAx : canonicalFiniteCertificateOperator t S F δ x ∈ V := by
    simp only [canonicalFiniteCertificateOperator, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.sum_apply,
      InnerProductSpace.rankOne_apply]
    apply V.sub_mem
    · apply V.add_mem (V.smul_mem δ hx)
      apply V.sum_mem
      intro ρ hρ
      apply V.smul_mem
      exact Submodule.subset_span ⟨Sum.inl ⟨ρ, hρ⟩, rfl⟩
    · apply V.sum_mem
      intro ρ hρ
      apply V.smul_mem
      exact Submodule.subset_span ⟨Sum.inr ⟨ρ, hρ⟩, rfl⟩
  have hcoord (i) : (canonicalFiniteIntegralCertificate t S F δ *ᵥ c) i =
      ⟪canonicalFiniteActorFamily t S F i, canonicalFiniteCertificateOperator t S F δ x⟫_ℂ := by
    rw [← canonical_finite_gram_eq_integral_certificate t ht S F δ]
    simp only [canonicalFiniteCertificateGram, Matrix.mulVec, dotProduct, x,
      map_sum, map_smul, inner_sum, inner_smul_right, mul_comm]
  constructor
  · intro h
    apply span_zero_of_column_orthogonal (canonicalFiniteActorFamily t S F) _ hAx
    intro i
    rw [← hcoord i, h]
    rfl
  · intro h
    funext i
    rw [hcoord i, h, inner_zero_right]
    rfl
theorem canonical_sampled_operator_kernel_iff_maximizing
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros) (x : Physical t)
    (hc : ∀ ρ : CriticalZeros, ρ ∉ F →
      ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) :
    canonicalFiniteCertificateOperator t S F (canonicalCertificateThreshold t ht S) x = 0 ↔
      x ∈ canonicalMaximizingSpace t ht S := by
  have he : canonicalFiniteCertificateOperator t S F (canonicalCertificateThreshold t ht S) x =
      (canonicalCertificateThreshold t ht S : ℂ) • x - canonicalLossCovariance t ht S x := by
    simp only [canonicalFiniteCertificateOperator, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.sum_apply,
      InnerProductSpace.rankOne_apply]
    rw [canonicalLossCovariance, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      canonical_selected_covariance_finite_sum,
      canonical_positive_covariance_of_finite_profile t ht F x hc]
    change (canonicalCertificateThreshold t ht S : ℂ) • x + _ - _ = _
    abel
  rw [he, sub_eq_zero, canonical_mem_maximizingSpace_iff]
  exact eq_comm
theorem canonical_positive_sampling_row_eq_integral
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros) (ρ : CriticalZeros)
    (c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ) :
    (∑ j, ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ,
      canonicalFiniteActorFamily t S F j⟫_ℂ * c j) =
    ∑ j, (Sum.elim
      (fun σ : {σ : CriticalZeros // σ ∈ F} => canonicalPairGramKernel t 1 1 ρ σ.1)
      (fun σ : {σ : CriticalZeros // σ ∈ S} => canonicalPairGramKernel t 1 (-1) ρ σ.1) j) * c j := by
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  cases j with
  | inl σ =>
    simpa only [canonicalFiniteActorFamily, Sum.elim_inl, positiveGreenColumn, one_smul]
      using canonical_pair_gram_eq_kernel t ht 1 1 ρ σ.1
  | inr σ =>
    simpa only [canonicalFiniteActorFamily, Sum.elim_inr, positiveGreenColumn,
      negativeGreenColumn, one_smul, neg_one_smul, sub_eq_add_neg]
      using canonical_pair_gram_eq_kernel t ht 1 (-1) ρ σ.1
end ConnesGreen
theorem solution
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (hμ : canonicalCertificateThreshold t ht S ≠ 0) :
    (∃ x : Physical t, x ≠ 0 ∧ x ∈ canonicalMaximizingSpace t ht S ∧
      ∀ ρ : CriticalZeros, ρ ∉ F →
        ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) ↔
    (∃ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
      canonicalFiniteColumnKernel t S F *ᵥ c ≠ 0 ∧
      canonicalFiniteIntegralCertificate t S F (canonicalCertificateThreshold t ht S) *ᵥ c = 0 ∧
      ∀ ρ : CriticalZeros, ρ ∉ F →
        (∑ j, (Sum.elim
          (fun σ : {σ : CriticalZeros // σ ∈ F} => canonicalPairGramKernel t 1 1 ρ σ.1)
          (fun σ : {σ : CriticalZeros // σ ∈ S} => canonicalPairGramKernel t 1 (-1) ρ σ.1) j) * c j) = 0) := by
  constructor
  · rintro ⟨x, hn, hx, hc⟩
    have hspan := canonical_maximizer_mem_finite_actor_span t ht S F hμ x hx hc
    have hspan' : x ∈ Submodule.span ℂ (Set.range (canonicalFiniteActorFamily t S F)) := by
      apply Submodule.span_mono ?_ hspan
      rintro y (⟨ρ, rfl⟩ | ⟨ρ, rfl⟩)
      · exact ⟨Sum.inr ρ, rfl⟩
      · exact ⟨Sum.inl ρ, rfl⟩
    obtain ⟨c, he⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).mp hspan'
    refine ⟨c, (canonical_finite_actor_sum_ne_zero_iff t ht S F c).mp (by rwa [he]), ?_, ?_⟩
    · apply (canonical_integral_certificate_kernel_iff t ht S F _ c).mpr
      rw [he]
      exact (canonical_sampled_operator_kernel_iff_maximizing t ht S F x hc).mpr hx
    · intro ρ hρ
      have h := hc ρ hρ
      rw [← he] at h
      rw [← canonical_positive_sampling_row_eq_integral t ht S F ρ c]
      simpa only [inner_sum, inner_smul_right, mul_comm] using h
  · rintro ⟨c, hn, hk, hc⟩
    let x := ∑ j, c j • canonicalFiniteActorFamily t S F j
    have hcx : ∀ ρ : CriticalZeros, ρ ∉ F →
        ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0 := by
      intro ρ hρ
      have h := hc ρ hρ
      rw [← canonical_positive_sampling_row_eq_integral t ht S F ρ c] at h
      simpa only [x, inner_sum, inner_smul_right, mul_comm] using h
    refine ⟨x, (canonical_finite_actor_sum_ne_zero_iff t ht S F c).mpr hn, ?_, hcx⟩
    apply (canonical_sampled_operator_kernel_iff_maximizing t ht S F x hcx).mp
    exact (canonical_integral_certificate_kernel_iff t ht S F _ c).mp hk
