-- Prove2me | solution 1 for ConnesGreen.canonical_gram_null_sampling_custody
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T18:17:53.99209+00:00
-- url     : https://prove2.me/submissions/f76fc63b-1ba8-409d-809c-615efa4c34c4

import Definitions.Def_ConnesGreen_integral_sampling_row
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

import Theorems.Thm_ConnesGreen_canonical_source_gram_eq_green_integral
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability
set_option backward.isDefEq.respectTransparency.types false
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
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros) (δ : ℝ) :
    (LinearMap.ker (canonicalFiniteColumnKernel t S F).mulVecLin ≤
      LinearMap.ker (canonicalFiniteIntegralCertificate t S F δ).mulVecLin) ∧
    (∀ (ρ : CriticalZeros)
      (c : ({σ : CriticalZeros // σ ∈ F} ⊕ {σ : CriticalZeros // σ ∈ S}) → ℂ),
      canonicalFiniteColumnKernel t S F *ᵥ c = 0 →
      canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) := by
  constructor
  · intro c hc
    change canonicalFiniteIntegralCertificate t S F δ *ᵥ c = 0
    change canonicalFiniteColumnKernel t S F *ᵥ c = 0 at hc
    simp only [canonicalFiniteIntegralCertificate, Matrix.add_mulVec,
      Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero, smul_zero, add_zero]
  · intro ρ c hc
    have hx : (∑ j, c j • canonicalFiniteActorFamily t S F j) = 0 := by
      by_contra hn
      exact ((canonical_finite_actor_sum_ne_zero_iff t ht S F c).mp hn) hc
    have he := congrArg
      (fun x => ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ) hx
    change (∑ j, canonicalIntegralSamplingRow t S F ρ j * c j) = 0
    simp only [canonicalIntegralSamplingRow]
    rw [← canonical_positive_sampling_row_eq_integral t ht S F ρ c]
    simpa only [inner_sum, inner_smul_right, inner_zero_right, mul_comm] using he
