-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.exists_prim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:21.421575+00:00
-- url     : https://prove2.me/submissions/d7f7f46a-994e-4197-a7d7-fd4a3bea04f9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.BallB
theorem _root_.solution {J : Type*} [Finite J] (a : J → K) {j₀ : J} (ha : a j₀ ≠ 0) {P : Ideal (𝓞 K)}
    (hP : P ≠ ⊤) :
    ∃ (t : K) (c : J → 𝓞 K), (∀ j, algebraMap (𝓞 K) K (c j) = t * a j) ∧ ∃ j, c j ∉ P := by
  obtain ⟨N, hN⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) a
  choose e he using hN
  have hN0 : algebraMap (𝓞 K) K (N : 𝓞 K) ≠ 0 := by
    rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    exact nonZeroDivisors.coe_ne_zero N
  have he' : ∀ j, algebraMap (𝓞 K) K (e j) = algebraMap (𝓞 K) K (N : 𝓞 K) * a j := by
    intro j
    rw [he j, Algebra.smul_def]
  have hβ : e j₀ ≠ 0 := by
    intro h0
    have := he' j₀
    rw [h0, map_zero] at this
    exact (mul_ne_zero hN0 ha) this.symm
  have hβK : algebraMap (𝓞 K) K (e j₀) ≠ 0 := by
    rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  obtain ⟨C, hC⟩ : Ideal.span (Set.range e) ∣ Ideal.span {e j₀} :=
    Ideal.dvd_iff_le.2 (Ideal.span_le.2 (by
      rintro _ rfl
      exact Ideal.subset_span ⟨j₀, rfl⟩))
  have hex : ∃ γ ∈ C, ∃ j, γ * e j ∉ P * Ideal.span {e j₀} := by
    by_contra hcon
    push Not at hcon
    have hle : Ideal.span {e j₀} ≤ P * Ideal.span {e j₀} := by
      conv_lhs => rw [hC]
      rw [mul_comm, Ideal.mul_le]
      intro γ hγ r hr
      induction hr using Submodule.span_induction with
      | mem r hr => obtain ⟨j, rfl⟩ := hr; exact hcon γ hγ j
      | zero => rw [mul_zero]; exact Ideal.zero_mem _
      | add r s _ _ hr hs => rw [mul_add]; exact Ideal.add_mem _ hr hs
      | smul c r _ hr => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hr
    have heq : P * Ideal.span {e j₀} = 1 * Ideal.span {e j₀} := by
      rw [one_mul]; exact le_antisymm Ideal.mul_le_right hle
    have hs0 : Ideal.span {e j₀} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hβ
    exact hP (by rw [mul_right_cancel₀ hs0 heq, Ideal.one_eq_top])
  obtain ⟨γ, hγ, j₁, hj₁⟩ := hex
  have hmem : ∀ j, γ * e j ∈ Ideal.span {e j₀} := by
    intro j
    rw [hC, mul_comm γ]
    exact Ideal.mul_mem_mul (Ideal.subset_span ⟨j, rfl⟩) hγ
  choose c hc using fun j => Ideal.mem_span_singleton'.1 (hmem j)
  refine ⟨algebraMap (𝓞 K) K γ * algebraMap (𝓞 K) K (N : 𝓞 K) / algebraMap (𝓞 K) K (e j₀), c,
    fun j => ?_, j₁, fun hcP => hj₁ ?_⟩
  · have := congrArg (algebraMap (𝓞 K) K) (hc j)
    rw [map_mul, map_mul, he' j] at this
    field_simp
    rw [this]; ring
  · rw [← hc j₁]
    exact Ideal.mul_mem_mul hcP (Ideal.mem_span_singleton_self _)
end Formalism.HermitianLattices.Ext.L3.BallB
