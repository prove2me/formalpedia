-- Prove2me | solution 1 for DedekindZeta.exists_orbitIdeal_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:28:09.572707+00:00
-- url     : https://prove2.me/submissions/6407d4be-6d71-4512-8126-cc09fb7ee039

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_mixedEmbedding_norm_eq_absNorm_span_local
import Theorems.Thm_DedekindZeta_orbitIdeal_fibre_aux
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal
namespace DedekindZeta
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) {t : ℂ} :
    ∃ ψ : Quotient (MulAction.orbitRel
          (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
          {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}) → NonzeroIdeal K,
      (∀ o, mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1) ^ (-t.re)
          = mixedEmbedding.norm (mixedEmbedding K ((I.den : 𝓞 K) : K)) ^ t.re
            * (Ideal.absNorm ((ψ o : NonzeroIdeal K) : Ideal (𝓞 K)) : ℝ) ^ (-t.re))
      ∧ (∀ J : NonzeroIdeal K, Finite {o // ψ o = J})
      ∧ (∀ J : NonzeroIdeal K,
          Nat.card {o // ψ o = J} ≤ NumberField.Units.torsionOrder K) := by
  classical
  -- `d := (I.den : 𝓞 K)` is nonzero, so clearing denominators is faithful.
  have hd_ne : ((I.den : 𝓞 K) : K) ≠ 0 :=
    RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.coe_ne_zero I.den)
  -- Clearing denominators: every nonzero `a ∈ I` has `d·a` integral
  -- (`FractionalIdeal.den_mul_self_eq_num`).
  have hden : ∀ a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0},
      ∃ b : 𝓞 K, (b : K) = ((I.den : 𝓞 K) : K) * a.1 := by
    intro a
    have hmem : I.den • a.1 ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num := by
      rw [← I.den_mul_self_eq_num]
      exact Submodule.smul_mem_pointwise_smul a.1 I.den _ a.2.1
    obtain ⟨b, -, hbeq⟩ := hmem
    refine ⟨b, ?_⟩
    rw [Algebra.linearMap_apply] at hbeq
    rw [show ((b : 𝓞 K) : K) = algebraMap (𝓞 K) K b from rfl, hbeq]
    simp [Submonoid.smul_def, Algebra.smul_def]
  choose bfun hbfun using hden
  -- The representatives are nonzero (`d ≠ 0`, `a ≠ 0`).
  have hbfun_ne : ∀ a, bfun a ≠ 0 := by
    intro a hzero
    have h := hbfun a
    rw [hzero, RingOfIntegers.coe_eq_algebraMap, map_zero] at h
    exact mul_ne_zero hd_ne a.2.2 h.symm
  -- The orbit-indexed principal ideal `ψ o = (bfun (out o))`.
  have hψ_ne : ∀ o : Quotient (MulAction.orbitRel
        (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
        {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}),
      Ideal.span {bfun (Quotient.out o)} ≠ 0 := by
    intro o
    simpa [Ideal.span_singleton_eq_bot] using hbfun_ne (Quotient.out o)
  let ψ : Quotient (MulAction.orbitRel
        (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
        {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}) → NonzeroIdeal K :=
    fun o => ⟨Ideal.span {bfun (Quotient.out o)}, hψ_ne o⟩
  have hψval : ∀ o, ((ψ o : NonzeroIdeal K) : Ideal (𝓞 K))
      = Ideal.span {bfun (Quotient.out o)} := fun _ => rfl
  refine ⟨ψ, ?_, ?_, ?_⟩
  · -- Norm identity.
    intro o
    -- `𝔑((bfun (out o))) = N(σ d) · N(σ a₀)`.
    have key : (Ideal.absNorm (Ideal.span {bfun (Quotient.out o)}) : ℝ)
        = mixedEmbedding.norm (mixedEmbedding K ((I.den : 𝓞 K) : K))
          * mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1) := by
      rw [← mixedEmbedding_norm_eq_absNorm_span_local (bfun (Quotient.out o)),
        hbfun (Quotient.out o)]
      simp only [mixedEmbedding.norm_eq_norm, map_mul]
    have hNd_nonneg : 0 ≤ mixedEmbedding.norm (mixedEmbedding K ((I.den : 𝓞 K) : K)) := by
      rw [mixedEmbedding.norm_eq_norm]; positivity
    have hNd0 : mixedEmbedding.norm (mixedEmbedding K ((I.den : 𝓞 K) : K)) ≠ 0 := by
      rw [mixedEmbedding.norm_eq_norm]
      exact_mod_cast abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hd_ne)
    have hNb_nonneg : (0 : ℝ)
        ≤ (Ideal.absNorm (Ideal.span {bfun (Quotient.out o)}) : ℝ) := Nat.cast_nonneg _
    have hNa : mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1)
        = (Ideal.absNorm (Ideal.span {bfun (Quotient.out o)}) : ℝ)
          * (mixedEmbedding.norm (mixedEmbedding K ((I.den : 𝓞 K) : K)))⁻¹ := by
      rw [key, mul_comm (mixedEmbedding.norm (mixedEmbedding K ((I.den : 𝓞 K) : K)))
          (mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1)),
        mul_assoc, mul_inv_cancel₀ hNd0, mul_one]
    rw [hψval, hNa, Real.mul_rpow hNb_nonneg (inv_nonneg.mpr hNd_nonneg),
      Real.inv_rpow hNd_nonneg, Real.rpow_neg hNd_nonneg, inv_inv, mul_comm]
  · -- Finite fibres: derived from the bounded-fibre injection below.
    intro J
    exact (orbitIdeal_fibre_aux K I bfun hbfun hd_ne ψ hψval J).1
  · -- Fibre cardinality bound `≤ w_K`.
    intro J
    exact (orbitIdeal_fibre_aux K I bfun hbfun hd_ne ψ hψval J).2
end DedekindZeta
