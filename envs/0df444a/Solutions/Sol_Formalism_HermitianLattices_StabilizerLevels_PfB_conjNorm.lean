-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.conjNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:29:09.829717+00:00
-- url     : https://prove2.me/submissions/e73f3fda-dae7-4ee3-b0c5-9e4c47782c0c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
import Theorems.Thm_Formalism_HermitianLattices_StabilizerLevels_PfB_quadNorm
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_key
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IntermediateField Ideal IsDedekindDomain nonZeroDivisors
open scoped Pointwise
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution (K : IntermediateField ℚ E) (hK : Module.finrank ℚ K = 2) (σ : E ≃ₐ[ℚ] E) (β : K)
    (hβ : σ (β : E) ≠ β) (𝔠 : Ideal (𝓞 K)) (h𝔠 : 𝔠 ≠ ⊥) :
    𝔠.map (algebraMap (𝓞 K) (𝓞 E)) * σ • (𝔠.map (algebraMap (𝓞 K) (𝓞 E))) =
      Ideal.span {((Ideal.absNorm 𝔠 : ℕ) : 𝓞 E)} := by
  have hnormE : ∀ z : 𝓞 K, (((Algebra.norm ℤ z : ℤ)) : E) = ((z : K) : E) * σ ((z : K) : E) := by
    intro z
    rw [← quadNorm K hK σ β hβ (z : K), ← Algebra.coe_norm_int z]
    push_cast; rfl
  have hnorm : ∀ z : 𝓞 K, (((Algebra.norm ℤ z : ℤ)) : 𝓞 E) =
      algebraMap (𝓞 K) (𝓞 E) z * σ • algebraMap (𝓞 K) (𝓞 E) z := by
    intro z
    apply RingOfIntegers.ext
    have := hnormE z
    show algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _
    rw [map_intCast, map_mul]
    exact this
  have hN0 : ((Ideal.absNorm 𝔠 : ℕ) : E) ≠ 0 := by
    have : Ideal.absNorm 𝔠 ≠ 0 := by rwa [ne_eq, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast this
  apply le_antisymm
  · have key : ∀ x ∈ 𝔠, ∀ y ∈ 𝔠, algebraMap (𝓞 K) (𝓞 E) x * σ • algebraMap (𝓞 K) (𝓞 E) y ∈
        Ideal.span {((Ideal.absNorm 𝔠 : ℕ) : 𝓞 E)} := by
      intro x hx y hy
      obtain ⟨kx, hkx⟩ := Ideal.absNorm_dvd_norm_of_mem hx
      obtain ⟨ky, hky⟩ := Ideal.absNorm_dvd_norm_of_mem hy
      obtain ⟨kxy, hkxy⟩ := Ideal.absNorm_dvd_norm_of_mem (𝔠.add_mem hx hy)
      have ex := hnormE x
      have ey := hnormE y
      have exy := hnormE (x + y)
      rw [hkx] at ex
      rw [hky] at ey
      rw [hkxy] at exy
      push_cast at ex ey exy
      rw [map_add] at exy
      obtain ⟨X, hX⟩ : ∃ X : E, X = ((x : K) : E) := ⟨_, rfl⟩
      obtain ⟨Y, hY⟩ : ∃ Y : E, Y = ((y : K) : E) := ⟨_, rfl⟩
      obtain ⟨X', hX'⟩ : ∃ X' : E, X' = σ ((x : K) : E) := ⟨_, rfl⟩
      obtain ⟨Y', hY'⟩ : ∃ Y' : E, Y' = σ ((y : K) : E) := ⟨_, rfl⟩
      obtain ⟨N, hN⟩ : ∃ N : E, N = ((Ideal.absNorm 𝔠 : ℕ) : E) := ⟨_, rfl⟩
      rw [← hX', ← hX, ← hN] at ex
      rw [← hY', ← hY, ← hN] at ey
      rw [← hX', ← hY', ← hX, ← hY, ← hN] at exy
      rw [← hN] at hN0
      have hkx' : (kx : E) = X * X' / N := by field_simp; linear_combination ex
      have hky' : (ky : E) = Y * Y' / N := by field_simp; linear_combination ey
      have hkxy' : (kxy : E) = (X + Y) * (X' + Y') / N := by field_simp; linear_combination exy
      have hint : IsIntegral ℤ (X * Y' / N) := by
        obtain ⟨T, hT⟩ : ∃ T : ℤ, T = kxy - kx - ky := ⟨_, rfl⟩
        obtain ⟨M, hM⟩ : ∃ M : ℤ, M = kx * ky := ⟨_, rfl⟩
        refine ⟨Polynomial.X ^ 2 - Polynomial.C T * Polynomial.X + Polynomial.C M, by monicity!, ?_⟩
        simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C]
        simp only [eq_intCast]
        rw [hT, hM]
        push_cast
        rw [hkx', hky', hkxy']
        field_simp
        ring
      rw [Ideal.mem_span_singleton']
      obtain ⟨w, hw⟩ : ∃ w : 𝓞 E, algebraMap (𝓞 E) E w = X * Y' / N := ⟨⟨_, hint⟩, rfl⟩
      refine ⟨w, ?_⟩
      apply RingOfIntegers.ext
      show algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _
      rw [map_mul, map_mul, map_natCast, hw]
      show X * Y' / N * ((Ideal.absNorm 𝔠 : ℕ) : E) = ((x : K) : E) * σ ((y : K) : E)
      rw [← hN, ← hX, ← hY']
      field_simp
    rw [Ideal.pointwise_smul_def, Ideal.map_map, Ideal.map, Ideal.map, Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact key x hx y hy
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    let J : Ideal ℤ := Ideal.comap (algebraMap ℤ (𝓞 E))
      (𝔠.map (algebraMap (𝓞 K) (𝓞 E)) * σ • (𝔠.map (algebraMap (𝓞 K) (𝓞 E))))
    have hJ : Ideal.relNorm ℤ 𝔠 ≤ J := by
      rw [Ideal.relNorm_apply, Ideal.span_le]
      rintro _ ⟨z, hz, rfl⟩
      refine Ideal.mem_comap.2 ?_
      rw [Algebra.intNorm_eq_norm, eq_intCast, hnorm]
      exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hz)
        (Ideal.smul_mem_pointwise_smul _ _ _ (Ideal.mem_map_of_mem _ hz))
    rw [Ideal.relNorm_int] at hJ
    have := hJ (Ideal.mem_span_singleton_self _)
    have h2 : algebraMap ℤ (𝓞 E) ((Ideal.absNorm 𝔠 : ℕ) : ℤ) ∈
      (𝔠.map (algebraMap (𝓞 K) (𝓞 E)) * σ • (𝔠.map (algebraMap (𝓞 K) (𝓞 E)))) := this
    simpa using h2
end Formalism.HermitianLattices.StabilizerLevels.PfB
