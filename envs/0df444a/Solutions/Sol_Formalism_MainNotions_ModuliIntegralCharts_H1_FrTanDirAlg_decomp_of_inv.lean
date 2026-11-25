-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg.decomp_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:20:41.470881+00:00
-- url     : https://prove2.me/submissions/ec92f6a9-e842-4846-a3b2-a34213ae79fa

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanDirAlg
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrTanDirAlg_hom_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
open NumberField Matrix
variable {E : Type} [Field E] [NumberField E] {κ : Type} [Fintype κ]
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {ι : Type} [Fintype ι] [DecidableEq ι]
  [DecidableEq κ]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
theorem _root_.solution (ρ : 𝓞 E →+* Module.End R M) (χ : ι → (𝓞 E →+* R)) (b : Module.Basis κ ℤ (𝓞 E))
    (Cm : κ → ι → R) (hAC : ∀ σ τ, ∑ i, χ σ (b i) * Cm i τ = if σ = τ then 1 else 0)
    (hCA : ∀ i j, ∑ τ, Cm i τ * χ τ (b j) = if i = j then 1 else 0) :
    (∀ m : M, ∃ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ a • mσ σ) ∧ ∑ σ, mσ σ = m) ∧
    (∀ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ a • mσ σ) → ∑ σ, mσ σ = 0 → ∀ σ, mσ σ = 0) := by
  classical
  set Q : ι → M → M := fun σ m => ∑ i, Cm i σ • ρ (b i) m with hQ
  have hcoef : ∀ (a : 𝓞 E) (i : κ), ∑ τ, χ τ a * Cm i τ = ((b.repr a i : ℤ) : R) := by
    intro a i
    have h1 : ∀ τ, χ τ a = ∑ k, ((b.repr a k : ℤ) : R) * χ τ (b k) := fun τ => hom_basis (χ τ) b a
    have hCA' : ∀ k, ∑ τ, χ τ (b k) * Cm i τ = if i = k then 1 else 0 := by
      intro k
      rw [← hCA i k]
      exact Finset.sum_congr rfl fun τ _ => mul_comm _ _
    simp_rw [h1, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, hCA']
    simp
  have F3 : ∀ (a : 𝓞 E) (m : M), ρ a m = ∑ τ, χ τ a • Q τ m := by
    intro a m
    simp only [hQ, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hcoef]
    conv_lhs => rw [hom_basis ρ b a]
    simp [Module.End.mul_apply, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]
  have eig : ∀ σ (a : 𝓞 E) (m : M), ρ a (Q σ m) = χ σ a • Q σ m := by
    intro σ a m
    have h1 : ρ a (Q σ m) = ∑ i, Cm i σ • ρ (a * b i) m := by
      simp only [hQ, map_sum, map_smul, map_mul, Module.End.mul_apply]
    rw [h1]
    simp_rw [F3 _ m, map_mul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have h2 : ∀ τ, ∑ i, Cm i σ * (χ τ a * χ τ (b i)) = χ τ a * (if τ = σ then 1 else 0) := by
      intro τ
      rw [← hAC τ σ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [h2]
    simp
  have hsum1 : ∀ m : M, ∑ σ, Q σ m = m := by
    intro m
    have := F3 1 m
    simp at this
    exact this.symm
  have hlin : ∀ σ (f : ι → M), Q σ (∑ σ', f σ') = ∑ σ', Q σ (f σ') := by
    intro σ f
    simp only [hQ, map_sum, Finset.smul_sum]
    exact Finset.sum_comm
  refine ⟨fun m => ⟨fun σ => Q σ m, fun σ a => eig σ a m, hsum1 m⟩, ?_⟩
  intro mσ hmσ hsum σ
  have hQe : ∀ τ σ', Q τ (mσ σ') = if σ' = τ then mσ σ' else 0 := by
    intro τ σ'
    simp only [hQ, hmσ, smul_smul]
    rw [← Finset.sum_smul]
    rw [show ∑ i, Cm i τ * χ σ' (b i) = if σ' = τ then 1 else 0 from by
      rw [← hAC σ' τ]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _]
    split_ifs <;> simp
  have h0 : Q σ (∑ σ', mσ σ') = 0 := by
    rw [hsum]
    simp [hQ]
  rw [hlin] at h0
  simpa [hQe] using h0
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
