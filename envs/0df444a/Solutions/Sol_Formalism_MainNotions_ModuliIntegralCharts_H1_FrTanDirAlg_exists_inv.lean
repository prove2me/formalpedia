-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg.exists_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:20:47.796388+00:00
-- url     : https://prove2.me/submissions/548767ad-4850-4800-a531-6d66bfa86c3b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanDirAlg
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrTanDirAlg_not_dvd_discr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrTanDirAlg_isUnit_of_not_dvd

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
variable (E : Type) [Field E] [NumberField E]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
theorem _root_.solution {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {Fr : Type} [Field Fr] [Algebra V Fr]
    [DecidableEq (E →+* ℂ)] (hinj : Function.Injective (algebraMap V Fr)) {F : Type} [Field F] (j : F →+* ℂ)
    (io : F →+* Fr)
    (φ : (E →+* ℂ) → (E →+* F)) (hφ : ∀ σ x, j (φ σ x) = σ x)
    (χ : (E →+* ℂ) → (𝓞 E →+* V)) (hχ : ∀ σ (a : 𝓞 E), algebraMap V Fr (χ σ a) = io (φ σ (a : E)))
    (g : ℕ) (hg : g.Prime) (hgV : ¬ IsUnit (g : V))
    (hnd : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup) :
    ∃ Cm : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (E →+* ℂ) → V,
      (∀ σ τ, ∑ i, χ σ (RingOfIntegers.basis E i) * Cm i τ = if σ = τ then 1 else 0) ∧
      (∀ i i', ∑ τ, Cm i τ * χ τ (RingOfIntegers.basis E i') = if i = i' then 1 else 0) := by
  classical

  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card (E →+* ℂ) := by
    rw [NumberField.Embeddings.card, ← NumberField.RingOfIntegers.rank E,
      Module.finrank_eq_card_chooseBasisIndex]
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →+* ℂ) := Fintype.equivOfCardEq hcard
  let B' : Matrix (E →+* ℂ) (E →+* ℂ) V := Matrix.of fun σ τ => χ σ (RingOfIntegers.basis E (e.symm τ))
  let Φ : Matrix (E →+* ℂ) (E →+* ℂ) F :=
    Matrix.of fun σ τ => φ σ ((RingOfIntegers.basis E (e.symm τ) : 𝓞 E) : E)
  let M : Matrix (E →+* ℂ) (E →+* ℂ) ℂ :=
    Matrix.of fun σ τ => σ ((RingOfIntegers.basis E (e.symm τ) : 𝓞 E) : E)

  have hM : (M.det) ^ 2 = ((discr E : ℤ) : ℂ) := by
    let e₂ : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] ℂ) := e.trans (RingHom.equivRatAlgHom E ℂ)
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (integralBasis E) e₂
    rw [← NumberField.coe_discr] at h1
    have hN : Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis E) e₂ = (M.submatrix e e)ᵀ := by
      ext a b
      simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, M, e₂,
        NumberField.integralBasis_apply]
    rw [hN, Matrix.det_transpose, Matrix.det_submatrix_equiv_self] at h1
    rw [← h1]
    simp
  have hΦ : (Φ.det) ^ 2 = ((discr E : ℤ) : F) := by
    apply j.injective
    rw [map_pow, RingHom.map_det, map_intCast, ← hM]
    congr 2
    ext σ τ
    simp [Φ, M, hφ]
  have hsq : B'.det ^ 2 = ((discr E : ℤ) : V) := by
    apply hinj
    rw [map_pow, RingHom.map_det, map_intCast]
    have hB : (algebraMap V Fr).mapMatrix B' = io.mapMatrix Φ := by
      ext σ τ
      simp [B', Φ, hχ]
    rw [hB, ← RingHom.map_det, ← map_pow, hΦ, map_intCast]
  have hu : IsUnit ((discr E : ℤ) : V) := isUnit_of_not_dvd g hg hgV _ (not_dvd_discr E g hg hnd)
  have hdet : IsUnit B'.det := (isUnit_pow_iff two_ne_zero).mp (hsq ▸ hu)
  refine ⟨fun i τ => B'⁻¹ (e i) τ, fun σ τ => ?_, fun i i' => ?_⟩
  · calc ∑ i, χ σ (RingOfIntegers.basis E i) * B'⁻¹ (e i) τ = ∑ i, B' σ (e i) * B'⁻¹ (e i) τ := by
          simp [B']
      _ = ∑ τ', B' σ τ' * B'⁻¹ τ' τ := Equiv.sum_comp e (fun τ' => B' σ τ' * B'⁻¹ τ' τ)
      _ = (B' * B'⁻¹) σ τ := (Matrix.mul_apply).symm
      _ = if σ = τ then 1 else 0 := by rw [Matrix.mul_nonsing_inv B' hdet, Matrix.one_apply]
  · calc ∑ τ, B'⁻¹ (e i) τ * χ τ (RingOfIntegers.basis E i') = ∑ τ, B'⁻¹ (e i) τ * B' τ (e i') := by
          simp [B']
      _ = (B'⁻¹ * B') (e i) (e i') := (Matrix.mul_apply).symm
      _ = if i = i' then 1 else 0 := by
          rw [Matrix.nonsing_inv_mul B' hdet, Matrix.one_apply]
          simp [e.injective.eq_iff]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
