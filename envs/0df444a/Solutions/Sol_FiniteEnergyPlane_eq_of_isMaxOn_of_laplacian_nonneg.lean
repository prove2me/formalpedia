-- Prove2me | solution 1 for FiniteEnergyPlane.eq_of_isMaxOn_of_laplacian_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-26T17:32:27.045043+00:00
-- url     : https://prove2.me/submissions/4c7959fb-731d-49de-9c6c-fef169993e13

import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Complex.Basic
import Theorems.Thm_HunterPDE_Harmonic_strong_maximum_principle

open Laplacian

namespace FiniteEnergyPlane

theorem amp_laplacian_comp_symm (f : ℂ → ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    Δ (f ∘ Complex.orthonormalBasisOneI.repr.symm) x =
      Δ f (Complex.orthonormalBasisOneI.repr.symm x) := by
  set L : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr with hL
  set b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
    Complex.orthonormalBasisOneI.map L with hb
  have h1 := InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (f ∘ L.symm) b
  have h2 := InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    Complex.orthonormalBasisOneI
  rw [h1, h2]
  simp only
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hc := ContinuousLinearEquiv.iteratedFDerivWithin_comp_right
    (L.symm.toContinuousLinearEquiv) f (s := Set.univ) uniqueDiffOn_univ
    (x := x) (Set.mem_univ _) 2
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at hc
  have hfun : f ∘ L.symm = f ∘ (L.symm.toContinuousLinearEquiv : _ → ℂ) := rfl
  rw [hfun, hc]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  ext j
  fin_cases j <;> simp [hb]

/-- Strong maximum principle on `ℂ` (Mathlib's Laplacian). -/
theorem eq_of_isMaxOn_of_laplacian_nonneg_aux {Ω : Set ℂ} {f : ℂ → ℝ} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) (hf : ContDiffOn ℝ 2 f Ω) (hΔ : ∀ z ∈ Ω, 0 ≤ Δ f z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hmax : ∀ z ∈ Ω, f z ≤ f z₀) :
    ∀ z ∈ Ω, f z = f z₀ := by
  set L : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr with hL
  set Ω' : Set (EuclideanSpace ℝ (Fin 2)) := L.symm ⁻¹' Ω with hΩ'
  set g : EuclideanSpace ℝ (Fin 2) → ℝ := f ∘ L.symm with hg
  have hΩ'o : IsOpen Ω' := hΩ.preimage L.symm.continuous
  have hΩ'c : IsPreconnected Ω' := by
    have : Ω' = L.toHomeomorph '' Ω := by
      ext x; simp only [hΩ', Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx; exact ⟨L.symm x, hx, by simp⟩
      · rintro ⟨z, hz, rfl⟩; simpa using hz
    rw [this]; exact hconn.image _ L.toHomeomorph.continuous.continuousOn
  have hsub : HunterPDE.Harmonic.IsSubharmonicOn Ω' g := by
    refine ⟨?_, ?_⟩
    · exact hf.comp L.symm.contDiff.contDiffOn (fun x hx => hx)
    · intro x hx
      rw [hg, amp_laplacian_comp_symm]
      exact hΔ _ hx
  have hx₀ : L z₀ ∈ Ω' := by simpa [hΩ'] using hz₀
  obtain ⟨c, hc⟩ := HunterPDE.Harmonic.strong_maximum_principle hΩ'o hΩ'c hsub
    ⟨L z₀, hx₀, fun x hx => by simpa [hg] using hmax _ hx⟩
  have key : ∀ z ∈ Ω, f z = c := by
    intro z hz
    have := hc (L z) (by simpa [hΩ'] using hz)
    simpa [hg] using this
  intro z hz
  rw [key z hz, key z₀ hz₀]

end FiniteEnergyPlane

open FiniteEnergyPlane

open Laplacian

theorem solution {Ω : Set ℂ} {f : ℂ → ℝ} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) (hf : ContDiffOn ℝ 2 f Ω) (hΔ : ∀ z ∈ Ω, 0 ≤ Δ f z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hmax : ∀ z ∈ Ω, f z ≤ f z₀) :
    ∀ z ∈ Ω, f z = f z₀ :=
  eq_of_isMaxOn_of_laplacian_nonneg_aux hΩ hconn hf hΔ hz₀ hmax
