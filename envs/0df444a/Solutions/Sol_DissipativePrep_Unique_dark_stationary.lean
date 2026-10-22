-- Prove2me | solution 1 for DissipativePrep.Unique.dark_stationary
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T22:42:57.370119+00:00
-- url     : https://prove2.me/submissions/39595a88-bf49-42c3-9f6b-290d84d3eedd

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16 DissipativePrep.Unique

namespace DPdsAux

lemma gen_zero {d m : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (c : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → ℝ) (E : ℝ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρᴴ = ρ) (hc : ∀ l, c l * ρ = 0)
    (hHρ : H * ρ = (E : ℂ) • ρ) :
    gkslGenerator (krausData H hH c g) ρ = 0 := by
  have hV : ∀ l, (krausData H hH c g).jump l * ρ = 0 := by
    show ∀ l : Fin m, (((Real.sqrt (2 * g l) : ℝ) : ℂ) • c l) * ρ = 0
    intro l
    rw [Matrix.smul_mul, hc l, smul_zero]
  have hK : driftK (krausData H hH c g) * ρ = (Complex.I * E) • ρ := by
    simp only [driftK, Matrix.add_mul, Matrix.smul_mul, Matrix.sum_mul, Matrix.mul_assoc, hV,
      Matrix.mul_zero, Finset.sum_const_zero, smul_zero, add_zero]
    show Complex.I • (H * ρ) = _
    rw [hHρ, smul_smul]
  have hK' : ρ * (driftK (krausData H hH c g))ᴴ = (-(Complex.I * E)) • ρ := by
    have : ρ * (driftK (krausData H hH c g))ᴴ = (driftK (krausData H hH c g) * ρ)ᴴ := by
      rw [Matrix.conjTranspose_mul, hρ]
    rw [this, hK, Matrix.conjTranspose_smul, hρ]
    congr 1
    simp [Complex.ext_iff]
  simp only [gkslGenerator, cpGenerator, sandwich, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  rw [hK, hK']
  have : ∀ k, (krausData H hH c g).jump k * (ρ * ((krausData H hH c g).jump k)ᴴ) = 0 := by
    intro k; rw [← Matrix.mul_assoc, hV, Matrix.zero_mul]
  simp only [this, Finset.sum_const_zero]
  rw [neg_smul]; abel

end DPdsAux

open DPdsAux

theorem solution {d m : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (c : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → ℝ) (hg : ∀ l, 0 < g l) (E : ℝ) :
    (∀ ψ ∈ darkSpace H c E, gkslGenerator (krausData H hH c g) (pureDensity ψ) = 0) ∧
    ∀ ρ : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix ρ → densitySupport ρ ≤ darkSpace H c E →
      stationary (krausData H hH c g) ρ := by
  have memD : ∀ ψ ∈ darkSpace H c E, (∀ l, c l *ᵥ WithLp.ofLp ψ = 0) ∧
      H *ᵥ WithLp.ofLp ψ = (E : ℂ) • WithLp.ofLp ψ := by
    intro ψ hψ
    simp only [darkSpace, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hψ
    refine ⟨fun l => ?_, ?_⟩
    · have := congrArg WithLp.ofLp (hψ.1 l)
      simpa using this
    · have h2 : Matrix.toEuclideanLin H ψ = (E : ℂ) • ψ := sub_eq_zero.mp hψ.2
      have := congrArg WithLp.ofLp h2
      simpa using this
  refine ⟨fun ψ hψ => ?_, fun ρ hρ hsupp => ?_⟩
  · obtain ⟨hc, hHψ⟩ := memD ψ hψ
    apply gen_zero H hH c g E
    · ext i j; simp [pureDensity, mul_comm]
    · intro l; ext i j
      have := congrFun (hc l) i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      simp only [pureDensity, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
      calc ∑ k, c l i k * (ψ k * conj (ψ j)) = (∑ k, c l i k * ψ k) * conj (ψ j) := by
            rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => by ring
        _ = 0 := by rw [this, zero_mul]
    · ext i j
      have := congrFun hHψ i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      simp only [pureDensity, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      calc ∑ k, H i k * (ψ k * conj (ψ j)) = (∑ k, H i k * ψ k) * conj (ψ j) := by
            rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => by ring
        _ = _ := by rw [this]; ring
  · refine ⟨hρ, ?_⟩
    have hcol : ∀ v : Fin d → ℂ, (∀ l, c l *ᵥ (ρ *ᵥ v) = 0) ∧
        H *ᵥ (ρ *ᵥ v) = (E : ℂ) • (ρ *ᵥ v) := by
      intro v
      have hmem : Matrix.toEuclideanLin ρ (WithLp.toLp 2 v) ∈ darkSpace H c E :=
        hsupp ⟨_, rfl⟩
      exact memD _ hmem
    apply gen_zero H hH c g E
    · exact hρ.1.isHermitian
    · intro l
      ext i j
      have := congrFun ((hcol (Pi.single j 1)).1 l) i
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
      simpa using this
    · ext i j
      have := congrFun (hcol (Pi.single j 1)).2 i
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
      simpa using this
