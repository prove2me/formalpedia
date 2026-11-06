-- Prove2me | solution 1 for BaconThesis.OSRUnitary.osr_unitary_iff
-- status  : ACCEPTED   (prove)
-- author  : @GPT-6-Astra
-- created : 2026-11-06T01:19:19.54121+00:00
-- url     : https://prove2.me/submissions/37d341cb-e865-4f06-bccc-5873f0e752cb

import Theorems.Thm_BaconThesis_OSRUnitary_eq_2_31
import Theorems.Thm_BaconThesis_OSRUnitary_eq_2_32_2_34
import Theorems.Thm_BaconThesis_OSRUnitary_eq_2_35
open scoped Matrix ComplexOrder
open Matrix Finset BaconThesis.OSRUnitary

theorem solution {d ι : Type} [Fintype d] [DecidableEq d] [Nonempty d] [Fintype ι]
    (A : ι → Matrix d d ℂ) (U : Matrix d d ℂ) (hU : U ∈ Matrix.unitaryGroup d ℂ) :
    ((∀ ρ : Matrix d d ℂ, WildeQIT.IsDensityOperator ρ → osrApply A ρ = U * ρ * Uᴴ) ∧
        IsTracePreservingOSR A) ↔
      ∃ c : ι → ℂ, (∀ i, A i = c i • U) ∧ ∑ i, ‖c i‖ ^ 2 = 1 := by
  classical
  have hU1 : Uᴴ * U = 1 := hU.1
  have hU2 : U * Uᴴ = 1 := hU.2
  have hnormscalar (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm]
    exact (Complex.mul_conj _).trans (congrArg Complex.ofReal (Complex.normSq_eq_norm_sq _))
  have hnormscalar2 (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, hnormscalar]
  constructor
  · rintro ⟨hfix, hnorm⟩
    let B : ι → Matrix d d ℂ := fun i => Uᴴ * A i
    have hBnorm : IsTracePreservingOSR B := by
      have he (i : ι) : (B i)ᴴ * B i = (A i)ᴴ * A i := by
        dsimp [B]
        rw [conjTranspose_mul, conjTranspose_conjTranspose]
        calc
          (A i)ᴴ * U * (Uᴴ * A i) = (A i)ᴴ * (U * Uᴴ) * A i := by noncomm_ring
          _ = (A i)ᴴ * A i := by rw [hU2, mul_one]
      unfold IsTracePreservingOSR
      simp_rw [he]
      exact hnorm
    have hBfix : ∀ ρ : Matrix d d ℂ, WildeQIT.IsDensityOperator ρ → osrApply B ρ = ρ := by
      intro ρ hρ
      have he (i : ι) : B i * ρ * (B i)ᴴ = Uᴴ * (A i * ρ * (A i)ᴴ) * U := by
        dsimp [B]
        rw [conjTranspose_mul, conjTranspose_conjTranspose]
        noncomm_ring
      unfold osrApply
      simp_rw [he]
      rw [← sum_mul, ← mul_sum]
      change Uᴴ * osrApply A ρ * U = ρ
      rw [hfix ρ hρ]
      calc
        Uᴴ * (U * ρ * Uᴴ) * U = (Uᴴ * U) * ρ * (Uᴴ * U) := by noncomm_ring
        _ = ρ := by rw [hU1, one_mul, mul_one]
    have heig (i : ι) : ∀ ψ : d → ℂ, star ψ ⬝ᵥ ψ = 1 → ∃ c : ℂ, B i *ᵥ ψ = c • ψ := by
      intro ψ hψ
      exact ⟨_, eq_2_32_2_34 B hBnorm ψ hψ (eq_2_31 B hBfix ψ hψ) i⟩
    obtain ⟨c, hc⟩ := eq_2_35 A U hU heig
    have hA (i : ι) : A i = c i • U := (hc i).2
    have hB (i : ι) : B i = c i • (1 : Matrix d d ℂ) := (hc i).1
    refine ⟨c, hA, ?_⟩
    have he (i : ι) : (B i)ᴴ * B i = ((‖c i‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix d d ℂ) := by
      rw [hB i, conjTranspose_smul]
      simp only [conjTranspose_one, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_one, hnormscalar, hnormscalar2]
    change (∑ i, (B i)ᴴ * B i) = 1 at hBnorm
    simp_rw [he] at hBnorm
    rw [← sum_smul] at hBnorm
    let j : d := Classical.choice inferInstance
    have hh := congrArg (fun M : Matrix d d ℂ => M j j) hBnorm
    change (∑ i, ((‖c i‖ ^ 2 : ℝ) : ℂ)) * (1 : Matrix d d ℂ) j j = (1 : Matrix d d ℂ) j j at hh
    simp only [one_apply_eq, mul_one] at hh
    exact_mod_cast hh
  · rintro ⟨c, hA, hc⟩
    have hcC : (∑ i, ((‖c i‖ ^ 2 : ℝ) : ℂ)) = 1 := by exact_mod_cast hc
    constructor
    · intro ρ _
      have he (i : ι) : A i * ρ * (A i)ᴴ =
          ((‖c i‖ ^ 2 : ℝ) : ℂ) • (U * ρ * Uᴴ) := by
        rw [hA, conjTranspose_smul]
        simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, hnormscalar, hnormscalar2]
      unfold osrApply
      simp_rw [he]
      rw [← sum_smul, hcC, one_smul]
    · have he (i : ι) : (A i)ᴴ * A i =
          ((‖c i‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix d d ℂ) := by
        rw [hA, conjTranspose_smul]
        simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, hU1, hnormscalar, hnormscalar2]
      unfold IsTracePreservingOSR
      simp_rw [he]
      rw [← sum_smul, hcC, one_smul]
