-- Prove2me | solution 1 for BookProof.SpectralGapStability.notMem_spectrum_of_gapAt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:23.157458+00:00
-- url     : https://prove2.me/submissions/62d77e7c-f659-4da0-86ae-c99661c95ee7

-- Generated from ChapterSpectralGapStability.lean — solution of BookProof.SpectralGapStability.notMem_spectrum_of_gapAt
import Mathlib
import Definitions.Def_ChapterSpectralGapStability
open BookProof.SpectralGapStability



noncomputable section


open scoped InnerProductSpace
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {lam d : ℝ}
    (hd : 0 < d) (h : GapAt A lam d) : (lam : ℂ) ∉ spectrum ℂ A := by

  set B : F →L[ℂ] F := A - (lam : ℂ) • (1 : F →L[ℂ] F) with hB
  have hBapp : ∀ x, B x = A x - (lam : ℂ) • x := by
    intro x; simp [hB]
  have hBx : ∀ x, d * ‖x‖ ≤ ‖B x‖ := by
    intro x; rw [hBapp x]; exact h x
  -- injectivity
  have hinj : Function.Injective B := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have := hBx x
    rw [hx, norm_zero] at this
    have : ‖x‖ ≤ 0 := by nlinarith [norm_nonneg x]
    simpa using le_antisymm this (norm_nonneg x)
  -- closed range
  have hanti : AntilipschitzWith ⟨d⁻¹, (inv_pos.2 hd).le⟩ B := by
    refine AddMonoidHomClass.antilipschitz_of_bound B ?_
    intro x
    have hxb := hBx x
    have h1 : ‖x‖ = d⁻¹ * (d * ‖x‖) := by
      calc ‖x‖ = 1 * ‖x‖ := (one_mul _).symm
        _ = (d⁻¹ * d) * ‖x‖ :=
          (congrArg (fun w => w * ‖x‖) (inv_mul_cancel₀ hd.ne')).symm
        _ = d⁻¹ * (d * ‖x‖) := mul_assoc d⁻¹ d ‖x‖
    have h2 : d⁻¹ * (d * ‖x‖) ≤ d⁻¹ * ‖B x‖ :=
      mul_le_mul_of_nonneg_left hxb (inv_pos.2 hd).le
    have h3 : ‖x‖ ≤ d⁻¹ * ‖B x‖ := by linarith
    exact h3
  have hclosed : IsClosed (Set.range B) := hanti.isClosed_range B.lipschitz.uniformContinuous
  -- symmetry
  have hAsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hsym : ∀ x y : F, (inner ℂ (B x) y : ℂ) = inner ℂ x (B y) := by
    intro x y
    have hA' : (inner ℂ (A x) y : ℂ) = inner ℂ x (A y) := hAsym x y
    rw [hBapp, hBapp, inner_sub_left, inner_sub_right, hA', inner_smul_left,
      inner_smul_right, Complex.conj_ofReal]
  -- dense range, hence surjectivity
  have hrangeSet : (LinearMap.range (B : F →ₗ[ℂ] F) : Set F) = Set.range B := by
    ext y; simp [LinearMap.mem_range]
  have hrangeClosed : IsClosed (LinearMap.range (B : F →ₗ[ℂ] F) : Set F) := by
    rw [hrangeSet]; exact hclosed
  have hcompl : (LinearMap.range (B : F →ₗ[ℂ] F))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hzero : ∀ x : F, (inner ℂ (B x) y : ℂ) = 0 := by
      intro x
      exact hy (B x) ⟨x, rfl⟩
    have hBy : (inner ℂ (B y) (B y) : ℂ) = 0 := by
      have h1 := hzero (B y)
      rwa [hsym (B y) y] at h1
    have : B y = 0 := by
      simpa using inner_self_eq_zero.mp hBy
    have hnorm := hBx y
    rw [this, norm_zero] at hnorm
    have : ‖y‖ ≤ 0 := by nlinarith [norm_nonneg y]
    simpa using le_antisymm this (norm_nonneg y)
  have hsurj : Function.Surjective B := by
    letI : IsClosed (LinearMap.range (B : F →ₗ[ℂ] F) : Set F) := hrangeClosed
    haveI : CompleteSpace (LinearMap.range (B : F →ₗ[ℂ] F)) := IsClosed.completeSpace_coe
    haveI := Submodule.HasOrthogonalProjection.ofCompleteSpace
      (LinearMap.range (B : F →ₗ[ℂ] F))
    have htop : LinearMap.range (B : F →ₗ[ℂ] F) = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hcompl
    intro y
    have : y ∈ LinearMap.range (B : F →ₗ[ℂ] F) := by rw [htop]; trivial
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx⟩
  have hunitB : IsUnit B := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, hsurj⟩
  rw [spectrum.mem_iff]
  push_neg
  have halg : (algebraMap ℂ (F →L[ℂ] F)) (lam : ℂ) - A = -B := by
    rw [Algebra.algebraMap_eq_smul_one, hB]; abel
  rw [halg]
  exact hunitB.neg
