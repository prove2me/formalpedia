-- Prove2me | solution 1 for BookProof.SpectralGapStability.spectrum_disjoint_of_shifted_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:28.387385+00:00
-- url     : https://prove2.me/submissions/5c155c34-ae4a-4853-a4ed-e914cb802445

-- Generated from ChapterSpectralGapStability.lean — solution of BookProof.SpectralGapStability.spectrum_disjoint_of_shifted_square_bound
import Mathlib
import Definitions.Def_ChapterSpectralGapStability
import Theorems.Thm_BookProof_SpectralGapStability_notMem_spectrum_of_gapAt
open BookProof.SpectralGapStability



noncomputable section


open scoped InnerProductSpace
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {A : F →L[ℂ] F} (hA : IsSelfAdjoint A)
    {c q : ℝ} (hq : 0 < q)
    (hbound : ∀ x : F, q * ‖x‖ ^ 2 ≤ ‖(A - (c : ℂ) • (1 : F →L[ℂ] F)) x‖ ^ 2) :
    ∀ lam ∈ Set.Ioo (c - Real.sqrt q) (c + Real.sqrt q),
      (lam : ℂ) ∉ spectrum ℂ A := by

  intro lam hlam
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hdist : |lam - c| < Real.sqrt q := by
    rw [abs_lt]
    constructor <;> linarith [hlam.1, hlam.2]
  have hnot : ∀ x : F, (Real.sqrt q - |lam - c|) * ‖x‖ ≤
      ‖A x - (lam : ℂ) • x‖ := by
    intro x
    have hsq : q * ‖x‖ ^ 2 ≤ ‖A x - (c : ℂ) • x‖ ^ 2 := by
      simpa [ContinuousLinearMap.sub_apply] using hbound x
    have htri : ‖A x - (c : ℂ) • x‖ ≤
        ‖A x - (lam : ℂ) • x‖ + |lam - c| * ‖x‖ := by
      have heq : A x - (c : ℂ) • x =
          (A x - (lam : ℂ) • x) + ((lam - c : ℂ) • x) := by
        module
      rw [heq]
      calc
        ‖A x - (lam : ℂ) • x + (lam - c : ℂ) • x‖ ≤
            ‖A x - (lam : ℂ) • x‖ + ‖(lam - c : ℂ) • x‖ := norm_add_le _ _
        _ = ‖A x - (lam : ℂ) • x‖ + |lam - c| * ‖x‖ := by
          have hnorm : ‖((lam : ℂ) - (c : ℂ))‖ = |lam - c| := by
            rw [show ((lam : ℂ) - (c : ℂ)) = ((lam - c : ℝ) : ℂ) by push_cast; ring,
              Complex.norm_real, Real.norm_eq_abs]
          rw [norm_smul, hnorm]
    have hqnorm : Real.sqrt q * ‖x‖ ≤ ‖A x - (c : ℂ) • x‖ := by
      have h1 : Real.sqrt (q * ‖x‖ ^ 2) ≤ Real.sqrt (‖A x - (c : ℂ) • x‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_mul hq.le, Real.sqrt_sq (norm_nonneg x),
        Real.sqrt_sq (norm_nonneg _)] at h1
    linarith
  have hpos : 0 < Real.sqrt q - |lam - c| := sub_pos.mpr hdist
  exact notMem_spectrum_of_gapAt hA hpos (by simpa [GapAt] using hnot)
