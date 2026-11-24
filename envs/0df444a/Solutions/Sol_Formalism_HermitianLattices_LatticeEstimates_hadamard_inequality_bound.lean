-- Prove2me | solution 1 for Formalism.HermitianLattices.LatticeEstimates.hadamard_inequality_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:10.380522+00:00
-- url     : https://prove2.me/submissions/444b948e-f7ec-4063-9a5e-65c2eefdce04

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InverseNormLeOfIntegerInner
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Theorems.Thm_Formalism_HermitianLattices_LatticeEstimates_hadamard_unit_diagonal_det_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LatticeEstimates
open Finset MeasureTheory Matrix Real
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (Interlace B0 len)
open scoped ComplexOrder
namespace Formalism.HermitianLattices.LatticeEstimates
theorem _root_.solution : Ms_hadamard := by
  intro N G hG
  have hdiag : ∀ c, 0 ≤ (G c c).re ∧ (G c c).im = 0 := by
    intro c
    have := hG.diag_nonneg (i := c)
    rw [Complex.le_def] at this
    exact ⟨by simpa using this.1, by simpa using this.2.symm⟩
  by_cases h0 : ∃ c, (G c c).re = 0
  · obtain ⟨c, hc⟩ := h0
    have hGc : G c c = 0 := Complex.ext hc (hdiag c).2
    have hv : G *ᵥ (Pi.single c 1) = 0 := by
      apply (hG.dotProduct_mulVec_zero_iff _).mp
      simp [hGc]
    have hdet : G.det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨Pi.single c 1, by simp, hv⟩
    rw [hdet, Finset.prod_eq_zero (mem_univ c) hc]; simp
  · push Not at h0
    have hpos : ∀ c, 0 < (G c c).re := fun c => lt_of_le_of_ne (hdiag c).1 (Ne.symm (h0 c))
    let s : Fin N → ℝ := fun c => (Real.sqrt (G c c).re)⁻¹
    have hs2 : ∀ c, s c * s c = ((G c c).re)⁻¹ := by
      intro c
      simp only [s]
      rw [← mul_inv, Real.mul_self_sqrt (hpos c).le]
    let Dg : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun c => (s c : ℂ))
    have hDg : Dgᴴ = Dg := by
      simp [Dg, Matrix.diagonal_conjTranspose, Pi.star_def]
    have hH : (Dgᴴ * G * Dg).PosSemidef := hG.conjTranspose_mul_mul_same Dg
    rw [hDg] at hH
    have hGre : ∀ c, G c c = (((G c c).re : ℝ) : ℂ) := fun c => Complex.ext (by simp) (by simp [(hdiag c).2])
    have hHd : ∀ c, (Dg * G * Dg) c c = 1 := by
      intro c
      simp only [Dg, Matrix.mul_diagonal, Matrix.diagonal_mul]
      rw [hGre c]
      have : (s c : ℂ) * (((G c c).re : ℝ) : ℂ) * (s c : ℂ) = ((s c * s c * (G c c).re : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, hs2 c, inv_mul_cancel₀ (hpos c).ne']; simp
    have h1 := hadamard_unit_diagonal_det_le_one N _ hH hHd
    have hdetD : Dg.det = ((∏ c, s c : ℝ) : ℂ) := by simp [Dg, Matrix.det_diagonal]
    rw [Matrix.det_mul, Matrix.det_mul, hdetD] at h1
    have h2 : (((∏ c, s c : ℝ) : ℂ) * G.det * ((∏ c, s c : ℝ) : ℂ)).re = ((∏ c, s c) * (∏ c, s c)) * G.det.re := by
      rw [Complex.re_mul_ofReal, Complex.re_ofReal_mul]; ring
    rw [h2, ← Finset.prod_mul_distrib] at h1
    simp only [hs2] at h1
    rw [Finset.prod_inv_distrib] at h1
    have hP : 0 < ∏ c, (G c c).re := Finset.prod_pos (fun c _ => hpos c)
    rwa [inv_mul_le_iff₀ hP, mul_one] at h1
end Formalism.HermitianLattices.LatticeEstimates
