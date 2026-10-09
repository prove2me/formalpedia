-- Prove2me | solution 1 for BookProof.BookBrstYangMills.gaussGenPoly_bracket
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:29:43.621436+00:00
-- url     : https://prove2.me/submissions/466f6d8b-fb99-4638-ad73-85b9bac8c7c9

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.gaussGenPoly_bracket
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
import Theorems.Thm_BookProof_BookBrstYangMills_sum_smul_der_apply
import Theorems.Thm_BookProof_BookBrstYangMills_gaussDer_bracket
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (c e : Fin N) :
    gaussGenPoly G c * gaussGenPoly G e - gaussGenPoly G e * gaussGenPoly G c
      = ∑ h, (G.f c e h) • gaussGenPoly G h := by

  refine LinearMap.ext fun p => ?_
  have h := congrArg (fun D : Derivation ℂ (FieldPoly N) (FieldPoly N) => D p)
    (gaussDer_bracket G c e)
  simp only [Derivation.commutator_apply] at h
  have hR : (∑ h, ((G.f c e h : ℝ) : ℂ) • gaussDer G h) p
      = ∑ h, ((G.f c e h : ℝ) : ℂ) • (gaussDer G h) p := sum_smul_der_apply _ _ _
  rw [hR] at h
  calc (gaussGenPoly G c * gaussGenPoly G e - gaussGenPoly G e * gaussGenPoly G c) p
      = (gaussDer G c) ((gaussDer G e) p) - (gaussDer G e) ((gaussDer G c) p) := rfl
    _ = ∑ h, ((G.f c e h : ℝ) : ℂ) • (gaussDer G h) p := h
    _ = (∑ h, (G.f c e h) • gaussGenPoly G h) p := by
        rw [LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun h _ => by
          simp [gaussGenPoly]
