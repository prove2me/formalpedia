-- Prove2me | solution 1 for BookProof.YangMillsAbelianNoGap.gaussInt_op_bigP
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:09:10.920001+00:00
-- url     : https://prove2.me/submissions/0a092ed2-2b4c-4cac-87a5-2a6236740e01

-- Generated from ChapterYangMillsAbelianNoGap.lean — solution of BookProof.YangMillsAbelianNoGap.gaussInt_op_bigP
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianNoGap
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_gaussInt_one_eq
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_coordFactor_facW
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_op_bigP
import Theorems.Thm_BookProof_GaussCoordCombo_coordFactor_coordCombo
import Theorems.Thm_BookProof_GaussCoordCombo_gaussInt_prod_coordFactor
import Theorems.Thm_BookProof_GaussCoordCombo_pderiv_prod_eq_zero
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterSqueezedGaussStates
open BookProof.YangMillsAbelianNoGap




open MvPolynomial MeasureTheory
open BookProof.HermiteProductCore BookProof.GaussCoordCombo BookProof.SqueezedGaussStates
open BookProof.YangMillsHermite BookProof.FarisLavine BookProof.HermiteGalerkin

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable (vf : Fin d → ℝ) (Mf : Fin d → ℕ)

set_option maxHeartbeats 1000000 in
theorem solution (c : Fin d) (α γ : ℝ) :
    gaussInt ((((α : ℝ) : ℂ) • (X c * bigP vf Mf) + ((γ : ℝ) : ℂ) • pderiv c (bigP vf Mf))
        * (((α : ℝ) : ℂ) • (X c * bigP vf Mf) + ((γ : ℝ) : ℂ) • pderiv c (bigP vf Mf)))
      = (((coordComboSum (opCoef α γ (vf c) (Mf c)) 1 (Mf c))
          * (∏ j ∈ Finset.univ.erase c, facS vf Mf j)
          * (Real.sqrt (2 * Real.pi)) ^ d : ℝ) : ℂ) := by

  classical
  set u : MvPolynomial (Fin d) ℂ := coordCombo c (opCoef α γ (vf c) (Mf c)) 1 (Mf c) with hu
  set R : MvPolynomial (Fin d) ℂ := ∏ j ∈ Finset.univ.erase c, facW vf Mf j with hR
  have hCFu : CoordFactor c u (coordComboSum (opCoef α γ (vf c) (Mf c)) 1 (Mf c)) :=
    coordFactor_coordCombo c _ _ _
  have hRR : gaussInt (R * (R * 1))
      = (((∏ j ∈ Finset.univ.erase c, facS vf Mf j) : ℝ) : ℂ) * gaussInt 1 :=
    gaussInt_prod_coordFactor (fun j _ => coordFactor_facW vf Mf j) (fun j _ => by simp)
  have hpRR : pderiv c (R * (R * 1)) = 0 := by
    have hpR : pderiv c R = 0 := by
      refine pderiv_prod_eq_zero (fun j hj => ?_)
      exact (coordFactor_facW vf Mf j).1 c (fun h => (Finset.ne_of_mem_erase hj) h.symm)
    rw [Derivation.leibniz, hpR, Derivation.leibniz, hpR]
    simp
  have hkey := hCFu.2 (R * (R * 1)) hpRR
  rw [op_bigP vf Mf c α γ, ← hu, ← hR]
  have hrw : (u * R) * (u * R) = u * (u * (R * (R * 1))) := by ring
  rw [hrw, hkey, hRR, gaussInt_one_eq]
  push_cast
  ring
