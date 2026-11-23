-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.det_rows_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:14.551889+00:00
-- url     : https://prove2.me/submissions/7f800657-7687-4ebd-8d34-a3d7bafa16d9

import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution {t : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (e : Fin t ≃ Fin n) (α : Fin t → Fin n)
    (hα : ¬ Function.Injective α) : (Matrix.of fun i j : Fin t => P (α i) (e j)).det = 0 := by
  simp only [Function.Injective, not_forall] at hα
  obtain ⟨i, i', h, hne⟩ := hα
  exact Matrix.det_zero_of_row_eq hne (by funext j; simp [h])
end Formalism.FourierDecayAlt.P.JFxE
