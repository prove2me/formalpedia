-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.pow_apply_strict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:31.19529+00:00
-- url     : https://prove2.me/submissions/37d3f63c-8b68-4971-861c-1d64655d73df

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X) :
    ∀ (j : ℕ) (i k : Fin n), (k : ℕ) < i + j → (X ^ j) i k = 0 := by
  intro j
  induction j with
  | zero =>
    intro i k h
    have : i ≠ k := by
      rintro rfl
      simp at h
    simp [this]
  | succ j ih =>
    intro i k h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : (l : ℕ) < i + j
    · rw [ih i l hl, zero_mul]
    · rw [hX l k (by rw [Fin.le_def]; omega), mul_zero]
end Formalism.FourierDecayAlt.P.G7
