-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.rpow_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:09.7615+00:00
-- url     : https://prove2.me/submissions/2077890d-202c-4043-8215-e854d4051ccc

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x6
open Formalism.FourierDecayAlt.P.A5x5
namespace Formalism.FourierDecayAlt.P.A6x6
theorem _root_.solution {x X : ℝ} (hx : 0 < x) (hX : 0 ≤ X) (h : X ^ 2 * x = 1) :
    X = x ^ (-(1 : ℝ) / 2) := by
  have h1 : (x ^ (-(1 : ℝ) / 2)) ^ 2 = x⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
    exact Real.rpow_neg_one x
  have h2 : X ^ 2 = (x ^ (-(1 : ℝ) / 2)) ^ 2 := by
    rw [h1]; field_simp; exact h
  exact (pow_left_inj₀ hX (Real.rpow_nonneg hx.le _) (by norm_num)).1 h2
end Formalism.FourierDecayAlt.P.A6x6
