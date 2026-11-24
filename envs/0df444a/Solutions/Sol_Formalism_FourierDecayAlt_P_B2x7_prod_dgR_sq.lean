-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x7.prod_dgR_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:52:56.739383+00:00
-- url     : https://prove2.me/submissions/8ec9c2c8-e73e-4c88-9006-de70aa2cdd12

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_dgR_rev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open Formalism.FourierDecayAlt.P.B2x7
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x7
theorem _root_.solution (k r : ℕ) (t : ℝ) (ht : t ≠ 0) : (∏ i, dgR k r t i) ^ 2 = 1 := by
  have h : ∏ i, dgR k r t (Fin.rev i) = ∏ i, dgR k r t i :=
    Equiv.prod_comp Fin.revPerm (dgR k r t)
  rw [sq]
  nth_rewrite 2 [← h]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => dgR_rev k r t ht i
end Formalism.FourierDecayAlt.P.B2x7
