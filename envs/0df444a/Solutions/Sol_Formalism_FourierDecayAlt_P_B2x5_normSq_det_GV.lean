-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.normSq_det_GV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:03:17.303674+00:00
-- url     : https://prove2.me/submissions/812f9be5-6f87-4530-9054-0931546225f3

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_isUnit_det_Hpk

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : Complex.normSq g.det = 1 := by
  have hH := isUnit_det_Hpk k r
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h2
  have h4 : (star g.det * g.det) * (Hpk k r).det = 1 * (Hpk k r).det := by
    rw [one_mul]
    nth_rewrite 2 [← h2]
    ring
  have h3 := hH.mul_right_cancel h4
  have h5 : ((Complex.normSq g.det : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact h3
  exact_mod_cast h5
end Formalism.FourierDecayAlt.P.B2x5
