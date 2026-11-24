-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dilation_unipotent_weyl_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:51:46.366715+00:00
-- url     : https://prove2.me/submissions/43c669de-7c8e-4417-b9a0-50990b0d3255

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dg_mid
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_block


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B.DilUW := by
  intro k r z t h hh
  obtain ⟨hc, hr⟩ := WeylGroupFacts.uw_block hh
  ext i j
  rw [aDil_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hj : j.val < r ∨ r + k < j.val
  · rw [hc i j hj]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · by_cases hi : i.val < r ∨ r + k < i.val
    · rw [hr i j hi]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    · rw [dg_mid k r t i (by omega) (by omega), dg_mid k r t j (by omega) (by omega)]; ring
end Formalism.FourierDecayAlt.P
