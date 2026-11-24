-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x4.heisG_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:46:15.502249+00:00
-- url     : https://prove2.me/submissions/68062443-9167-4d51-8449-8311aa8df5ec

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_hermitian_first_basis_right

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x4
theorem _root_.solution (k r' : ℕ) (v : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) (i j : Fin (2 * (1 + r') + k + 1)) :
    heisG k r' v b i j = (if i = j then 1 else 0) - e0 k r' i * herm (Hpk k (1 + r')) (bvec j) v +
      (v i + b * e0 k r' i) * (if j.val = 2 * (1 + r') + k then 1 else 0) := by
  simp only [heisG, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, vecMulVec_apply, hermitian_first_basis_right,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply, lastI, Fin.ext_iff]
  congr 2
  simp only [eq_comm]
end Formalism.FourierDecayAlt.P.B2x4
