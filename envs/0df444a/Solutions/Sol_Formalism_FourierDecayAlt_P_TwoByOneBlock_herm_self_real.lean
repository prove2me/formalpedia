-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:51:01.675026+00:00
-- url     : https://prove2.me/submissions/3ba4e6ce-4243-4ea0-8775-c2c6e9e38bfa

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_symm

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution (hH : Hᴴ = H) (x : Fin m → ℂ) : herm H x x = ((herm H x x).re : ℂ) := by
  have h := herm_symm H hH x x
  apply Complex.ext
  · simp
  · have h2 := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at h2
    simp only [Complex.ofReal_im]
    linarith
end Formalism.FourierDecayAlt.P.TwoByOneBlock
