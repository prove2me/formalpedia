-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.Hherm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:04:46.203376+00:00
-- url     : https://prove2.me/submissions/617f3820-cf61-4af0-a3fd-cced4904a0a4

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure

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
theorem _root_.solution (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | simp
end Formalism.FourierDecayAlt.P.B2x5
