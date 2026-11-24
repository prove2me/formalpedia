-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.sum_split_first_middle_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:04:53.972566+00:00
-- url     : https://prove2.me/submissions/3bb8a4e2-1f8d-4e49-9ddf-61fe71d29078

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution {N n : ℕ} (h : N = n + 2) (f : Fin N → ℂ) :
    ∑ i, f i = f ⟨0, by omega⟩ + ∑ j : Fin n, f ⟨j.val + 1, by omega⟩ + f ⟨n + 1, by omega⟩ := by
  subst h
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, ← add_assoc]
  rfl
end Formalism.FourierDecayAlt.P.B2x8
