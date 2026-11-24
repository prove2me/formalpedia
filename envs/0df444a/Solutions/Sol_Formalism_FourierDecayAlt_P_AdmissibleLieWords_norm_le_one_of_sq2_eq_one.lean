-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.norm_le_one_of_sq2_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:27:49.879727+00:00
-- url     : https://prove2.me/submissions/1c17a570-1252-43b5-871a-1c800e9b41ba

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfUnitWords
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Manifold Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution {m : ℕ} {v : Fin m → ℂ} (h : C6.sq2 v = 1) : ‖v‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
  have h1 : Complex.normSq (v a) ≤ 1 := by
    rw [← h]
    unfold C6.sq2
    exact Finset.single_le_sum (f := fun a => Complex.normSq (v a)) (fun i _ => Complex.normSq_nonneg _)
      (Finset.mem_univ a)
  have h2 : ‖v a‖ ^ 2 ≤ 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h1
  nlinarith [norm_nonneg (v a)]
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
