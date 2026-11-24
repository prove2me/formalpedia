-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.up_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:52:05.749842+00:00
-- url     : https://prove2.me/submissions/886d1523-cafa-4c40-a52e-293005a394ff

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_glev_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
local notation "⟪" u ", " v "⟫" => herm (Hpk k r) u v
variable {l : Fin r}
local notation "𝐞" => bvec (eI k r l)
local notation "𝐬" => bvec (esI k r l)
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution {u u' : Mx k r} (hu : u ∈ UP k r l) (hu' : u' ∈ UP k r l) : u * u' ∈ UP k r l := by
  refine ⟨glev_mul hu.1 hu'.1, by rw [← Matrix.mulVec_mulVec, hu'.2.1, hu.2.1], fun y hy => ?_⟩
  obtain ⟨t', ht'⟩ := hu'.2.2 y hy
  obtain ⟨t, ht⟩ := hu.2.2 y hy
  refine ⟨t + t', ?_⟩
  rw [← Matrix.mulVec_mulVec, ht', Matrix.mulVec_add, Matrix.mulVec_smul, hu.2.1, ht, add_smul]
  exact add_assoc _ _ _
end Formalism.FourierDecayAlt.P.Qx4
