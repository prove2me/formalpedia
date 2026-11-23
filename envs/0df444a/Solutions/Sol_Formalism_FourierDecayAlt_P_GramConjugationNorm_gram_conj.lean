-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramConjugationNorm.gram_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:46.779512+00:00
-- url     : https://prove2.me/submissions/e78f90ef-631c-4e15-bbfe-1a6751a20be9

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramConjugationNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramConjugationNorm
open Finset Filter Topology Formalism.FourierDecayAlt.TA
open scoped InnerProductSpace ComplexConjugate
variable {E : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.GramConjugationNorm
theorem _root_.solution (k : Pt E → Pt E → ℂ) (V : Pt E → H) (P : Finset (Pt E))
    (hk : PSDOn P k) : conj (gram k V P) = gram k V P := by
  unfold gram
  rw [map_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun p' hp' => ?_
  rw [map_mul, inner_conj_symm, hk.1 p hp p' hp']
end Formalism.FourierDecayAlt.P.GramConjugationNorm
