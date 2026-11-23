-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.intersection_of_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:56.250744+00:00
-- url     : https://prove2.me/submissions/98cf53d0-eada-466c-af4c-2c6d5392e4e7

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx10_inter_of_module

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.IntersectionOfLocal := by
  intro E _ _ _ L hL t
  obtain ⟨hL1, -⟩ := hL
  constructor
  · intro ht P hP
    unfold Formalism.FourierDecayAlt.S6.locAt
    rw [Set.mem_setOf_eq]
    refine ⟨1, fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1), ?_⟩
    rw [map_one, one_mul]
    exact ht
  · intro h
    exact Jx10.inter_of_module E L hL1 t h
end Formalism.FourierDecayAlt.P
