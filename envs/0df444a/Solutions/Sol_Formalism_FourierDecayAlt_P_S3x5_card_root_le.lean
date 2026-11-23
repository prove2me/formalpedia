-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.card_root_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:57.321801+00:00
-- url     : https://prove2.me/submissions/b07cc519-e6b9-47f0-8a80-68076b607cb5

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Polynomial Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution (p : K[X]) (hp : p ≠ 0) : Nat.card {x : K // p.eval x = 0} ≤ p.natDegree := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc _ ≤ p.roots.toFinset.card := Finset.card_le_card (by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]
        exact hx)
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ _ := Polynomial.card_roots' p
end Formalism.FourierDecayAlt.P.S3x5
