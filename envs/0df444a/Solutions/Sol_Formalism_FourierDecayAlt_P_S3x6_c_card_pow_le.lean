-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.c_card_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:02.896904+00:00
-- url     : https://prove2.me/submissions/85598d75-2a20-41bd-8f2d-145ae1ab4f4d

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
open Finset
variable (K : Type) [Field K] [Fintype K] (q : ℕ)
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution [DecidableEq K] (n : ℕ) (hn : 0 < n) (a : K) :
    (univ.filter (fun x : K => x ^ n = a)).card ≤ n := by
  calc (univ.filter (fun x : K => x ^ n = a)).card ≤ (Polynomial.nthRoots n a).toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        simp [Polynomial.mem_nthRoots hn, hx]
    _ ≤ Multiset.card (Polynomial.nthRoots n a) := Multiset.toFinset_card_le _
    _ ≤ n := Polynomial.card_nthRoots n a
end Formalism.FourierDecayAlt.P.S3x6
