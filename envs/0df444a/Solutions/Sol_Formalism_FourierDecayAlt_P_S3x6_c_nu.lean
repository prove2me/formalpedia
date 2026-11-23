-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.c_nu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:08.934455+00:00
-- url     : https://prove2.me/submissions/f23e155a-c144-4913-b7c7-4addfb0a1a8b

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_c_fibre

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
theorem _root_.solution [DecidableEq K] (hq : Fintype.card K = q ^ 2) (c : K) (hc : c ^ q = c) :
    (univ.filter (fun x : K => c - x ^ q * x = 0)).card = if c = 0 then 1 else q + 1 := by
  have h1 : univ.filter (fun x : K => c - x ^ q * x = 0) = univ.filter (fun x : K => x ^ (q + 1) = c) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, pow_succ, sub_eq_zero]
    exact eq_comm
  rw [h1]
  by_cases h0 : c = 0
  · rw [if_pos h0, h0]
    have : univ.filter (fun x : K => x ^ (q + 1) = 0) = {0} := by
      ext x
      simp
    rw [this, card_singleton]
  · rw [if_neg h0]
    exact c_fibre K q hq c hc h0
end Formalism.FourierDecayAlt.P.S3x6
