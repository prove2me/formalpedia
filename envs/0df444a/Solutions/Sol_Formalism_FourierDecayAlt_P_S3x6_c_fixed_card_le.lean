-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.c_fixed_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:41.684328+00:00
-- url     : https://prove2.me/submissions/3d0904df-5af6-40da-850f-3758513c4a75

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_c_two_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_c_card_pow_le

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
theorem _root_.solution [DecidableEq K] (hq : Fintype.card K = q ^ 2) :
    (univ.filter (fun x : K => x ^ q = x)).card ≤ q := by
  have h2 := c_two_le K q hq
  have hsub : univ.filter (fun x : K => x ^ q = x) ⊆ insert 0 (univ.filter (fun x : K => x ^ (q - 1) = 1)) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and, mem_insert] at hx ⊢
    by_cases h0 : x = 0
    · exact Or.inl h0
    · right
      have : x * x ^ (q - 1) = x * 1 := by
        rw [mul_one, ← pow_succ']
        have : q - 1 + 1 = q := by omega
        rw [this]; exact hx
      exact mul_left_cancel₀ h0 this
  have h3 := c_card_pow_le K (q - 1) (by omega) 1
  have h4 := Finset.card_le_card hsub
  have h5 := Finset.card_insert_le (0 : K) (univ.filter (fun x : K => x ^ (q - 1) = 1))
  omega
end Formalism.FourierDecayAlt.P.S3x6
