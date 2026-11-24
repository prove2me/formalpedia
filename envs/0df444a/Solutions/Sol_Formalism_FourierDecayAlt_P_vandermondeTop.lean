-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.vandermondeTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:07.555374+00:00
-- url     : https://prove2.me/submissions/47f14ddd-324d-4e2d-9961-00744239b71e

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_rde_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_succ_top
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_prod_refl
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_v_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_v_anti
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_words_ratio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Sz.VandTop := by
  intro c de hc hw
  have hk := hc.hk
  have hcast : ((c.k - 2 : ℕ) : ℝ) + 1 = (c.k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hb := rde_bound (c.k - 2) (by omega) de hw.1
  rw [hcast] at hb
  refine ⟨vand_pos _ _ fun i j _ hij _ => v_anti c hc i j hij,
    vand_words_ratio c de hw (c.k - 2) (by omega) (Or.inl (by omega)), hb.1, hb.2, ?_⟩
  have h := vand_succ_top (c.k - 2) c.v
  have e : c.k - 2 + 1 = c.k - 1 := by omega
  have h2 : ∏ i ∈ Icc 1 (c.k - 2), (c.v i - c.v (c.k - 2 + 1)) =
      (4 * c.Del) ^ (c.k - 2) * ((c.k - 2).factorial : ℝ) := by
    rw [← prod_refl (c.k - 2)]
    simp only [v_sub]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
    simp
  rw [h2, e] at h
  rw [h]; ring
end Formalism.FourierDecayAlt.P
