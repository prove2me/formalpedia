-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.vandermondeNonTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:06.814819+00:00
-- url     : https://prove2.me/submissions/dea82768-84a4-4fe8-96a3-cc3cbf802331

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_rde_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_pos
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
theorem _root_.solution : Formalism.FourierDecayAlt.Sz.VandNonTop := by
  intro c de hc hw ht
  have hk := hc.hk
  have hcast : ((c.k - 1 : ℕ) : ℝ) + 1 = c.k := by
    rw [Nat.cast_sub (by omega)]; simp
  have hb := rde_bound (c.k - 1) (by omega) de hw.1
  rw [hcast] at hb
  exact ⟨vand_pos _ _ fun i j _ hij _ => v_anti c hc i j hij,
    vand_words_ratio c de hw (c.k - 1) (by omega) (Or.inr ht), hb.1, hb.2⟩
end Formalism.FourierDecayAlt.P
