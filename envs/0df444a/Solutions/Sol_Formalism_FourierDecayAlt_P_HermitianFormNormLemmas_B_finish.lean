-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.finish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:58.458693+00:00
-- url     : https://prove2.me/submissions/d7a48cd8-462e-4d86-b8b4-e8c13542f0cd

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_B_pow_card_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical
variable {Cl Nu : Type}
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
theorem _root_.solution (L : LocalNG Cl Nu) (Xp Yp : L.P → ℝ) (hX : ∀ p, 1 ≤ Xp p) (hY : ∀ p, 1 ≤ Yp p) (e : ℕ)
    (h : ∀ p, (if p ∈ L.Om then (4 : ℝ) else 1) * (Xp p * Yp p) ≤ L.H p ^ e) :
    (4 : ℝ) ^ L.Om.card * (∏ p, Xp p * Yp p) ≤ L.Htot ^ e := by
  have hnn : ∀ p ∈ Finset.univ, 0 ≤ (if p ∈ L.Om then (4 : ℝ) else 1) * (Xp p * Yp p) := by
    intro p _
    exact mul_nonneg (by split_ifs <;> norm_num)
      (mul_nonneg (by linarith [hX p]) (by linarith [hY p]))
  calc (4 : ℝ) ^ L.Om.card * (∏ p, Xp p * Yp p)
      = ∏ p, (if p ∈ L.Om then (4 : ℝ) else 1) * (Xp p * Yp p) := by
        rw [pow_card_eq, ← Finset.prod_mul_distrib]
    _ ≤ ∏ p, L.H p ^ e := Finset.prod_le_prod hnn (fun p _ => h p)
    _ = L.Htot ^ e := by
        rw [Finset.prod_pow]
        rfl
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
