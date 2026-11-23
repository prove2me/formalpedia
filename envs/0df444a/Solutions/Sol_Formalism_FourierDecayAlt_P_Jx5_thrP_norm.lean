-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx5.thrP_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:43.569596+00:00
-- url     : https://prove2.me/submissions/135f5d60-9074-4d1a-8ee4-f372afbd6a3e

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Jx5_rd_pos__157dd2cb063d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx5_ka_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped Pointwise
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx5
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable (G : Sz.Glob (InfinitePlace E)) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ)
namespace Formalism.FourierDecayAlt.P.Jx5
theorem _root_.solution (hF : FrameProducts) (hv : G.v = S6.rd E / 2) (hg : 0 < G.g) (b : ℕ) (hb : 1 ≤ b)
    (w : InfinitePlace E) :
    thrP G C de de' T T' l b w * (G.g * S6.rd E ^ (S6.nuBlock G.r b ((G.r : ℤ) + 2 - b))) =
      Sz.lamPrimeHat b C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T') := by
  have hrd := rd_pos' (E := E)
  have hka := ka_eq G hv
  have hkap : 0 < G.ka := by rw [hka]; positivity
  have h := (hF G.r b 1 C (S6.rd E) G.g G.N G.lenI
    (supA G de de' T T' l false w) (T * T') hb le_rfl hrd hg).2
  have hm : G.m = 2 * G.r + 2 := rfl
  unfold thrP
  rw [hm, h, ← hka]
  congr 1
  unfold supA
  rw [hm]
  simp only [Bool.false_eq_true, if_false]
  field_simp
end Formalism.FourierDecayAlt.P.Jx5
