-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx5.thrS_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:43.896372+00:00
-- url     : https://prove2.me/submissions/13cce2dd-4cba-4cd5-9856-8be491304c40

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
theorem _root_.solution (hF : FrameProducts) (hv : G.v = S6.rd E / 2) (hg : 0 < G.g) (b s : ℕ) (hb : 1 ≤ b)
    (hs : 1 ≤ s) (w : InfinitePlace E) :
    thrS G C de de' T T' l b s w * (G.g * S6.rd E ^ (S6.nuBlock G.r b s + 1)) =
      Sz.lamHat b s C G.ka G.N G.lenI G.g (supBS G de de' T T' l b s w) := by
  have hrd := rd_pos' (E := E)
  have hka := ka_eq G hv
  have hkap : 0 < G.ka := by rw [hka]; positivity
  have h := (hF G.r b s C (S6.rd E) G.g G.N G.lenI
    (supA G de de' T T' l (decide (b = 1 ∧ s = 1)) w) (T * T') hb hs hrd hg).1
  have hm : G.m = 2 * G.r + 2 := rfl
  unfold thrS
  rw [hm, h, ← hka]
  congr 1
  unfold supA supBS
  rw [hm]
  simp only [decide_eq_true_eq]
  field_simp
end Formalism.FourierDecayAlt.P.Jx5
