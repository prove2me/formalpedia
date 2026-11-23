-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx5.supA_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:42.738825+00:00
-- url     : https://prove2.me/submissions/0290beb3-05e8-4ba6-b2dd-01cf7e5e4d23

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant

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
namespace Formalism.FourierDecayAlt.P.Jx5
theorem _root_.solution {ι : Type} [Fintype ι] (G : Sz.Glob ι) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ)
    (one : Bool) (w : ι) (hg : 0 < G.g) (hv : 0 < G.v) : 0 ≤ supA G de de' T T' l one w := by
  have hka : 0 < G.ka := by unfold Sz.Glob.ka; positivity
  have hel : ∀ Y, 0 ≤ G.g ^ G.m * (G.place w).be G.ka de de' T T' Y := by
    intro Y
    unfold Sz.Cfg.be Sz.Cfg.core
    positivity
  unfold supA
  apply div_nonneg _ (by positivity)
  cases one
  · simp only [Bool.false_eq_true, if_false]
    unfold Sz.Glob.supI
    apply Real.sSup_nonneg
    rintro x ⟨Y, _, rfl⟩
    exact hel Y
  · simp only [if_true]
    unfold Sz.Glob.cutSupLong
    apply Real.sSup_nonneg
    rintro x ⟨Y, _, rfl⟩
    exact hel Y
end Formalism.FourierDecayAlt.P.Jx5
