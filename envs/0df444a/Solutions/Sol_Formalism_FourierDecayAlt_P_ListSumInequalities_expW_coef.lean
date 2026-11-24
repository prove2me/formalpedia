-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumInequalities.expW_coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:19:04.145798+00:00
-- url     : https://prove2.me/submissions/9d059353-426f-48c0-989b-d6d0506b6e16

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_one_le_Kc
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_kc_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumInequalities
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumInequalities
theorem _root_.solution (w : List (Bool × Mat k r)) (hw : ∀ y ∈ w, unitLie k r y.2) :
    ∀ p ∈ expW w, |p.1| ≤ Kc k r ^ w.length := by
  induction w with
  | nil =>
    intro p hp
    simp only [expW, List.mem_singleton] at hp
    subst hp
    simp
  | cons x w ih =>
    intro p hp
    simp only [expW, List.mem_flatMap, List.mem_map] at hp
    obtain ⟨q, hq, i, -, rfl⟩ := hp
    have hq' := ih (fun y hy => hw y (by simp [hy])) q hq
    have hk := kc_le (hw x (by simp)) i
    simp only [List.length_cons, pow_succ]
    rw [abs_mul, mul_comm (Kc k r ^ _)]
    exact mul_le_mul hk hq' (abs_nonneg _) (by linarith [one_le_Kc (k := k) (r := r)])
end Formalism.FourierDecayAlt.P.ListSumInequalities
