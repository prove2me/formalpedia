-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.Fk_iter_lim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:03.784799+00:00
-- url     : https://prove2.me/submissions/7c61f19c-d549-49a3-8c54-b852864b1b16

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_Fk_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_Fk_deriv
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_Fk_lim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (p : ℕ) : ∀ (k : ℕ) (s : ℝ),
    Tendsto (iteratedDeriv p (Fk k s)) atTop (𝓝 (if p = 0 ∧ k = 0 then 1 else 0)) := by
  induction p with
  | zero => intro k s; simpa using Fk_lim k s
  | succ n ih =>
    intro k s
    rw [iteratedDeriv_succ', Fk_deriv]
    have hadd : iteratedDeriv n (fun t => -(k:ℝ) * Fk k s t + s * Fk (k+1) (s+1) t) =
        fun t => -(k:ℝ) * iteratedDeriv n (Fk k s) t + s * iteratedDeriv n (Fk (k+1) (s+1)) t := by
      funext t
      have c1 : ContDiffAt ℝ n (fun t => -(k:ℝ) * Fk k s t) t :=
        (contDiff_const.mul ((Fk_contDiff k s).of_le (by exact_mod_cast le_top))).contDiffAt
      have c2 : ContDiffAt ℝ n (fun t => s * Fk (k+1) (s+1) t) t :=
        (contDiff_const.mul ((Fk_contDiff (k+1) (s+1)).of_le (by exact_mod_cast le_top))).contDiffAt
      rw [iteratedDeriv_fun_add c1 c2, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
    rw [hadd]
    have t1 := (ih k s).const_mul (-(k:ℝ))
    have t2 := (ih (k+1) (s+1)).const_mul s
    have := t1.add t2
    have hval : -(k:ℝ) * (if n = 0 ∧ k = 0 then 1 else 0) + s * (if n = 0 ∧ k + 1 = 0 then 1 else 0) =
        (if n + 1 = 0 ∧ k = 0 then (1:ℝ) else 0) := by
      by_cases hk : k = 0 <;> simp [hk]
    rw [hval] at this
    exact this
end Formalism.FourierDecayAlt.P.LEx1
