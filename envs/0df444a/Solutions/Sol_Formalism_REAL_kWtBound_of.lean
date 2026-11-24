-- Prove2me | solution 1 for Formalism.REAL.kWtBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:44:07.356448+00:00
-- url     : https://prove2.me/submissions/e67e2c21-c777-4242-9a34-7ff4239665a9

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantOrthogonalInf
import Theorems.Thm_Formalism_REAL_inner_compactCasimir_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (hc : KCasSpan) : KWtBound := by
  intro V _ _ n ε F μ ν x y hr hu hx hy hy0 hν
  have h1 := hc V n ε F μ x hr hx y hy
  have h2 := inner_compactCasimir_self ε F hu y
  rw [h1, inner_smul_right, inner_self_eq_norm_sq_to_K] at h2
  have h3 : ckv ε μ * ‖y‖ ^ 2 = ∑ a, ∑ b, (if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ) := by
    apply Complex.ofReal_injective
    push_cast at h2 ⊢
    exact h2
  have h4 : nsq ν * ‖y‖ ^ 2 ≤ ∑ a, ∑ b, (if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ) := by
    unfold nsq dot
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    calc ν a * ν a * ‖y‖ ^ 2 = (if ε a = ε a then ‖F a a y‖ ^ 2 else 0 : ℝ) := by
          rw [if_pos rfl, hν a, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
          ring
      _ ≤ ∑ b, (if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ) :=
          Finset.single_le_sum (f := fun b => (if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ))
            (fun b _ => by split_ifs <;> positivity) (Finset.mem_univ a)
  have hpos : 0 < ‖y‖ ^ 2 := by positivity
  exact le_of_mul_le_mul_right (h4.trans h3.ge) hpos
end Formalism.REAL
