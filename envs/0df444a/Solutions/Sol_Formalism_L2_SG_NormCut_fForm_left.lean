-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.fForm_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:17:49.668907+00:00
-- url     : https://prove2.me/submissions/d211e32f-ff21-444e-8a59-29eb27f9d101

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormAsm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NormCut
variable {I : Type*} [Group I] [Fintype I]
namespace Formalism.L2.SG.NormCut
theorem _root_.solution (U : Set I) (p : I → ℂ) (hl : ∀ x, ∀ u ∈ U, p (u * x) = p u * p x)
    (hn : ∀ u ∈ U, conj (p u) * p u = 1) (Gm : I → I → ℂ) (b : I)
    (hG : ∀ i j, Gm (b * i) (b * j) = Gm i j) (x y w : I) (hw : w ∈ U) :
    fForm p Gm (b * x * w) y = fForm p Gm x y := by
  have hq : ∀ m, p (w⁻¹ * m) = conj (p w) * p m := by
    intro m
    have e := hl (w⁻¹ * m) w hw
    rw [mul_inv_cancel_left] at e
    rw [e, ← mul_assoc, hn w hw, one_mul]
  unfold fForm
  rw [← Equiv.sum_comp (Equiv.mulLeft b)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft b)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.coe_mulLeft, hG]
  rw [show (b * x * w)⁻¹ * (b * i) * y = w⁻¹ * (x⁻¹ * i * y) by group,
    show (b * x * w)⁻¹ * (b * j) * y = w⁻¹ * (x⁻¹ * j * y) by group, hq, hq, map_mul, Complex.conj_conj]
  linear_combination (conj (p (x⁻¹ * i * y)) * p (x⁻¹ * j * y) * Gm i j) * hn w hw
end Formalism.L2.SG.NormCut
