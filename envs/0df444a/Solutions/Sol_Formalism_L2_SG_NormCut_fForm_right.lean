-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.fForm_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:17:51.897615+00:00
-- url     : https://prove2.me/submissions/423d8f30-a91c-4e99-a802-99856f0c90e4

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
theorem _root_.solution (U : Set I) (p : I → ℂ) (hr : ∀ x, ∀ u ∈ U, p (x * u) = p x * p u)
    (hn : ∀ u ∈ U, conj (p u) * p u = 1) (Gm : I → I → ℂ) (b : I)
    (hG : ∀ i j, Gm (i * b⁻¹) (j * b⁻¹) = Gm i j) (x y w : I) (hw : w ∈ U) :
    fForm p Gm x (b * y * w) = fForm p Gm x y := by
  unfold fForm
  rw [← Equiv.sum_comp (Equiv.mulRight b⁻¹)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulRight b⁻¹)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.coe_mulRight, hG]
  rw [show x⁻¹ * (i * b⁻¹) * (b * y * w) = x⁻¹ * i * y * w by group,
    show x⁻¹ * (j * b⁻¹) * (b * y * w) = x⁻¹ * j * y * w by group, hr _ w hw, hr _ w hw, map_mul]
  linear_combination (conj (p (x⁻¹ * i * y)) * p (x⁻¹ * j * y) * Gm i j) * hn w hw
end Formalism.L2.SG.NormCut
