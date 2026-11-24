-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.fForm_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:27:18.872559+00:00
-- url     : https://prove2.me/submissions/a4c9e62a-6524-4559-b470-d38f6d7f1d67

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormAsm
import Theorems.Thm_Formalism_L2_SG_NormCut_pairSum_gam

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
theorem _root_.solution (U : Set I) (p : I → ℂ) (h0 : ∀ x, x ∉ U → p x = 0)
    (hr : ∀ x, ∀ w ∈ U, p (x * w) = p x * p w) (hn : ∀ w ∈ U, conj (p w) * p w = 1)
    (hU : (Nat.card U : ℂ) ≠ 0) (Gm : I → I → ℂ) :
    ∑ x : I, ∑ y : I, fForm p Gm x y =
      (Nat.card U : ℂ) ^ 2 * ∑ i, ∑ j, conj (gamOf U p (i * j⁻¹)) * Gm i j := by
  have hswap : ∀ (F : I → I → I → I → ℂ),
      ∑ x, ∑ y, ∑ i, ∑ j, F x y i j = ∑ i, ∑ j, ∑ x, ∑ y, F x y i j := by
    intro F
    calc ∑ x, ∑ y, ∑ i, ∑ j, F x y i j = ∑ x, ∑ i, ∑ j, ∑ y, F x y i j := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, ∑ x, ∑ y, F x y i j := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
  unfold fForm
  refine (hswap (fun x y i j => conj (p (x⁻¹ * i * y)) * p (x⁻¹ * j * y) * Gm i j)).trans ?_
  simp_rw [← Finset.sum_mul]
  simp_rw [pairSum_gam U p h0 hr hn hU]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end Formalism.L2.SG.NormCut
