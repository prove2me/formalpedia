-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.colSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:12:17.369005+00:00
-- url     : https://prove2.me/submissions/b2f0ae2a-a457-4fe7-9908-cce420348de3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore

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
namespace Formalism.L2.SG.NormCut
theorem _root_.solution {G : Type*} [Group G] [Fintype G] (U : Set G) (p : G → ℂ) (h0 : ∀ x, x ∉ U → p x = 0)
    (hr : ∀ x, ∀ w ∈ U, p (x * w) = p x * p w) (hn : ∀ w ∈ U, conj (p w) * p w = 1) (i j : G) :
    ∑ s : G, ∑ s' : G, conj (p (s⁻¹ * i * s')) * p (s⁻¹ * j * s') =
      (Nat.card U : ℂ) * ∑ s : G, conj (p (s⁻¹ * (i * j⁻¹) * s)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft (j⁻¹ * s))]
  simp only [Equiv.coe_mulLeft]
  have h1 : ∀ w : G, conj (p (s⁻¹ * i * (j⁻¹ * s * w))) * p (s⁻¹ * j * (j⁻¹ * s * w)) =
      if w ∈ U then conj (p (s⁻¹ * (i * j⁻¹) * s)) else 0 := by
    intro w
    have hw : s⁻¹ * j * (j⁻¹ * s * w) = w := by group
    have hw2 : s⁻¹ * i * (j⁻¹ * s * w) = s⁻¹ * (i * j⁻¹) * s * w := by group
    rw [hw, hw2]
    split_ifs with h
    · rw [hr _ w h, map_mul, mul_assoc, hn w h, mul_one]
    · rw [h0 w h, mul_zero]
  simp only [h1]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.univ.filter fun w => w ∈ U).card : ℂ) = (Nat.card U : ℂ) := by
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
    congr 2
    ext w
    simp
  rw [hc]
end Formalism.L2.SG.NormCut
