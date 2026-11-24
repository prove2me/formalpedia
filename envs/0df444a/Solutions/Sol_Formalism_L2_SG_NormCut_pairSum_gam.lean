-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.pairSum_gam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:18:29.862338+00:00
-- url     : https://prove2.me/submissions/a5a6c4a8-9b99-4587-930d-e8f02273d0b5

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
theorem _root_.solution (U : Set I) (p : I → ℂ) (h0 : ∀ x, x ∉ U → p x = 0)
    (hr : ∀ x, ∀ w ∈ U, p (x * w) = p x * p w) (hn : ∀ w ∈ U, conj (p w) * p w = 1)
    (hU : (Nat.card U : ℂ) ≠ 0) (i j : I) :
    ∑ s : I, ∑ s' : I, conj (p (s⁻¹ * i * s')) * p (s⁻¹ * j * s') =
      (Nat.card U : ℂ) ^ 2 * conj (gamOf U p (i * j⁻¹)) := by
  have hU' : ∀ x : I, ∑ t : I, conj (p (x * t)) * p t = (Nat.card U : ℂ) * conj (p x) := by
    intro x
    have e : ∀ t, conj (p (x * t)) * p t = if t ∈ U then conj (p x) else 0 := by
      intro t
      split_ifs with ht
      · rw [hr x t ht, map_mul, mul_assoc, hn t ht, mul_one]
      · rw [h0 t ht, mul_zero]
    simp_rw [e]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have step : ∀ s : I, ∑ s' : I, conj (p (s⁻¹ * i * s')) * p (s⁻¹ * j * s') =
      (Nat.card U : ℂ) * conj (p (s⁻¹ * (i * j⁻¹) * s)) := by
    intro s
    rw [← Equiv.sum_comp (Equiv.mulLeft (j⁻¹ * s)), ← hU' (s⁻¹ * (i * j⁻¹) * s)]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Equiv.coe_mulLeft]
    rw [show s⁻¹ * i * (j⁻¹ * s * t) = s⁻¹ * (i * j⁻¹) * s * t by group,
      show s⁻¹ * j * (j⁻¹ * s * t) = t by group]
  simp_rw [step]
  rw [← Finset.mul_sum]
  have hsw : ∑ s : I, conj (p (s⁻¹ * (i * j⁻¹) * s)) = ∑ y : I, conj (p (y * (i * j⁻¹) * y⁻¹)) := by
    rw [← Equiv.sum_comp (Equiv.inv I)]
    simp
  rw [hsw]
  unfold gamOf
  rw [map_mul, map_inv₀, map_natCast, map_sum]
  field_simp
end Formalism.L2.SG.NormCut
