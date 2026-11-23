-- Prove2me | solution 1 for Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower.t_odd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:44.411316+00:00
-- url     : https://prove2.me/submissions/7cedceb6-68dd-41bd-8bb9-5a2e7508ed73

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SignsFromTrianglesSquares
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareEqDiagOfQuadraticEven

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.WeilRepresentation Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower
open Formalism.HermitianLattices.WeilRepresentation Formalism.HermitianLattices.IntegralLatticeDensity
namespace Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower
theorem _root_.solution : OddOrderDetermined := by
  intro G H _ _ _ Φ Φ' B hodd h h' he he' x
  let c : Multiplicative G →* H :=
    { toFun := fun g => Φ (Multiplicative.toAdd g) * (Φ' (Multiplicative.toAdd g))⁻¹
      map_one' := by
        have a := h 0 0; have a' := h' 0 0
        simp only [add_zero] at a a'
        have : Φ 0 * B 0 0 = 1 := by
          have := a; rw [mul_assoc] at this; exact (mul_eq_left.mp this.symm)
        have t' : Φ' 0 * B 0 0 = 1 := by
          have := a'; rw [mul_assoc] at this; exact (mul_eq_left.mp this.symm)
        show Φ 0 * (Φ' 0)⁻¹ = 1
        rw [mul_inv_eq_one]; exact mul_right_cancel (this.trans t'.symm)
      map_mul' := by
        intro g g'
        show Φ (_ + _) * (Φ' (_ + _))⁻¹ = _
        rw [h, h']; simp only [mul_inv];
        rw [show ∀ a b c d e f : H, a * b * c * (d * e * f) = (a * d) * (b * e) * (c * f) from by
          intros; ac_rfl]
        simp }
  have hc2 : ∀ g, c g ^ 2 = 1 := by
    intro g
    have : c g⁻¹ = c g := by
      show Φ (-_) * (Φ' (-_))⁻¹ = Φ _ * (Φ' _)⁻¹
      rw [he, he']
    rw [pow_two]; nth_rewrite 2 [← this]; rw [← map_mul]; simp
  have hcn : ∀ g, c g ^ Fintype.card G = 1 := by
    intro g; rw [← map_pow]
    have : g ^ Fintype.card (Multiplicative G) = 1 := pow_card_eq_one
    have e : Fintype.card (Multiplicative G) = Fintype.card G := by simp
    rw [← e, this, map_one]
  obtain ⟨k, hk⟩ := hodd
  have : c (Multiplicative.ofAdd x) = 1 := by
    have a := hcn (Multiplicative.ofAdd x)
    rw [hk, pow_succ, pow_mul, hc2, one_pow, one_mul] at a; exact a
  exact mul_inv_eq_one.mp this
end Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower
