-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.thetaBasic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:03:31.596037+00:00
-- url     : https://prove2.me/submissions/5109ee9b-3bda-4167-b344-c31d2f13935c

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_thetaBasic_trace_star
import Theorems.Thm_Formalism_HermitianLatticesTheory_thetaBasic_eqv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.K
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : ThetaBasic := by
  intro K V _ _ _ _ _ _ _ h hh L γ τ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    unfold thetaL
    refine Eq.trans ?_ ((Equiv.addRight (⟨l, hl⟩ : L)).tsum_eq _)
    refine tsum_congr fun x => ?_
    simp only [Equiv.coe_addRight, Submodule.coe_add]
    rw [show γ + l + (x : V) = γ + ((x : V) + l) by abel]
  · unfold thetaL
    refine Eq.trans ?_ ((Equiv.neg L).tsum_eq _)
    refine tsum_congr fun x => ?_
    simp only [Equiv.neg_apply, Submodule.coe_neg]
    rw [show -γ + (x : V) = -(γ + -(x : V)) by abel]
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
  · intro g hg
    have hg' : ∀ x y, h (g x) (g y) = h x y := hg
    unfold thetaL
    rw [← (thetaBasic_eqv g L).tsum_eq]
    refine tsum_congr fun x => ?_
    rw [thetaBasic_eqv_apply, ← map_add, hg']
  · intro hev hdual
    unfold thetaL
    rw [← tsum_mul_left]
    refine tsum_congr fun x => ?_
    obtain ⟨m, hm⟩ := hev x x.2
    obtain ⟨n, hn⟩ := hdual x x.2
    have h1 : h (x : V) γ = star (h γ x) := (hh.eq γ x).symm
    have hx : Algebra.trace ℚ K (h (γ + x) (γ + x)) =
        Algebra.trace ℚ K (h γ γ) + 2 * ((n : ℚ) + m) := by
      simp only [map_add, LinearMap.add_apply, h1, thetaBasic_trace_star, hn, hm]
      ring
    rw [hx, ← Complex.exp_add]
    set T0 : ℂ := ((Algebra.trace ℚ K (h γ γ) : ℚ) : ℂ)
    have : (Real.pi : ℂ) * Complex.I * (τ + 1) * (((Algebra.trace ℚ K (h γ γ) + 2 * ((n : ℚ) + m) : ℚ)) : ℂ)
        = (Real.pi * Complex.I * T0 + Real.pi * Complex.I * τ *
          (((Algebra.trace ℚ K (h γ γ) + 2 * ((n : ℚ) + m) : ℚ)) : ℂ)) +
          ((n + m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      simp only [T0]; push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · intro n γs T g hg
    have hg' : ∀ x y, h (g x) (g y) = h x y := hg
    unfold thetaN
    rw [← (Equiv.piCongrRight fun _ : Fin n => thetaBasic_eqv g L).tsum_eq]
    refine tsum_congr fun x => ?_
    simp only [Equiv.piCongrRight_apply, Pi.map_apply, thetaBasic_eqv_apply, ← map_add, hg']
  · intro T
    unfold thetaN thetaL
    rw [← (Equiv.funUnique (Fin 1) L).symm.tsum_eq]
    refine tsum_congr fun x => ?_
    simp only [Equiv.funUnique_symm_apply, Fin.sum_univ_one]
    congr 1
    simp [uniqueElim_const]
    ring
end Formalism.HermitianLatticesTheory
