-- Prove2me | solution 1 for Formalism.L2.Th1.H.summable_gauss_of_discrete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:27:26.289346+00:00
-- url     : https://prove2.me/submissions/0bc14692-215b-4ff0-9f4c-100dcf7f4059

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaloisDescentSubspaces
import Theorems.Thm_Formalism_L2_Th1_H_exp_neg_le_factorial_div

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : AddSubgroup V) [hd : DiscreteTopology Λ] {a : ℝ} (ha : 0 < a) :
    Summable fun x : Λ => Real.exp (-a * ‖(x : V)‖ ^ 2) := by
  classical
  let L : Submodule ℤ V := AddSubgroup.toIntSubmodule Λ
  have : DiscreteTopology L := hd
  set n : ℕ := Module.finrank ℤ L + 1 with hn
  have hsum : Summable fun z : L => ‖z‖⁻¹ ^ (2 * n) :=
    ZLattice.summable_norm_pow_inv L (2 * n) (by omega)
  have hsum' : Summable fun x : Λ => ‖(x : V)‖⁻¹ ^ (2 * n) := hsum
  have hite : Summable fun x : Λ => if x = 0 then (1 : ℝ) else 0 := (hasSum_ite_eq (0 : Λ) (1 : ℝ)).summable
  refine Summable.of_nonneg_of_le (fun x => (Real.exp_pos _).le) (fun x => ?_)
    ((hsum'.mul_left ((n ! : ℝ) / a ^ n)).add hite)
  by_cases hx : x = 0
  · subst hx
    simp
  · have hx' : 0 < ‖(x : V)‖ := by
      rw [norm_pos_iff]
      exact fun h => hx (Subtype.ext h)
    have hs : 0 < a * ‖(x : V)‖ ^ 2 := by positivity
    have h1 := exp_neg_le_factorial_div hs n
    rw [if_neg hx, add_zero]
    calc Real.exp (-a * ‖(x : V)‖ ^ 2) = Real.exp (-(a * ‖(x : V)‖ ^ 2)) := by rw [neg_mul]
      _ ≤ (n ! : ℝ) / (a * ‖(x : V)‖ ^ 2) ^ n := h1
      _ = (n ! : ℝ) / a ^ n * ‖(x : V)‖⁻¹ ^ (2 * n) := by
          rw [mul_pow, ← pow_mul, inv_pow]
          field_simp
end Formalism.L2.Th1.H
