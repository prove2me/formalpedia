-- Prove2me | solution 1 for FreyCurve.eight_mul_Psi2Sq_eval_reductionMod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/0b50d815-48a0-539f-b243-74f43c525461

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_FreyPackage
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Theorems.Thm_FreyPackage_freyCurveInt_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyCurve_eight_mul_Psi2Sq_eval_reductionMod

open Polynomial WeierstrassCurve

namespace FreyCurve

private lemma freyCurveInt_b₂ (P : FreyPackage) :
    P.freyCurveInt.b₂ = P.b ^ P.p - P.a ^ P.p := by
  have key : (P.freyCurveInt.map (Int.castRingHom ℚ)).b₂ = ((P.b ^ P.p - P.a ^ P.p : ℤ) : ℚ) := by
    rw [FreyPackage.freyCurveInt_map]
    push_cast
    simp only [FreyPackage.freyCurve, WeierstrassCurve.b₂]; ring
  rw [map_b₂] at key
  simp only [eq_intCast] at key
  exact_mod_cast key

private lemma eight_mul_freyCurveInt_b₄ (P : FreyPackage) :
    8 * P.freyCurveInt.b₄ = -(P.a * P.b) ^ P.p := by
  have key : 8 * (P.freyCurveInt.map (Int.castRingHom ℚ)).b₄ = ((-(P.a * P.b) ^ P.p : ℤ) : ℚ) := by
    rw [FreyPackage.freyCurveInt_map]
    push_cast
    simp only [FreyPackage.freyCurve, WeierstrassCurve.b₄]; ring
  rw [map_b₄] at key
  simp only [eq_intCast] at key
  exact_mod_cast key

private lemma freyCurveInt_b₆ (P : FreyPackage) : P.freyCurveInt.b₆ = 0 := by
  have key : (P.freyCurveInt.map (Int.castRingHom ℚ)).b₆ = (0 : ℚ) := by
    rw [FreyPackage.freyCurveInt_map]
    simp [FreyPackage.freyCurve, WeierstrassCurve.b₆]
  rw [map_b₆] at key
  simp only [eq_intCast] at key
  exact_mod_cast key

theorem _root_.P2MW.S_FreyCurve_eight_mul_Psi2Sq_eval_reductionMod.solution (P : FreyPackage) {q : ℕ} [Fact q.Prime]
    (x : ZMod q) :
    8 * (((FreyPackage.freyCurveInt P).reductionMod q).Ψ₂Sq.eval x) =
      2 * x * (4 * x - ((P.a : ZMod q)) ^ P.p) * (4 * x + ((P.b : ZMod q)) ^ P.p) := by
  have hb₂ : (P.freyCurveInt.reductionMod q).b₂
      = ((P.b ^ P.p - P.a ^ P.p : ℤ) : ZMod q) := by
    rw [reductionMod, map_b₂, freyCurveInt_b₂]; simp only [eq_intCast]
  have hb₄ : (8 : ZMod q) * (P.freyCurveInt.reductionMod q).b₄
      = ((-(P.a * P.b) ^ P.p : ℤ) : ZMod q) := by
    rw [reductionMod, map_b₄]; simp only [eq_intCast]
    push_cast [← eight_mul_freyCurveInt_b₄]; ring
  have hb₆ : (P.freyCurveInt.reductionMod q).b₆ = 0 := by
    rw [reductionMod, map_b₆, freyCurveInt_b₆]; simp only [eq_intCast, Int.cast_zero]
  have hexp : ((P.freyCurveInt.reductionMod q).Ψ₂Sq.eval x)
      = 4 * x ^ 3 + (P.freyCurveInt.reductionMod q).b₂ * x ^ 2
        + 2 * (P.freyCurveInt.reductionMod q).b₄ * x
        + (P.freyCurveInt.reductionMod q).b₆ := by
    simp only [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  rw [hexp, hb₆, add_zero]
  have key : (8 : ZMod q) * (4 * x ^ 3 + (P.freyCurveInt.reductionMod q).b₂ * x ^ 2
      + 2 * (P.freyCurveInt.reductionMod q).b₄ * x)
      = 32 * x ^ 3 + 8 * (P.freyCurveInt.reductionMod q).b₂ * x ^ 2
        + 2 * ((8 : ZMod q) * (P.freyCurveInt.reductionMod q).b₄) * x := by ring
  rw [key, hb₂, hb₄]
  push_cast
  ring

end FreyCurve

end S_FreyCurve_eight_mul_Psi2Sq_eval_reductionMod
end P2MW
export P2MW.S_FreyCurve_eight_mul_Psi2Sq_eval_reductionMod (solution)
