-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.geom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:45.367844+00:00
-- url     : https://prove2.me/submissions/8e0842a5-59b0-47d3-8e80-34ab5510f2a0

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7
namespace Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
theorem _root_.solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X) (t : ℂ) :
    (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) * geoS X t = t ^ n • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hnil : ∀ k : ℕ, ∀ i j : Fin n, (j : ℕ) < i + k → (X ^ k) i j = 0 := by
    intro k
    induction k with
    | zero =>
      intro i j hij
      rw [pow_zero, Matrix.one_apply_ne]
      intro h; rw [h] at hij; omega
    | succ k ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : (l : ℕ) < i + k
      · rw [ih i l hl, zero_mul]
      · rw [hX l j (by rw [Fin.le_def]; omega), mul_zero]
  have hXn : X ^ n = 0 := by
    ext i j
    have hj := j.isLt
    simp [hnil n i j (by omega)]
  have hc : Commute (-X) (t • (1 : Matrix (Fin n) (Fin n) ℂ)) := (Commute.one_right _).smul_right t
  have h := hc.mul_geom_sum₂ n
  have hS : ∑ i ∈ Finset.range n, (-X) ^ i * (t • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (n - 1 - i) = geoS X t := by
    unfold geoS
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_pow, one_pow, Matrix.mul_smul, mul_one]
  rw [hS, smul_pow, one_pow, neg_pow, hXn, mul_zero, zero_sub] at h
  have e : t • (1 : Matrix (Fin n) (Fin n) ℂ) + X = -(-X - t • 1) := by rw [neg_sub, sub_neg_eq_add]
  rw [e, neg_mul, h, neg_neg]
end Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
