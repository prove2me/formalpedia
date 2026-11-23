-- Prove2me | solution 1 for Formalism.DivisionValues.third_complement_final_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:59.762372+00:00
-- url     : https://prove2.me/submissions/172fe31a-be71-472d-aa76-a6fb61b66093

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open PlaceSumConjugation
namespace Formalism.DivisionValues
theorem _root_.solution (C0 c a La m B0 f b L S Sc η N k w'' b' Δ tt P1 P1' MM TTm cPl : ℝ)
    (hB0 : B0 = f * m * b * L) (hf : 1 ≤ f) (hm : 1 ≤ m) (hL1 : 1 ≤ L) (hb : 0 ≤ b)
    (hc0 : 0 ≤ c) (ha : 0 ≤ a) (hLLa : L ≤ La) (hLa3 : La ≤ 3 * L) (hk : 1 ≤ k) (hN : 1 ≤ N)
    (hS : 0 ≤ S) (hSc : Sc ≤ 3 * S) (htt : 0 ≤ tt) (hη : 0 ≤ η) (hb' : 0 ≤ b')
    (hcPl0 : 0 ≤ cPl) (hcPl : cPl ≤ f)
    (h3 : m ^ 3 * N ^ 2 * L ≤ b) (hkN : k * N ≤ b) (hkS : k * S ≤ w'')
    (hmη : m * (tt + 1) * η ≤ w'') (hNw : N * w'' ≤ b) (hmkb : m * k * b' ≤ a) (hmΔ : m * Δ ≤ a)
    (hP1 : |P1| ≤ C0 * (c * b' + cPl * (S + m * η + N)) * (C0 * m * L))
    (hP1' : |P1'| ≤ C0 * (c * b' + cPl * (S + m * η + N)) * (C0 * m * L))
    (hMM : |MM| ≤ m * (cPl * (2 * (k * Sc * La)) + c * (2 * (Δ * La))))
    (hT : |TTm| ≤ m * (C0 * (f * m ^ 2 * N ^ 2)) * (C0 * m * L)) :
    |P1 - P1' + MM + TTm| ≤ (7 * C0 ^ 2 + 18) * (c * a * La + m * B0) := by
  subst hB0
  have hm0 : 0 ≤ m := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hLa0 : 0 ≤ La := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hkS0 : 0 ≤ k * S := mul_nonneg hk0 hS
  have hw0 : 0 ≤ w'' := le_trans hkS0 hkS
  have hw1 : w'' ≤ b := by
    have := mul_nonneg hw0 (sub_nonneg.2 hN); linarith
  have hS1 : S ≤ w'' := by
    have := mul_nonneg hS (sub_nonneg.2 hk); linarith
  have hmη1 : m * η ≤ w'' := by
    have := mul_nonneg (mul_nonneg hm0 htt) hη; linarith
  have hN1 : N ≤ b := by
    have := mul_nonneg hN0 (sub_nonneg.2 hk); linarith
  have hmη0 : 0 ≤ m * η := mul_nonneg hm0 hη
  have hsum : S + m * η + N ≤ 3 * b := by linarith
  have hmb' : m * b' ≤ a := by
    have := mul_nonneg (mul_nonneg hm0 hb') (sub_nonneg.2 hk); linarith
  have hc1 : c * (m * b') ≤ c * a := mul_le_mul_of_nonneg_left hmb' hc0
  have hc2 : cPl * (S + m * η + N) ≤ f * (3 * b) :=
    le_trans (mul_le_mul_of_nonneg_left hsum hcPl0)
      (mul_le_mul_of_nonneg_right hcPl (by linarith))
  have hca : 0 ≤ c * a := mul_nonneg hc0 ha
  have hcaL : c * a * L ≤ c * a * La := mul_le_mul_of_nonneg_left hLLa hca
  have hmLX : m * L * (c * b' + cPl * (S + m * η + N)) ≤ c * a * La + 3 * (f * m * b * L) := by
    have g1 := mul_le_mul_of_nonneg_left hc1 hL0
    have g2 := mul_le_mul_of_nonneg_left hc2 (mul_nonneg hm0 hL0)
    linarith
  have hP1b : |P1| ≤ C0 ^ 2 * (c * a * La + 3 * (f * m * b * L)) :=
    calc |P1| ≤ C0 * (c * b' + cPl * (S + m * η + N)) * (C0 * m * L) := hP1
      _ = C0 ^ 2 * (m * L * (c * b' + cPl * (S + m * η + N))) := by ring
      _ ≤ C0 ^ 2 * (c * a * La + 3 * (f * m * b * L)) :=
        mul_le_mul_of_nonneg_left hmLX (sq_nonneg C0)
  have hP1'b : |P1'| ≤ C0 ^ 2 * (c * a * La + 3 * (f * m * b * L)) :=
    calc |P1'| ≤ C0 * (c * b' + cPl * (S + m * η + N)) * (C0 * m * L) := hP1'
      _ = C0 ^ 2 * (m * L * (c * b' + cPl * (S + m * η + N))) := by ring
      _ ≤ C0 ^ 2 * (c * a * La + 3 * (f * m * b * L)) :=
        mul_le_mul_of_nonneg_left hmLX (sq_nonneg C0)
  have t1 : cPl * (k * Sc * La) ≤ f * (k * (3 * S) * La) := by
    have a1 : k * Sc * La ≤ k * (3 * S) * La :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSc hk0) hLa0
    have a2 : 0 ≤ k * (3 * S) * La := mul_nonneg (mul_nonneg hk0 (by linarith)) hLa0
    exact le_trans (mul_le_mul_of_nonneg_left a1 hcPl0) (mul_le_mul_of_nonneg_right hcPl a2)
  have t2 : k * S * La ≤ b * (3 * L) := mul_le_mul (le_trans hkS hw1) hLa3 hLa0 hb
  have t3 : m * f * (k * S * La) ≤ m * f * (b * (3 * L)) :=
    mul_le_mul_of_nonneg_left t2 (mul_nonneg hm0 hf0)
  have t4 : m * Δ * (c * La) ≤ a * (c * La) :=
    mul_le_mul_of_nonneg_right hmΔ (mul_nonneg hc0 hLa0)
  have t5 : m * (cPl * (k * Sc * La)) ≤ m * (f * (k * (3 * S) * La)) :=
    mul_le_mul_of_nonneg_left t1 hm0
  have hMMb : |MM| ≤ 2 * (c * a * La) + 18 * (f * m * b * L) := by
    rw [abs_le] at hMM ⊢
    constructor <;> linarith [hMM.1, hMM.2]
  have hTb : |TTm| ≤ C0 ^ 2 * (f * m * b * L) := by
    have u1 : f * m * (m ^ 3 * N ^ 2 * L) ≤ f * m * b :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg hf0 hm0)
    have u2 : f * m * b ≤ f * m * b * L := by
      have := mul_nonneg (mul_nonneg (mul_nonneg hf0 hm0) hb) (sub_nonneg.2 hL1); linarith
    calc |TTm| ≤ m * (C0 * (f * m ^ 2 * N ^ 2)) * (C0 * m * L) := hT
      _ = C0 ^ 2 * (f * m * (m ^ 3 * N ^ 2 * L)) := by ring
      _ ≤ C0 ^ 2 * (f * m * b * L) := mul_le_mul_of_nonneg_left (le_trans u1 u2) (sq_nonneg C0)
  have hB0' : 0 ≤ f * m * b * L := mul_nonneg (mul_nonneg (mul_nonneg hf0 hm0) hb) hL0
  have hcaLa : 0 ≤ c * a * La := mul_nonneg hca hLa0
  have q1 : 0 ≤ C0 ^ 2 * (c * a * La) := mul_nonneg (sq_nonneg C0) hcaLa
  have q2 : 0 ≤ (f * m * b * L) * (m - 1) := mul_nonneg hB0' (by linarith)
  have q3 : 0 ≤ C0 ^ 2 * ((f * m * b * L) * (m - 1)) := mul_nonneg (sq_nonneg C0) q2
  rw [abs_le] at hP1b hP1'b hMMb hTb ⊢
  constructor <;> linarith [hP1b.1, hP1b.2, hP1'b.1, hP1'b.2, hMMb.1, hMMb.2, hTb.1, hTb.2]
end Formalism.DivisionValues
