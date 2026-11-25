-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.OnPage.dfx_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:43:30.365736+00:00
-- url     : https://prove2.me/submissions/7d1c29d1-ade0-4fa0-b8c7-4eb14d541e04

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONPage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.L2.Indef.Tree.OnPage
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}
namespace Formalism.L2.Indef.Tree.OnPage
theorem _root_.solution (DF x k f m b T de2 PP D C2 : ℝ) (hDF0 : 0 ≤ DF) (hPP : 1 ≤ PP) (hD : 1 ≤ D)
    (hT : PP ^ 4 * D ^ 3 * k * f * x ≤ T * m * de2) (hde0 : 0 ≤ de2) (hde1 : de2 ≤ 1)
    (hZ3 : T * DF ≤ 3 * C2 * k * f * b) (hC2 : 0 ≤ C2) (hk : 0 < k) (hf : 0 < f) (hx0 : 0 ≤ x)
    (hm0 : 0 ≤ m) (hb0 : 0 ≤ b) : DF * x ≤ 3 * C2 * m * b := by
  have hQ : 1 ≤ PP ^ 4 * D ^ 3 := by
    have h1' : 1 ≤ PP ^ 4 := one_le_pow₀ hPP
    have h2' : 1 ≤ D ^ 3 := one_le_pow₀ hD
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ PP ^ 4 * D ^ 3 := mul_le_mul h1' h2' (by norm_num) (by linarith)
  have hkfx : 0 ≤ k * f * x := mul_nonneg (mul_nonneg hk.le hf.le) hx0
  have e1 : DF * (k * f * x) ≤ DF * (PP ^ 4 * D ^ 3 * k * f * x) := by
    apply mul_le_mul_of_nonneg_left _ hDF0
    calc k * f * x = 1 * (k * f * x) := by ring
      _ ≤ (PP ^ 4 * D ^ 3) * (k * f * x) := mul_le_mul_of_nonneg_right hQ hkfx
      _ = PP ^ 4 * D ^ 3 * k * f * x := by ring
  have e2 : DF * (PP ^ 4 * D ^ 3 * k * f * x) ≤ DF * (T * m * de2) := mul_le_mul_of_nonneg_left hT hDF0
  have e4 : (T * DF) * (m * de2) ≤ (3 * C2 * k * f * b) * (m * de2) :=
    mul_le_mul_of_nonneg_right hZ3 (mul_nonneg hm0 hde0)
  have hK0 : 0 ≤ 3 * C2 * k * f * b := by positivity
  have hmd : m * de2 ≤ m := by
    calc m * de2 ≤ m * 1 := mul_le_mul_of_nonneg_left hde1 hm0
      _ = m := by ring
  have e5 : (3 * C2 * k * f * b) * (m * de2) ≤ (3 * C2 * k * f * b) * m := mul_le_mul_of_nonneg_left hmd hK0
  have hkf : 0 < k * f := mul_pos hk hf
  have e6 : (k * f) * (DF * x) ≤ (k * f) * (3 * C2 * m * b) := by
    have a : (k * f) * (DF * x) = DF * (k * f * x) := by ring
    have a' : DF * (T * m * de2) = (T * DF) * (m * de2) := by ring
    have a'' : (k * f) * (3 * C2 * m * b) = (3 * C2 * k * f * b) * m := by ring
    rw [a, a'']
    rw [a'] at e2
    linarith
  exact le_of_mul_le_mul_left e6 hkf
end Formalism.L2.Indef.Tree.OnPage
