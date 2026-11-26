-- Prove2me | solution 1 for FourierJacobi.Algebra.normalized_closedCore_special_negative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:38.927725+00:00
-- url     : https://prove2.me/submissions/d80befc8-bc29-42af-945b-971489f4e6b2

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Theorems.Thm_P2M_FourierJacobi_Algebra_special_negative_d__9d3a998530fe
import Theorems.Thm_P2M_FourierJacobi_Algebra_special_negative_d__a6d88199088c
import Theorems.Thm_FourierJacobi_Algebra_special_negative_cancellation

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
namespace FourierJacobi.Algebra
theorem _root_.solution (t a b : K)
    (ht₀ : t ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : poincare t ≠ 0) (hp : satakeNumerator a b ≠ 0)
    (hn₁ : n₁ t a b ≠ 0) (hn₂ : n₂ t a b ≠ 0)
    (hf : fourFactors a b (-t ^ 2) ≠ 0)
    (ht : 1 - t ^ 2 ≠ 0) (ht₄ : 1 - t ^ 4 ≠ 0) :
    closedCore t a b (-t) * specialNormalizer t a b (-1) = 1 := by
  unfold closedCore specialNormalizer specialTensorInverse piAdjointInverse
  rw [special_negative_d₁, special_negative_d₂ t a b ht₀ ha hb]
  simp only [neg_one_mul, sub_neg_eq_add]
  exact special_negative_cancellation t (satakeNumerator a b) (n₁ t a b)
    (n₂ t a b) (fourFactors a b (-t ^ 2)) hc hp hn₁ hn₂ hf ht ht₄
end FourierJacobi.Algebra
