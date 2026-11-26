-- Prove2me | solution 1 for FourierJacobi.Algebra.normalized_closedCore_principal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:38.308861+00:00
-- url     : https://prove2.me/submissions/29d97beb-9613-4f5a-95d6-848c921d0703

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Theorems.Thm_FourierJacobi_Algebra_principal_cancellation

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
namespace FourierJacobi.Algebra
theorem _root_.solution (t a b d : K)
    (hc : poincare t ≠ 0) (hn₁ : n₁ t a b ≠ 0) (hn₂ : n₂ t a b ≠ 0)
    (hd₁ : d₁ t a b d ≠ 0) (hd₂ : d₂ t a b d ≠ 0)
    (ht : 1 - t ^ 2 ≠ 0)
    (hm : 1 - d * t ≠ 0) (hp : 1 + d * t ≠ 0)
    (him : 1 - t / d ≠ 0) (hip : 1 + t / d ≠ 0) :
    closedCore t a b d * principalNormalizer t a b d =
      satakeNumerator a b / ((1 + d * t) * (1 + t / d)) :=
  principal_cancellation t d (satakeNumerator a b) (n₁ t a b) (n₂ t a b)
    (d₁ t a b d) (d₂ t a b d) hc hn₁ hn₂ hd₁ hd₂ ht hm hp him hip
end FourierJacobi.Algebra
