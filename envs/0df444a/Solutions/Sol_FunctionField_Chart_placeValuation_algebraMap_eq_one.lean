-- Prove2me | solution 1 for FunctionField.Chart.placeValuation_algebraMap_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T14:32:24.728555+00:00
-- url     : https://prove2.me/submissions/9cd985e1-8df1-419b-b939-c89f92ab964b

import Mathlib
import Definitions.Def_RiemannRoch_Places
/-
Contains code from riemann-roch-function-fields
(https://github.com/vaca22/riemann-roch-function-fields, commit dbca5bee),
Copyright (c) 2026 Guanghao Li, released under the Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
Modified: ported to Lean v4.33.1 / Mathlib 0df444a (module headers converted, some proofs
adapted to this Mathlib, a few names qualified, `picTorsor` omitted; statements unchanged), then
split into prove2.me definitions and theorems, with comments removed.
-/
set_option linter.style.haveILetI false
open scoped nonZeroDivisors Polynomial RatFunc WithZero
open FunctionField
variable (k K : Type*) [Field k] [Field K]
open MonoidWithZeroHom
open FunctionField.Chart
attribute [local instance] FunctionField.Chart.instDecidableEqRatFuncRiemannRoch
variable [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
variable [Algebra k K] [IsScalarTower k k[X] K]
namespace FunctionField.Chart
theorem _root_.solution (v : PlaceA k K) (c : kˣ) :
    placeValuation k K v (algebraMap k K (c : k)) = 1 := by
  have hc_le := placeValuation_algebraMap_le_one k K v (c : k)
  have hc_inv_le := placeValuation_algebraMap_le_one k K v ((c⁻¹ : kˣ) : k)
  have hmap_ne : placeValuation k K v (algebraMap k K (c : k)) ≠ 0 := by
    rw [map_ne_zero]
    exact (map_ne_zero (algebraMap k K)).2 c.ne_zero
  have hmap_pos : 0 < placeValuation k K v (algebraMap k K (c : k)) :=
    WithZero.pos_iff_ne_zero.2 hmap_ne
  have hinv_le : (placeValuation k K v (algebraMap k K (c : k)))⁻¹ ≤ 1 := by
    simpa using hc_inv_le
  exact le_antisymm hc_le ((inv_le_one₀ hmap_pos).1 hinv_le)
end FunctionField.Chart
