-- Prove2me | solution 1 for Ehrhart.Geometry.interior_integerPoint_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/a4482806-0fe6-4489-9a8c-1a6a96dfb114

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_Geometry_mem_interior_centeredSimplex_iff

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.Geometry
open Set MeasureTheory
open scoped BigOperators
namespace Ehrhart.Geometry
theorem _root_.solution {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℤ)
    (hz : integerPoint n z ∈
      interior (centeredSimplex n)) :
    z = 0 := by
  classical
  have hstrict := (mem_interior_centeredSimplex_iff hn).mp hz
  have hstrict_coords : ∀ i, -(1 : ℝ) < (z i : ℝ) := by
    intro i
    simpa [integerPoint] using hstrict.1 i
  have hstrict_sum : (∑ i, (z i : ℝ)) < 1 := by
    simpa [integerPoint] using hstrict.2
  have hnonneg : ∀ i, (0 : ℤ) ≤ z i := by
    intro i
    have hi : (-1 : ℤ) < z i := by
      exact_mod_cast hstrict_coords i
    have hi' : (-1 : ℤ) + 1 ≤ z i := (Int.add_one_le_iff).mpr hi
    simpa using hi'
  have hsum_lt : (∑ i, z i) < (1 : ℤ) := by
    exact_mod_cast hstrict_sum
  have hsum_le : (∑ i, z i) ≤ (0 : ℤ) := by
    apply (Int.lt_add_one_iff).mp
    simpa using hsum_lt
  have hsum_nonneg : (0 : ℤ) ≤ ∑ i, z i :=
    Finset.sum_nonneg fun i _ => hnonneg i
  have hsum_zero : (∑ i, z i) = (0 : ℤ) :=
    le_antisymm hsum_le hsum_nonneg
  funext i
  have hi_le : z i ≤ ∑ j, z j :=
    Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  have hi_zero : z i = (0 : ℤ) :=
    le_antisymm (hsum_zero ▸ hi_le) (hnonneg i)
  simpa using hi_zero
end Ehrhart.Geometry
