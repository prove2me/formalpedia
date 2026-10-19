-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.antisymmetric_matrix_energy_add_cross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/1d1f736b-91d8-4195-a453-f8590f008f93

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedDolbeaultBochnerIdentity
open Set MeasureTheory Filter
open EqualitySaturatingKillingPaths
open scoped BigOperators ENNReal ComplexConjugate
namespace Ehrhart.WeightedDolbeaultBochnerIdentity
theorem _root_.solution {n : ℕ}
    (A : Fin n → Fin n → ℂ) :
    (∑ i : Fin n, ∑ j : Fin n,
      (A i j - A j i) * conj (A i j - A j i)) / 2 +
      (∑ i : Fin n, ∑ j : Fin n,
        A i j * conj (A j i)) =
      ∑ i : Fin n, ∑ j : Fin n,
        A i j * conj (A i j) := by
  have hdiag :
      (∑ i : Fin n, ∑ j : Fin n,
        A j i * conj (A j i)) =
      ∑ i : Fin n, ∑ j : Fin n,
        A i j * conj (A i j) := by
    rw [Finset.sum_comm]
  have hcross :
      (∑ i : Fin n, ∑ j : Fin n,
        A j i * conj (A i j)) =
      ∑ i : Fin n, ∑ j : Fin n,
        A i j * conj (A j i) := by
    rw [Finset.sum_comm]
  have hexpand :
      (∑ i : Fin n, ∑ j : Fin n,
        (A i j - A j i) * conj (A i j - A j i)) =
      (∑ i : Fin n, ∑ j : Fin n,
        A i j * conj (A i j)) -
      (∑ i : Fin n, ∑ j : Fin n,
        A i j * conj (A j i)) -
      (∑ i : Fin n, ∑ j : Fin n,
        A j i * conj (A i j)) +
      (∑ i : Fin n, ∑ j : Fin n,
        A j i * conj (A j i)) := by
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n,
        (A i j * conj (A i j) -
          A i j * conj (A j i) -
          A j i * conj (A i j) +
          A j i * conj (A j i)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [map_sub]
        ring
      _ = _ := by
        simp_rw [Finset.sum_add_distrib,
          Finset.sum_sub_distrib]
  rw [hexpand, hdiag, hcross]
  ring
end Ehrhart.WeightedDolbeaultBochnerIdentity
