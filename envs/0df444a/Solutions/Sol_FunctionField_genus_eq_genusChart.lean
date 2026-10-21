-- Prove2me | solution 1 for FunctionField.genus_eq_genusChart
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T14:35:10.861788+00:00
-- url     : https://prove2.me/submissions/9ebd9c16-20c3-45a1-9c31-5dda8d92af3f

import Mathlib
import Definitions.Def_RiemannRoch_WeilDifferentials
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
section
section
open scoped nonZeroDivisors Polynomial RatFunc WithZero
noncomputable section
namespace FunctionField
open Chart
variable (k K : Type*) [Field k] [Field K]
  [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
attribute [local instance] FunctionField.instDecidableEqRatFuncCoordinateFreeDivisor
namespace Place
attribute [local instance] FunctionField.Place.finiteVspTower
attribute [local instance] FunctionField.Place.infiniteVspTower
end Place
namespace Divisor
omit [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
    [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
    [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_add (D E : Divisor k K) : deg k K (D + E) = deg k K D + deg k K E := by
  classical
  simp [deg, Finsupp.sum_add_index, add_mul]
theorem deg_equivChart (D : DivisorA k K) :
    deg k K (divisorEquivChart k K D) = Chart.deg k K D := by
  classical
  induction D using Finsupp.induction with
  | zero => simp [deg, Chart.deg, divisorEquivChart]
  | single_add a b f ha hb ih =>
      rw [map_add, deg_add, Chart.deg_add, ih]
      congr 1
      simp [deg, Chart.deg, divisorEquivChart, Finsupp.domCongr_apply,
        Finsupp.equivMapDomain_single, placeDegree_eq]
end Divisor
end FunctionField
end
end
end
section
section
open scoped nonZeroDivisors Polynomial RatFunc WithZero
noncomputable section
namespace FunctionField
open Chart
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
namespace memRRspace
variable {k K} {D : Divisor k K}
end memRRspace
variable [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]
omit [IsFullConstantField k K] in
theorem memRRspace_equivChart (D : Divisor k K) (f : K) :
    memRRspace k K D f ↔
      Chart.memRRspace k K ((divisorEquivChart k K).symm D) f := by
  constructor
  · intro hf w
    have hv := hf (chartToPlace k K w)
    rw [placeValuation_eq] at hv
    simpa [divisorEquivChart, Finsupp.domCongr_apply] using hv
  · intro hf v
    let w := (chartToPlace k K).symm v
    have hw := hf w
    rw [← placeValuation_eq] at hw
    simpa [w, divisorEquivChart, Finsupp.domCongr_apply] using hw
omit [IsFullConstantField k K] in
theorem RRspace_eq_chart (D : Divisor k K) :
    RRspace k K D = Chart.RRspace k K ((divisorEquivChart k K).symm D) := by
  ext f
  exact memRRspace_equivChart k K D f
omit [IsFullConstantField k K] in
theorem ell_eq_chart (D : Divisor k K) :
    ell k K D = Chart.ell k K ((divisorEquivChart k K).symm D) := by
  rw [ell, Chart.ell, RRspace_eq_chart k K D]
omit [IsFullConstantField k K] in
@[simp]
theorem Divisor.chart_deg (D : Divisor k K) :
    Chart.deg k K ((divisorEquivChart k K).symm D) = D.deg := by
  have h := Divisor.deg_equivChart k K ((divisorEquivChart k K).symm D)
  simpa using h.symm
omit [IsFullConstantField k K] in
theorem defect_eq_chart (D : Divisor k K) :
    defect k K D = Chart.defect k K ((divisorEquivChart k K).symm D) := by
  rw [defect, Chart.defect, ell_eq_chart, Divisor.chart_deg]
section Canonical
variable {W : Divisor k K} (hW : IsCanonical k K W)
include hW
end Canonical
end FunctionField
end
end
end
open scoped nonZeroDivisors Polynomial RatFunc WithZero
open FunctionField
open Chart
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
variable [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]
namespace FunctionField
theorem _root_.solution : genus k K = Chart.genus k K := by
  let S : Set ℤ := {d | ∃ D : Divisor k K, defect k K D = d}
  have hS : S.Nonempty := ⟨defect k K 0, ⟨0, rfl⟩⟩
  have hub : ∀ d ∈ S, d ≤ (Chart.genus k K : ℤ) := by
    rintro d ⟨D, rfl⟩
    rw [defect_eq_chart]
    exact Chart.defect_le k K _
  obtain ⟨E, hE⟩ := Chart.exists_defect_eq (k := k) (K := K)
  have happ : ∀ z < (Chart.genus k K : ℤ), ∃ d ∈ S, z < d := by
    intro z hz
    refine ⟨defect k K (divisorEquivChart k K E), ⟨_, rfl⟩, ?_⟩
    rw [defect_eq_chart]
    simpa [hE] using hz
  have hsup : sSup S = (Chart.genus k K : ℤ) :=
    csSup_eq_of_forall_le_of_forall_lt_exists_gt hS hub happ
  rw [genus]
  change (sSup S).toNat = _
  rw [hsup]
  simp
end FunctionField
