-- Prove2me | solution 1 for Erdos9796FiniteNine.circle_placement
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-10T07:08:34.795679+00:00
-- url     : https://prove2.me/submissions/dabbf8f4-1dad-4e7d-93ac-a4861ec89239

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_Erdos9796FiniteNine_N8Interface

section Batch3N9Unit046CirclePlacement
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace FiniteEndpointShell

theorem k4_at_v1
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    Erdos97.HasNEquidistantPointsAt 4 A S.triangle.v1 :=
  S.hK4 _ S.triangle.v1_mem
theorem k4_at_v2
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    Erdos97.HasNEquidistantPointsAt 4 A S.triangle.v2 :=
  S.hK4 _ S.triangle.v2_mem
theorem k4_at_v3
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    Erdos97.HasNEquidistantPointsAt 4 A S.triangle.v3 :=
  S.hK4 _ S.triangle.v3_mem
theorem n5_forced_m44
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment) :
    S.CP.C1.card = 4 ∧ S.CP.C2.card = 4 ∧ S.CP.C3.card = 4 := by
  have hC1ge : 4 ≤ S.CP.C1.card := by
    rcases S.k4_at_v1 with ⟨r, hr, hcard⟩
    exact le_trans hcard (Finset.card_le_card (hN4e.1 hr hcard))
  have hC2ge : 4 ≤ S.CP.C2.card := by
    rcases S.k4_at_v2 with ⟨r, hr, hcard⟩
    exact le_trans hcard (Finset.card_le_card (hN4e.2.1 hr hcard))
  have hC3ge : 4 ≤ S.CP.C3.card := by
    rcases S.k4_at_v3 with ⟨r, hr, hcard⟩
    exact le_trans hcard (Finset.card_le_card (hN4e.2.2 hr hcard))
  have hsum := S.hcapSum12
  omega

theorem exact_cap_class_at_v1
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment) :
    ∃ r : ℝ, 0 < r ∧
      A.filter (fun x => dist S.triangle.v1 x = r) = S.CP.C1 := by
  classical
  rcases S.k4_at_v1 with ⟨r, hr, hcard⟩
  let T : Finset ℝ² := A.filter (fun x => dist S.triangle.v1 x = r)
  have hTfour : 4 ≤ T.card := by
    simpa [T, triangle, Problem97.MEC.MoserTriangle.toStructural] using hcard
  have hsub : T ⊆ S.CP.C1 := hN4e.1 hr hTfour
  have hcap4 : S.CP.C1.card = 4 := (S.n5_forced_m44 hN4e).1
  have hcle : S.CP.C1.card ≤ T.card := by
    omega
  refine ⟨r, hr, ?_⟩
  exact Finset.eq_of_subset_of_card_le hsub hcle
theorem exact_cap_class_at_v2
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment) :
    ∃ r : ℝ, 0 < r ∧
      A.filter (fun x => dist S.triangle.v2 x = r) = S.CP.C2 := by
  classical
  rcases S.k4_at_v2 with ⟨r, hr, hcard⟩
  let T : Finset ℝ² := A.filter (fun x => dist S.triangle.v2 x = r)
  have hTfour : 4 ≤ T.card := by
    simpa [T, triangle, Problem97.MEC.MoserTriangle.toStructural] using hcard
  have hsub : T ⊆ S.CP.C2 := hN4e.2.1 hr hTfour
  have hcap4 : S.CP.C2.card = 4 := (S.n5_forced_m44 hN4e).2.1
  have hcle : S.CP.C2.card ≤ T.card := by
    omega
  refine ⟨r, hr, ?_⟩
  exact Finset.eq_of_subset_of_card_le hsub hcle
theorem exact_cap_class_at_v3
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment) :
    ∃ r : ℝ, 0 < r ∧
      A.filter (fun x => dist S.triangle.v3 x = r) = S.CP.C3 := by
  classical
  rcases S.k4_at_v3 with ⟨r, hr, hcard⟩
  let T : Finset ℝ² := A.filter (fun x => dist S.triangle.v3 x = r)
  have hTfour : 4 ≤ T.card := by
    simpa [T, triangle, Problem97.MEC.MoserTriangle.toStructural] using hcard
  have hsub : T ⊆ S.CP.C3 := hN4e.2.2 hr hTfour
  have hcap4 : S.CP.C3.card = 4 := (S.n5_forced_m44 hN4e).2.2
  have hcle : S.CP.C3.card ≤ T.card := by
    omega
  refine ⟨r, hr, ?_⟩
  exact Finset.eq_of_subset_of_card_le hsub hcle
theorem n6_equilateral_moser_triangle
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment) :
    dist S.triangle.v1 S.triangle.v2 = dist S.triangle.v2 S.triangle.v3 ∧
      dist S.triangle.v2 S.triangle.v3 = dist S.triangle.v3 S.triangle.v1 := by
  classical
  rcases S.exact_cap_class_at_v1 hN4e with ⟨r1, -, hC1⟩
  rcases S.exact_cap_class_at_v2 hN4e with ⟨r2, -, hC2⟩
  have hv2C1 : S.triangle.v2 ∈ A.filter (fun x => dist S.triangle.v1 x = r1) := by
    rw [hC1]
    exact S.CP.v2_mem_C1
  have hv3C1 : S.triangle.v3 ∈ A.filter (fun x => dist S.triangle.v1 x = r1) := by
    rw [hC1]
    exact S.CP.v3_mem_C1
  have hv3C2 : S.triangle.v3 ∈ A.filter (fun x => dist S.triangle.v2 x = r2) := by
    rw [hC2]
    exact S.CP.v3_mem_C2
  have hv1C2 : S.triangle.v1 ∈ A.filter (fun x => dist S.triangle.v2 x = r2) := by
    rw [hC2]
    exact S.CP.v1_mem_C2
  have d12 : dist S.triangle.v1 S.triangle.v2 = r1 := (Finset.mem_filter.mp hv2C1).2
  have d13 : dist S.triangle.v1 S.triangle.v3 = r1 := (Finset.mem_filter.mp hv3C1).2
  have d23 : dist S.triangle.v2 S.triangle.v3 = r2 := (Finset.mem_filter.mp hv3C2).2
  have d21 : dist S.triangle.v2 S.triangle.v1 = r2 := (Finset.mem_filter.mp hv1C2).2
  have d12' : dist S.triangle.v1 S.triangle.v2 = r2 := by
    rw [dist_comm]
    exact d21
  refine ⟨?_, ?_⟩
  · calc
      dist S.triangle.v1 S.triangle.v2 = r1 := d12
      _ = dist S.triangle.v1 S.triangle.v2 := d12.symm
      _ = r2 := d12'
      _ = dist S.triangle.v2 S.triangle.v3 := d23.symm
  · calc
      dist S.triangle.v2 S.triangle.v3 = r2 := d23
      _ = dist S.triangle.v1 S.triangle.v2 := d12'.symm
      _ = r1 := d12
      _ = dist S.triangle.v3 S.triangle.v1 := by
        rw [dist_comm]
        exact d13.symm
theorem n7_circle_placement
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment) :
    ∃ d : ℝ, 0 < d ∧
      (∀ x ∈ S.CP.C1, dist S.triangle.v1 x = d) ∧
      (∀ x ∈ S.CP.C2, dist S.triangle.v2 x = d) ∧
      (∀ x ∈ S.CP.C3, dist S.triangle.v3 x = d) := by
  classical
  rcases S.exact_cap_class_at_v1 hN4e with ⟨r1, hr1, hC1⟩
  rcases S.exact_cap_class_at_v2 hN4e with ⟨r2, -, hC2⟩
  rcases S.exact_cap_class_at_v3 hN4e with ⟨r3, -, hC3⟩
  have hEq := S.n6_equilateral_moser_triangle hN4e
  have hv2C1 : S.triangle.v2 ∈ A.filter (fun x => dist S.triangle.v1 x = r1) := by
    rw [hC1]
    exact S.CP.v2_mem_C1
  have hv3C2 : S.triangle.v3 ∈ A.filter (fun x => dist S.triangle.v2 x = r2) := by
    rw [hC2]
    exact S.CP.v3_mem_C2
  have hv1C3 : S.triangle.v1 ∈ A.filter (fun x => dist S.triangle.v3 x = r3) := by
    rw [hC3]
    exact S.CP.v1_mem_C3
  have hr1d : r1 = dist S.triangle.v1 S.triangle.v2 := by
    symm
    exact (Finset.mem_filter.mp hv2C1).2
  have hr2d : r2 = dist S.triangle.v2 S.triangle.v3 := by
    symm
    exact (Finset.mem_filter.mp hv3C2).2
  have hr3d : r3 = dist S.triangle.v3 S.triangle.v1 := by
    symm
    exact (Finset.mem_filter.mp hv1C3).2
  let d : ℝ := dist S.triangle.v1 S.triangle.v2
  have hdpos : 0 < d := dist_pos.mpr S.triangle.v12_ne
  refine ⟨d, hdpos, ?_, ?_, ?_⟩
  · intro x hx
    have hxT : x ∈ A.filter (fun y => dist S.triangle.v1 y = r1) := by
      rw [hC1]
      exact hx
    have hxdist : dist S.triangle.v1 x = r1 := (Finset.mem_filter.mp hxT).2
    simpa [d, hr1d] using hxdist
  · intro x hx
    have hxT : x ∈ A.filter (fun y => dist S.triangle.v2 y = r2) := by
      rw [hC2]
      exact hx
    have hxdist : dist S.triangle.v2 x = r2 := (Finset.mem_filter.mp hxT).2
    calc
      dist S.triangle.v2 x = r2 := hxdist
      _ = dist S.triangle.v2 S.triangle.v3 := hr2d
      _ = dist S.triangle.v1 S.triangle.v2 := hEq.1.symm
      _ = d := by rfl
  · intro x hx
    have hxT : x ∈ A.filter (fun y => dist S.triangle.v3 y = r3) := by
      rw [hC3]
      exact hx
    have hxdist : dist S.triangle.v3 x = r3 := (Finset.mem_filter.mp hxT).2
    calc
      dist S.triangle.v3 x = r3 := hxdist
      _ = dist S.triangle.v3 S.triangle.v1 := hr3d
      _ = dist S.triangle.v2 S.triangle.v3 := hEq.2.symm
      _ = dist S.triangle.v1 S.triangle.v2 := hEq.1.symm
      _ = d := by rfl
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit046CirclePlacement

open scoped EuclideanGeometry

theorem solution {A : Finset ℝ²}
    (S : Batch3N9.Problem97.FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment) :
    ∃ d : ℝ, 0 < d ∧
      (∀ x ∈ S.CP.C1, dist S.triangle.v1 x = d) ∧
      (∀ x ∈ S.CP.C2, dist S.triangle.v2 x = d) ∧
      (∀ x ∈ S.CP.C3, dist S.triangle.v3 x = d) := by
  exact S.n7_circle_placement hN4e
