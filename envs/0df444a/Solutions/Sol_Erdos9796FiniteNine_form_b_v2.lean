-- Prove2me | solution 1 for Erdos9796FiniteNine.form_b_v2
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-10T04:30:17.198468+00:00
-- url     : https://prove2.me/submissions/4dc55b21-a512-4a1c-9e81-161649b772be

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796FiniteNine_N8Interface
import Theorems.Thm_Erdos9796FiniteNine_form_b_v1

/-! Authenticated cyclic relabelling support for the Form `b` exclusion at `v₂`. -/

open scoped EuclideanGeometry

-- Original module: Solutions.Batch3N9.N4d.CyclicTransport
section Batch3N9Unit073
namespace Batch3N9
open scoped EuclideanGeometry
open scoped InnerProductSpace
open Finset
namespace Problem97
namespace FiniteEndpointShell
noncomputable def b3n9m073_cyclicShiftMT {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    Problem97.MEC.NonObtuseCircumscribedMoserTriangle A S.hne S.hnoncol :=
  { toMoserTriangle :=
      { v1 := S.MT.toMoserTriangle.v2
        v2 := S.MT.toMoserTriangle.v3
        v3 := S.MT.toMoserTriangle.v1
        v1_mem := S.MT.toMoserTriangle.v2_mem
        v2_mem := S.MT.toMoserTriangle.v3_mem
        v3_mem := S.MT.toMoserTriangle.v1_mem
        v1_boundary := S.MT.toMoserTriangle.v2_boundary
        v2_boundary := S.MT.toMoserTriangle.v3_boundary
        v3_boundary := S.MT.toMoserTriangle.v1_boundary
        case_split := by
          obtain ⟨h12, h23, h13, _⟩ := S.hCirc
          exact Or.inl ⟨h23, h13.symm, h12.symm⟩ }
    inner_at_v1 := S.MT.inner_at_v2
    inner_at_v2 := S.MT.inner_at_v3
    inner_at_v3 := S.MT.inner_at_v1 }
theorem b3n9m073_cyclicShift_hCirc {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    ∃ h12 h23 h13,
      (b3n9m073_cyclicShiftMT S).toMoserTriangle.case_split = Or.inl ⟨h12, h23, h13⟩ := by
  obtain ⟨h12, h23, h13, _⟩ := S.hCirc
  exact ⟨h23, h13.symm, h12.symm, rfl⟩
theorem b3n9m073_not_mem_verts_of_not_mem_cyclicShift_verts
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {v : ℝ²}
    (hv : v ∉ ((b3n9m073_cyclicShiftMT S).toMoserTriangle.toStructural
      (b3n9m073_cyclicShift_hCirc S)).verts) :
    v ∉ S.triangle.verts := by
  intro hvOld
  apply hv
  unfold Problem97.MoserTriangle.verts at hvOld ⊢
  simp only [mem_insert, mem_singleton] at hvOld ⊢
  rcases hvOld with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
noncomputable def b3n9m073_cyclicShiftCP {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    Problem97.CapTriple A
      ((b3n9m073_cyclicShiftMT S).toMoserTriangle.toStructural (b3n9m073_cyclicShift_hCirc S)) :=
  { C1 := S.CP.C2
    C2 := S.CP.C3
    C3 := S.CP.C1
    C1_subset := S.CP.C2_subset
    C2_subset := S.CP.C3_subset
    C3_subset := S.CP.C1_subset
    v1_notin_C1 := S.CP.v2_notin_C2
    v2_mem_C1 := S.CP.v3_mem_C2
    v3_mem_C1 := S.CP.v1_mem_C2
    v1_mem_C2 := S.CP.v2_mem_C3
    v2_notin_C2 := S.CP.v3_notin_C3
    v3_mem_C2 := S.CP.v1_mem_C3
    v1_mem_C3 := S.CP.v2_mem_C1
    v2_mem_C3 := S.CP.v3_mem_C1
    v3_notin_C3 := S.CP.v1_notin_C1
    nonmoser_in_one := by
      classical
      intro v hvA hv
      have hvOld := b3n9m073_not_mem_verts_of_not_mem_cyclicShift_verts S hv
      simpa [add_assoc, add_comm, add_left_comm] using S.CP.nonmoser_in_one v hvA hvOld
    arc_membership := by
      intro v hvA
      have h := S.CP.arc_membership v hvA
      exact ⟨h.2.1, h.2.2, h.1⟩ }
noncomputable def b3n9m073_cyclicShiftPacket {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    Problem97.CircumscribedMECPacket A
      ((b3n9m073_cyclicShiftMT S).toMoserTriangle.toStructural (b3n9m073_cyclicShift_hCirc S)) :=
  { center := S.Packet.center
    radius := S.Packet.radius
    radius_pos := S.Packet.radius_pos
    moser_on_boundary_1 := S.Packet.moser_on_boundary_2
    moser_on_boundary_2 := S.Packet.moser_on_boundary_3
    moser_on_boundary_3 := S.Packet.moser_on_boundary_1
    inner_at_v1 := S.Packet.inner_at_v2
    inner_at_v2 := S.Packet.inner_at_v3
    inner_at_v3 := S.Packet.inner_at_v1
    disk_contains_A := S.Packet.disk_contains_A }
@[reducible] noncomputable def cyclicShift {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    FiniteEndpointShell A :=
  { hne := S.hne
    hcard9 := S.hcard9
    hconv := S.hconv
    hK4 := S.hK4
    hnoncol := S.hnoncol
    hbd := S.hbd
    MT := b3n9m073_cyclicShiftMT S
    hCirc := b3n9m073_cyclicShift_hCirc S
    CP := b3n9m073_cyclicShiftCP S
    hcapSum12 := by
      simpa [b3n9m073_cyclicShiftCP, add_assoc, add_comm, add_left_comm] using S.hcapSum12
    Packet := b3n9m073_cyclicShiftPacket S }

theorem cyclicShift_witnessClassAt_v1 {A : Finset ℝ²}
    (S : FiniteEndpointShell A) (r : ℝ) :
    (S.cyclicShift).witnessClassAt_v1 r = S.witnessClassAt_v2 r := by
  rfl

theorem cyclicShift_CP_C1 {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    (S.cyclicShift).CP.C1 = S.CP.C2 := by
  rfl

theorem isFormB_v1_cyclicShift {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (r : ℝ) : (S.cyclicShift).IsFormB_v1 r ↔ S.IsFormB_v2 r := by
  rfl

theorem N4dExcludesFormB_v2_proof
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    S.N4dExcludesFormB_v2 := by
  intro r hr hcard hesc hform
  exact Erdos9796FiniteNine.form_b_v1 (S.cyclicShift) (r := r) hr
    (by simpa [cyclicShift_witnessClassAt_v1] using hcard)
    (by simpa [cyclicShift_witnessClassAt_v1, cyclicShift_CP_C1, b3n9m073_cyclicShiftCP] using hesc)
    ((isFormB_v1_cyclicShift S r).mpr hform)

end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit073

/-- The escaped Form `b` at `v₂` is impossible for a finite endpoint shell. -/
theorem solution {A : Finset ℝ²}
    (S : Batch3N9.Problem97.FiniteEndpointShell A) :
    S.N4dExcludesFormB_v2 :=
  Batch3N9.Problem97.FiniteEndpointShell.N4dExcludesFormB_v2_proof S
