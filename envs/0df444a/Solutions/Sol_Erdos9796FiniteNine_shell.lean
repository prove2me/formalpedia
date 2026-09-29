-- Prove2me | solution 1 for Erdos9796FiniteNine.shell
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T07:24:29.439493+00:00
-- url     : https://prove2.me/submissions/1e741eb6-3b25-4609-9c63-9e8fb24eb101

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796FiniteNine_Shell
import Theorems.Thm_Problem97_ConvexIndep_not_collinear_of_card_ge_three
import Theorems.Thm_Problem97_Dumitrescu_three_cap_decomposition
import Theorems.Thm_Problem97_MEC_exists_nonobtuse_circumscribed_triple
import Theorems.Thm_Problem97_MEC_no_diameter_under_k4
import Theorems.Thm_Problem97_card_ge_five_of_K4

open scoped EuclideanGeometry InnerProductSpace

theorem solution :
    ∀ {A : Finset ℝ²}, A.Nonempty → A.card = 9 →
      Batch3N9.Problem97.ConvexIndep A →
      Batch3N9.Problem97.HasNEquidistantProperty 4 A →
      Nonempty (Batch3N9.Problem97.FiniteEndpointShell A) := by
  classical
  intro A hne hcard9 hconv hK4
  have h5 : 5 ≤ A.card :=
    _root_.Problem97.card_ge_five_of_K4 hne hK4
  have h3 : 3 ≤ A.card := le_trans (by decide : 3 ≤ 5) h5
  have hnoncol : ¬ Collinear ℝ (A : Set ℝ²) :=
    _root_.Problem97.ConvexIndep.not_collinear_of_card_ge_three hconv h3
  have hbd :
      3 ≤ (A.filter (fun p =>
        dist p (_root_.Problem97.MEC.mec A hne).center =
          (_root_.Problem97.MEC.mec A hne).radius)).card :=
    _root_.Problem97.MEC.no_diameter_under_k4 hne hnoncol hconv hK4
  let htriple :=
    _root_.Problem97.MEC.exists_nonobtuse_circumscribed_triple hne hnoncol hbd
  let a := Classical.choose htriple
  let htriple1 := Classical.choose_spec htriple
  let b := Classical.choose htriple1
  let htriple2 := Classical.choose_spec htriple1
  let c := Classical.choose htriple2
  let htriple3 := Classical.choose_spec htriple2
  rcases htriple3 with
    ⟨haA, hbA, hcA, hab, hbc, hac, haB, hbB, hcB, hacute1, hacute2, hacute3⟩
  let MT : _root_.Problem97.MEC.MoserTriangle A hne hnoncol :=
    { v1 := a
      v2 := b
      v3 := c
      v1_mem := haA
      v2_mem := hbA
      v3_mem := hcA
      v1_boundary := haB
      v2_boundary := hbB
      v3_boundary := hcB
      case_split := Or.inl ⟨hab, hbc, hac⟩ }
  let N : _root_.Problem97.MEC.NonObtuseCircumscribedMoserTriangle A hne hnoncol :=
    { toMoserTriangle := MT
      inner_at_v1 := hacute1
      inner_at_v2 := hacute2
      inner_at_v3 := hacute3 }
  have hCirc : ∃ h12 h23 h13,
      MT.case_split = Or.inl ⟨h12, h23, h13⟩ := by
    exact ⟨hab, hbc, hac, rfl⟩
  let hdecomp :=
    _root_.Problem97.Dumitrescu.three_cap_decomposition hconv MT hCirc
  let CP := Classical.choose hdecomp
  let hcapSum := Classical.choose_spec hdecomp
  have hcapSum' : CP.C1.card + CP.C2.card + CP.C3.card = A.card + 3 := by
    simpa [CP] using hcapSum
  have hcapSum12 : CP.C1.card + CP.C2.card + CP.C3.card = 12 := by
    have hcard9' : A.card + 3 = 12 := by omega
    rw [hcapSum']
    exact hcard9'
  let Packet : _root_.Problem97.CircumscribedMECPacket A
      (MT.toStructural hCirc) :=
    _root_.Problem97.CircumscribedMECPacket.ofNonObtuse N hCirc
  exact ⟨{
    hne := hne
    hcard9 := hcard9
    hconv := hconv
    hK4 := hK4
    hnoncol := hnoncol
    hbd := hbd
    MT := N
    hCirc := hCirc
    CP := CP
    hcapSum12 := hcapSum12
    Packet := Packet
  }⟩
