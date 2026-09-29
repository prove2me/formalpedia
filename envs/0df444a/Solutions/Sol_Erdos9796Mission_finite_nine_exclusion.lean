-- Prove2me | solution 1 for Erdos9796Mission.finite_nine_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-10T08:21:00.854075+00:00
-- url     : https://prove2.me/submissions/5fe2c335-e30b-4c66-8aaa-39e172428132

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Theorems.Thm_Erdos9796FiniteNine_shell
import Theorems.Thm_Erdos9796FiniteNine_form_b_v1
import Theorems.Thm_Erdos9796FiniteNine_form_b_v2
import Theorems.Thm_Erdos9796FiniteNine_form_a_v1
import Theorems.Thm_Erdos9796FiniteNine_form_c_v1
import Theorems.Thm_Erdos9796FiniteNine_cyclic_forms
import Theorems.Thm_Erdos9796FiniteNine_cap_containment
import Theorems.Thm_Erdos9796FiniteNine_circle_placement
import Theorems.Thm_Erdos9796FiniteNine_single_apex_exhaustion
import Definitions.Def_Erdos9796Counting_Adapter

/-! Final reduction over the nine accepted public child theorems. -/



open Erdos9796Mission

theorem solution :
    ∀ A : Finset Plane, A.card = 9 → ConvexIndep (A : Set Plane) →
      ¬ HasNEquidistantProperty 4 A := by
  intro A hcard hconv hK4
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨S⟩ := Erdos9796FiniteNine.shell hne hcard hconv hK4
  have hB1 : S.N4dExcludesFormB_v1 := Erdos9796FiniteNine.form_b_v1 S
  have hB2 : S.N4dExcludesFormB_v2 := Erdos9796FiniteNine.form_b_v2 S
  have hA1 : S.N4dExcludesFormA_v1 := Erdos9796FiniteNine.form_a_v1 S hB2
  have hC1 : S.N4dExcludesFormC_v1 := Erdos9796FiniteNine.form_c_v1 S
  have hcyclic : S.N4dExcludesFormA_v2 ∧ S.N4dExcludesFormC_v2 ∧
      S.N4dExcludesFormA_v3 ∧ S.N4dExcludesFormB_v3 ∧ S.N4dExcludesFormC_v3 :=
    Erdos9796FiniteNine.cyclic_forms S
  have hN4e : S.N4eCapContainment :=
    Erdos9796FiniteNine.cap_containment S hA1 hB1 hC1 hB2 hcyclic
  classical
  obtain ⟨h12, h23, h13, _⟩ := S.hCirc
  have hI1card : S.I1.card + 2 = S.CP.C1.card := by
    have hv3 : S.MT.toMoserTriangle.v3 ∈
        S.CP.C1.erase S.MT.toMoserTriangle.v2 :=
      Finset.mem_erase.mpr ⟨by intro h; exact h23 h.symm, S.CP.v3_mem_C1⟩
    have hC1erase :
        (S.CP.C1.erase S.MT.toMoserTriangle.v2).card = S.CP.C1.card - 1 :=
      Finset.card_erase_of_mem S.CP.v2_mem_C1
    have hC1ge : 2 ≤ S.CP.C1.card := by
      have hsubset :
          ({S.MT.toMoserTriangle.v2, S.MT.toMoserTriangle.v3} : Finset Plane) ⊆
            S.CP.C1 := by
        intro x hx
        simp at hx
        rcases hx with rfl | rfl
        · exact S.CP.v2_mem_C1
        · exact S.CP.v3_mem_C1
      have hcard_le := Finset.card_le_card hsubset
      simpa [h23] using hcard_le
    have hI1 : S.I1.card =
        (S.CP.C1.erase S.MT.toMoserTriangle.v2).card - 1 := by
      unfold Batch3N9.Problem97.FiniteEndpointShell.I1
      exact Finset.card_erase_of_mem hv3
    rw [hI1, hC1erase]
    omega
  have hI2card : S.I2.card + 2 = S.CP.C2.card := by
    have hv1 : S.MT.toMoserTriangle.v1 ∈
        S.CP.C2.erase S.MT.toMoserTriangle.v3 :=
      Finset.mem_erase.mpr ⟨h13, S.CP.v1_mem_C2⟩
    have hC2erase :
        (S.CP.C2.erase S.MT.toMoserTriangle.v3).card = S.CP.C2.card - 1 :=
      Finset.card_erase_of_mem S.CP.v3_mem_C2
    have hC2ge : 2 ≤ S.CP.C2.card := by
      have hsubset :
          ({S.MT.toMoserTriangle.v3, S.MT.toMoserTriangle.v1} : Finset Plane) ⊆
            S.CP.C2 := by
        intro x hx
        simp at hx
        rcases hx with rfl | rfl
        · exact S.CP.v3_mem_C2
        · exact S.CP.v1_mem_C2
      have hcard_le := Finset.card_le_card hsubset
      have h31 : S.MT.toMoserTriangle.v3 ≠ S.MT.toMoserTriangle.v1 := by
        intro h
        exact h13 h.symm
      simpa [h31] using hcard_le
    have hI2 : S.I2.card =
        (S.CP.C2.erase S.MT.toMoserTriangle.v3).card - 1 := by
      unfold Batch3N9.Problem97.FiniteEndpointShell.I2
      exact Finset.card_erase_of_mem hv1
    rw [hI2, hC2erase]
    omega
  have hI3card : S.I3.card + 2 = S.CP.C3.card := by
    have hv2 : S.MT.toMoserTriangle.v2 ∈
        S.CP.C3.erase S.MT.toMoserTriangle.v1 :=
      Finset.mem_erase.mpr ⟨by intro h; exact h12 h.symm, S.CP.v2_mem_C3⟩
    have hC3erase :
        (S.CP.C3.erase S.MT.toMoserTriangle.v1).card = S.CP.C3.card - 1 :=
      Finset.card_erase_of_mem S.CP.v1_mem_C3
    have hC3ge : 2 ≤ S.CP.C3.card := by
      have hsubset :
          ({S.MT.toMoserTriangle.v1, S.MT.toMoserTriangle.v2} : Finset Plane) ⊆
            S.CP.C3 := by
        intro x hx
        simp at hx
        rcases hx with rfl | rfl
        · exact S.CP.v1_mem_C3
        · exact S.CP.v2_mem_C3
      have hcard_le := Finset.card_le_card hsubset
      simpa [h12] using hcard_le
    have hI3 : S.I3.card =
        (S.CP.C3.erase S.MT.toMoserTriangle.v1).card - 1 := by
      unfold Batch3N9.Problem97.FiniteEndpointShell.I3
      exact Finset.card_erase_of_mem hv2
    rw [hI3, hC3erase]
    omega
  have hchoice : 4 ≤ S.CP.C1.card ∨ 4 ≤ S.CP.C2.card ∨
      4 ≤ S.CP.C3.card := by
    have hsum := S.hcapSum12
    omega
  rcases hchoice with hC1 | hC2 | hC3
  · obtain ⟨x, hx⟩ : S.I1.Nonempty := Finset.card_pos.mp (by omega)
    exact Erdos9796FiniteNine.single_apex_exhaustion S hN4e S.hK4
      (i := ⟨0, by omega⟩) (by simpa [Batch3N9.Problem97.FiniteEndpointShell.capInteriorByIndex] using hx)
  · obtain ⟨x, hx⟩ : S.I2.Nonempty := Finset.card_pos.mp (by omega)
    exact Erdos9796FiniteNine.single_apex_exhaustion S hN4e S.hK4
      (i := ⟨1, by omega⟩) (by simpa [Batch3N9.Problem97.FiniteEndpointShell.capInteriorByIndex] using hx)
  · obtain ⟨x, hx⟩ : S.I3.Nonempty := Finset.card_pos.mp (by omega)
    exact Erdos9796FiniteNine.single_apex_exhaustion S hN4e S.hK4
      (i := ⟨2, by omega⟩) (by simpa [Batch3N9.Problem97.FiniteEndpointShell.capInteriorByIndex] using hx)
