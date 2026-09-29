-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_107479040_r95682560_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:05:47.811892+00:00
-- url     : https://prove2.me/submissions/6ee6b45f-6396-4a9c-a6ed-d6512c41712c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 41/320]`, `ρ ∈ [73/640, 41/320]` by 16 cells of the computing
correction-band checker; each cell is kernel-checked in its own declaration. -/

theorem leaf_ok {U0 U1 R0 R1 : ℤ} {h : Hint} (hc : cellOK U0 U1 R0 R1 h = true) :
    treeOK U0 U1 R0 R1 (.leaf h) = true := by
  simpa only [treeOK] using hc

theorem join_su {U0 U1 R0 R1 m : ℤ} {l r : Tree} (hm : (decide (U0 ≤ m) && decide (m ≤ U1)) = true)
    (hl : treeOK U0 m R0 R1 l = true) (hr : treeOK m U1 R0 R1 r = true) :
    treeOK U0 U1 R0 R1 (.su m l r) = true := by
  simp only [treeOK, Bool.and_eq_true] at hm ⊢
  exact ⟨⟨hm, hl⟩, hr⟩

theorem join_sr {U0 U1 R0 R1 m : ℤ} {l r : Tree} (hm : (decide (R0 ≤ m) && decide (m ≤ R1)) = true)
    (hl : treeOK U0 U1 R0 m l = true) (hr : treeOK U0 U1 m R1 r = true) :
    treeOK U0 U1 R0 R1 (.sr m l r) = true := by
  simp only [treeOK, Bool.and_eq_true] at hm ⊢
  exact ⟨⟨hm, hl⟩, hr⟩

set_option maxRecDepth 100000 in
theorem cell0 : cellOK 104857600 105512960 95682560 98631680 ⟨⟨79239008622, 79239008631⟩, ⟨76002944979, 82518393904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 105512960 106168320 95682560 98631680 ⟨⟨78828979883, 78828979893⟩, ⟨75609017779, 82091876491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 104857600 105512960 98631680 101580800 ⟨⟨81422050869, 81422050878⟩, ⟨78178109429, 84709126936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 105512960 106168320 98631680 101580800 ⟨⟨81002571474, 81002571484⟩, ⟨77774742149, 84273152326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 106168320 106823680 95682560 98631680 ⟨⟨78422296714, 78422296718⟩, ⟨75218270048, 81668876199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 106823680 107479040 95682560 98631680 ⟨⟨78018912227, 78018912235⟩, ⟨74830657543, 81249343409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 106168320 106823680 98631680 101580800 ⟨⟨80586491788, 80586491792⟩, ⟨77374609005, 83840748359⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 106823680 107479040 98631680 101580800 ⟨⟨80173764433, 80173764441⟩, ⟨76977665241, 83411864953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 104857600 105512960 101580800 104529920 ⟨⟨83593990087, 83593990097⟩, ⟨80342300205, 86888627834⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 105512960 106168320 101580800 104529920 ⟨⟨83165197251, 83165197259⟩, ⟨79929628127, 86443335148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 104857600 105512960 104529920 107479040 ⟨⟨85754969852, 85754969862⟩, ⟨82495658196, 89057042876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 105512960 106168320 104529920 107479040 ⟨⟨85316998133, 85316998141⟩, ⟨82073814010, 88602568517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 106168320 106823680 101580800 104529920 ⟨⟨82739856348, 82739856352⟩, ⟨79520242969, 86001664687⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 106823680 107479040 101580800 104529920 ⟨⟨82317919549, 82317919559⟩, ⟨79114099496, 85563565936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 106168320 106823680 104529920 107479040 ⟨⟨84882528718, 84882528721⟩, ⟨81655307696, 88151766086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 106823680 107479040 104529920 107479040 ⟨⟨84451513351, 84451513361⟩, ⟨81240093577, 87704584658⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 107479040 95682560 107479040 t = true :=
  ⟨_, (join_sr (m := 101580800) (by decide) (join_su (m := 106168320) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 105512960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 105512960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 98631680) (by decide) (join_su (m := 106823680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 106823680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 106168320) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 105512960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 105512960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 104529920) (by decide) (join_su (m := 106823680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 106823680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (41/320 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
