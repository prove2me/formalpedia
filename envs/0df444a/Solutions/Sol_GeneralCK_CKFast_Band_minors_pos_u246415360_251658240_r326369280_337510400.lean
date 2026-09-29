-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_251658240_r326369280_337510400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:50:01.788698+00:00
-- url     : https://prove2.me/submissions/2460a0fd-353f-4160-9916-babdb6f2f0c8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 3/10]`, `ρ ∈ [249/640, 103/256]` by 18 cells of the computing
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
theorem cell0 : cellOK 246415360 247726080 326369280 329154560 ⟨⟨96002017194, 96002017201⟩, ⟨92829371868, 99210340505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246415360 247726080 329154560 331939840 ⟨⟨96782494222, 96782494228⟩, ⟨93603195804, 99997509598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247726080 249036800 326369280 329154560 ⟨⟨95142965168, 95142965175⟩, ⟨91983157223, 98338269408⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247726080 249036800 329154560 331939840 ⟨⟨95917052805, 95917052812⟩, ⟨92750617400, 99119024097⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 246415360 247726080 331939840 334725120 ⟨⟨97562481699, 97562481706⟩, ⟨94376531404, 100784187769⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 246415360 247726080 334725120 337510400 ⟨⟨98341982013, 98341982020⟩, ⟨95149381047, 101570377417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247726080 249036800 331939840 334725120 ⟨⟨96690662977, 96690662984⟩, ⟨93517601168, 99899300112⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247726080 249036800 334725120 337510400 ⟨⟨97463798002, 97463798009⟩, ⟨94284110837, 100679099783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 250347520 326369280 329154560 ⟨⟨94287296524, 94287296530⟩, ⟨91140225418, 97469684020⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249036800 250347520 329154560 331939840 ⟨⟨95055004929, 95055004936⟩, ⟨91901332150, 98244034295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 250347520 251002880 326369280 329154560 ⟨⟨93647738511, 93647738514⟩, ⟨91837408355, 95470170612⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 251002880 251658240 326369280 329154560 ⟨⟨93222400648, 93222400654⟩, ⟨91416480229, 95040385011⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 250347520 251002880 329154560 331939840 ⟨⟨94410669127, 94410669129⟩, ⟨92596829976, 96236619566⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 251002880 251658240 329154560 331939840 ⟨⟨93982149212, 93982149219⟩, ⟨92172727476, 95803644349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 249036800 250347520 331939840 334725120 ⟨⟨95822247732, 95822247738⟩, ⟨92661974180, 99017917917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 249036800 250347520 334725120 337510400 ⟨⟨96589027181, 96589027188⟩, ⟨93422153750, 99791337147⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 250347520 251658240 331939840 334725120 ⟨⟨94957191210, 94957191216⟩, ⟨91809606912, 98139995184⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 250347520 251658240 334725120 337510400 ⟨⟨95717624744, 95717624751⟩, ⟨92563466199, 98907043461⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 251658240 326369280 337510400 t = true :=
  ⟨_, (join_su (m := 249036800) (by decide) (join_sr (m := 331939840) (by decide) (join_su (m := 247726080) (by decide) (join_sr (m := 329154560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 329154560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 247726080) (by decide) (join_sr (m := 334725120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 334725120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 331939840) (by decide) (join_su (m := 250347520) (by decide) (join_sr (m := 329154560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 329154560) (by decide) (join_su (m := 251002880) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_su (m := 251002880) (by decide) (leaf_ok cell12) (leaf_ok cell13)))) (join_su (m := 250347520) (by decide) (join_sr (m := 334725120) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_sr (m := 334725120) (by decide) (leaf_ok cell16) (leaf_ok cell17)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (249/640 : ℝ) (103/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  have e3 : (((337510400 : ℤ) : ℝ) / (D : ℝ)) = (103/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
