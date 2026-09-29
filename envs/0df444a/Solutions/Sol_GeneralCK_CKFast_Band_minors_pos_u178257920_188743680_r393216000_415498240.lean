-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_188743680_r393216000_415498240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:03:55.235246+00:00
-- url     : https://prove2.me/submissions/d8a8427d-3574-4471-9dc1-516c9a429a3f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 9/40]`, `ρ ∈ [15/32, 317/640]` by 20 cells of the computing
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
theorem cell0 : cellOK 178257920 180879360 393216000 398786560 ⟨⟨173260091338, 173260091347⟩, ⟨164929015828, 181780816693⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178257920 180879360 398786560 404357120 ⟨⟨175438710908, 175438710917⟩, ⟨167078674890, 183988116281⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 180879360 183500800 393216000 398786560 ⟨⟨170717919642, 170717919651⟩, ⟨162467388024, 179156008858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 180879360 183500800 398786560 404357120 ⟨⟨172871370441, 172871370450⟩, ⟨164591863646, 181338189521⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 178257920 180879360 404357120 409927680 ⟨⟨177612233631, 177612233638⟩, ⟨169223338148, 186190212424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 178257920 180879360 409927680 415498240 ⟨⟨179780725994, 179780726003⟩, ⟨171363070569, 188387173150⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 180879360 183500800 404357120 409927680 ⟨⟨175019909445, 175019909452⟩, ⟨166711523520, 183515356824⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 180879360 183500800 409927680 415498240 ⟨⟨177163600046, 177163600055⟩, ⟨168826429618, 185687575605⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 183500800 184811520 393216000 398786560 ⟨⟨168829358921, 168829358930⟩, ⟨163922361877, 173803481499⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 184811520 186122240 393216000 398786560 ⟨⟨167578749246, 167578749254⟩, ⟨162698677038, 172525511786⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 183500800 186122240 398786560 404357120 ⟨⟨170331505871, 170331505880⟩, ⟨162131095779, 178717209174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 186122240 187432960 393216000 398786560 ⟨⟨166334778951, 166334778955⟩, ⟨161481399855, 171254417183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 187432960 188743680 393216000 398786560 ⟨⟨165097359439, 165097359448⟩, ⟨160270444892, 169990105890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 186122240 187432960 398786560 404357120 ⟨⟨168444199104, 168444199108⟩, ⟨163575351627, 173379184699⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 187432960 188743680 398786560 404357120 ⟨⟨167194204835, 167194204844⟩, ⟨162351821588, 172102305213⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 183500800 186122240 404357120 409927680 ⟨⟨172455061329, 172455061337⟩, ⟨164225765548, 180869433254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 183500800 186122240 409927680 415498240 ⟨⟨174573945373, 174573945382⟩, ⟨166315853721, 183016890655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 186122240 187432960 404357120 409927680 ⟨⟨170549019087, 170549019089⟩, ⟨165664760333, 175499293421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 187432960 188743680 404357120 409927680 ⟨⟨169286536300, 169286536307⟩, ⟨164428740025, 174209933414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell19 : cellOK 186122240 188743680 409927680 415498240 ⟨⟨172011039952, 172011039960⟩, ⟨163830658877, 180374357532⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 188743680 393216000 415498240 t = true :=
  ⟨_, (join_su (m := 183500800) (by decide) (join_sr (m := 404357120) (by decide) (join_su (m := 180879360) (by decide) (join_sr (m := 398786560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 398786560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 180879360) (by decide) (join_sr (m := 409927680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 409927680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 404357120) (by decide) (join_su (m := 186122240) (by decide) (join_sr (m := 398786560) (by decide) (join_su (m := 184811520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 398786560) (by decide) (join_su (m := 187432960) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 187432960) (by decide) (leaf_ok cell13) (leaf_ok cell14)))) (join_su (m := 186122240) (by decide) (join_sr (m := 409927680) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_sr (m := 409927680) (by decide) (join_su (m := 187432960) (by decide) (leaf_ok cell17) (leaf_ok cell18)) (leaf_ok cell19)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (15/32 : ℝ) (317/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  have e3 : (((415498240 : ℤ) : ℝ) / (D : ℝ)) = (317/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
