-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_193986560_r203816960_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:06:14.377741+00:00
-- url     : https://prove2.me/submissions/1d73a5c5-9105-4693-bdc2-468a3c479e41

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 37/160]`, `ρ ∈ [311/1280, 41/160]` by 17 cells of the computing
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
theorem cell0 : cellOK 188743680 190054400 203816960 206602240 ⟨⟨89356749269, 89356749276⟩, ⟨85841386896, 92918107742⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 188743680 190054400 206602240 209387520 ⟨⟨90494816471, 90494816479⟩, ⟨86971285641, 94064348646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 190054400 191365120 203816960 206602240 ⟨⟨88624547136, 88624547142⟩, ⟨85127160565, 92167563629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 190054400 191365120 206602240 209387520 ⟨⟨89754384822, 89754384830⟩, ⟨86248860500, 93305545922⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 188743680 190054400 209387520 212172800 ⟨⟨91631182743, 91631182751⟩, ⟨88099500531, 95208871150⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 188743680 190054400 212172800 214958080 ⟨⟨92765858516, 92765858522⟩, ⟨89226041879, 96351685809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 190054400 191365120 209387520 212172800 ⟨⟨90882558203, 90882558211⟩, ⟨87368912657, 94441846997⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 190054400 191365120 212172800 214958080 ⟨⟨92009077415, 92009077421⟩, ⟨88487327058, 95576477104⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 191365120 192675840 203816960 206602240 ⟨⟨87897524107, 87897524114⟩, ⟨84417911711, 91422405550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 191365120 192675840 206602240 209387520 ⟨⟨89019166648, 89019166654⟩, ⟨85531447442, 92552163320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 192675840 193331200 203816960 206602240 ⟨⟨87355606581, 87355606587⟩, ⟨85265414183, 89462419368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 193331200 193986560 203816960 206602240 ⟨⟨86995904541, 86995904547⟩, ⟨84911788866, 89096566024⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 192675840 193986560 206602240 209387520 ⟨⟨88289080210, 88289080213⟩, ⟨84818968116, 91804115610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 191365120 192675840 209387520 212172800 ⟨⟨90139180822, 90139180828⟩, ⟨86643370799, 93680276351⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 191365120 192675840 212172800 214958080 ⟨⟨91257576473, 91257576479⟩, ⟨87753691518, 94806754600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 192675840 193986560 209387520 212172800 ⟨⟨89400968557, 89400968562⟩, ⟨85922796290, 92924073699⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 192675840 193986560 212172800 214958080 ⟨⟨90511273362, 90511273367⟩, ⟨87025056287, 94042432511⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 193986560 203816960 214958080 t = true :=
  ⟨_, (join_su (m := 191365120) (by decide) (join_sr (m := 209387520) (by decide) (join_su (m := 190054400) (by decide) (join_sr (m := 206602240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 206602240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 190054400) (by decide) (join_sr (m := 212172800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 212172800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 209387520) (by decide) (join_su (m := 192675840) (by decide) (join_sr (m := 206602240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 206602240) (by decide) (join_su (m := 193331200) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))) (join_su (m := 192675840) (by decide) (join_sr (m := 212172800) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_sr (m := 212172800) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (37/160 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
