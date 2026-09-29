-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_115343360_r414187520_461373440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:44:12.593589+00:00
-- url     : https://prove2.me/submissions/fc43639a-687a-450b-bcab-80c2ec4a644d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 11/80]`, `ρ ∈ [79/160, 11/20]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 107479040 414187520 425984000 ⟨⟨271876504698, 271876504710⟩, ⟨257414725513, 286747861471⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 107479040 110100480 414187520 425984000 ⟨⟨268029425752, 268029425764⟩, ⟨253763919426, 282698900714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 104857600 107479040 425984000 437780480 ⟨⟨277806481545, 277806481557⟩, ⟨263310127997, 292704134113⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 107479040 110100480 425984000 437780480 ⟨⟨273915798715, 273915798727⟩, ⟨259613215527, 288614478656⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 110100480 112721920 414187520 425984000 ⟨⟨264245635679, 264245635687⟩, ⟨250171911358, 278717803052⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 112721920 115343360 414187520 425984000 ⟨⟨260522994839, 260522994850⟩, ⟨246636722919, 274802268061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 110100480 112721920 425984000 437780480 ⟨⟨270087724484, 270087724492⟩, ⟨255974578662, 284591830895⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 112721920 115343360 425984000 437780480 ⟨⟨266320167287, 266320167299⟩, ⟨252392278688, 280633947654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 104857600 107479040 437780480 449576960 ⟨⟨283685009477, 283685009490⟩, ⟨269155167564, 298607973123⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 107479040 110100480 437780480 449576960 ⟨⟨279752100983, 279752100995⟩, ⟨265413530435, 294478985111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 104857600 107479040 449576960 461373440 ⟨⟨289514047794, 289514047804⟩, ⟨274951733038, 304461405121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 107479040 110100480 449576960 461373440 ⟨⟨285540215515, 285540215527⟩, ⟨271166678885, 300294368598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 110100480 112721920 437780480 449576960 ⟨⟨275881101420, 275881101425⟩, ⟨261729623224, 290416134912⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 112721920 115343360 437780480 449576960 ⟨⟨272069966439, 272069966451⟩, ⟨258101546439, 286417235257⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 110100480 112721920 449576960 461373440 ⟨⟨281627575612, 281627575616⟩, ⟨267438788242, 296192587915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 112721920 115343360 449576960 461373440 ⟨⟨277774130043, 277774130055⟩, ⟨263766200311, 292153930363⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 115343360 414187520 461373440 t = true :=
  ⟨_, (join_sr (m := 437780480) (by decide) (join_su (m := 110100480) (by decide) (join_sr (m := 425984000) (by decide) (join_su (m := 107479040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 107479040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 425984000) (by decide) (join_su (m := 112721920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 112721920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 110100480) (by decide) (join_sr (m := 449576960) (by decide) (join_su (m := 107479040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 107479040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 449576960) (by decide) (join_su (m := 112721920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 112721920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (79/160 : ℝ) (11/20 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((414187520 : ℤ) : ℝ) / (D : ℝ)) = (79/160 : ℝ) := by norm_num [D]
  have e3 : (((461373440 : ℤ) : ℝ) / (D : ℝ)) = (11/20 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
