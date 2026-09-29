-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u217579520_220200960_r181534720_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:34:10.179221+00:00
-- url     : https://prove2.me/submissions/3af92eb1-69a5-422b-9c67-8bf2b7ff846a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [83/320, 21/80]`, `ρ ∈ [277/1280, 147/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 217579520 218234880 181534720 184320000 ⟨⟨66719978658, 66719978661⟩, ⟨64872803949, 68581232548⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 218234880 218890240 181534720 184320000 ⟨⟨66432270768, 66432270775⟩, ⟨64590031056, 68288530724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 217579520 218234880 184320000 187105280 ⟨⟨67694892843, 67694892846⟩, ⟨65843611725, 69560258689⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 218234880 218890240 184320000 187105280 ⟨⟨67403305834, 67403305839⟩, ⟨65556970601, 69263667034⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 218890240 219545600 181534720 184320000 ⟨⟨66145437486, 66145437492⟩, ⟨64308108994, 67996727674⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 219545600 220200960 181534720 184320000 ⟨⟨65859472214, 65859472221⟩, ⟨64027031354, 67705816614⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 218890240 219545600 184320000 187105280 ⟨⟨67112601405, 67112601410⟩, ⟨65271188281, 68967982123⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 219545600 220200960 184320000 187105280 ⟨⟨66822772915, 66822772922⟩, ⟨64986258308, 68673197132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 217579520 218234880 187105280 189890560 ⟨⟨68668719540, 68668719543⟩, ⟨66813337635, 70538191643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 218234880 218890240 187105280 189890560 ⟨⟨68373266227, 68373266233⟩, ⟨66522840984, 70237723082⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 217579520 218234880 189890560 192675840 ⟨⟨69641464476, 69641464478⟩, ⟨67781987370, 71515037163⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 218234880 218890240 189890560 192675840 ⟨⟨69342157585, 69342157590⟩, ⟨67487647804, 71210704539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 218890240 219545600 187105280 189890560 ⟨⟨68078703339, 68078703345⟩, ⟨66233210979, 69938169112⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 219545600 220200960 187105280 189890560 ⟨⟨67785024194, 67785024200⟩, ⟨65944441124, 69639522863⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 218890240 219545600 189890560 192675840 ⟨⟨69043748840, 69043748845⟩, ⟨67194182607, 70907294223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 219545600 220200960 189890560 192675840 ⟨⟨68746231517, 68746231523⟩, ⟨66901585239, 70604799304⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 217579520 220200960 181534720 192675840 t = true :=
  ⟨_, (join_sr (m := 187105280) (by decide) (join_su (m := 218890240) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 218234880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 218234880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184320000) (by decide) (join_su (m := 219545600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 219545600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 218890240) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 218234880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 218234880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 189890560) (by decide) (join_su (m := 219545600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 219545600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (83/320 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
