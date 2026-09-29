-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u112721920_115343360_r95682560_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:07:38.513304+00:00
-- url     : https://prove2.me/submissions/6e1ce599-c67d-4361-a1e5-ff5141d64ae7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/320, 11/80]`, `ρ ∈ [73/640, 41/320]` by 20 cells of the computing
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
theorem cell0 : cellOK 112721920 113377280 95682560 97157120 ⟨⟨74009794285, 74009794289⟩, ⟨71620698782, 76422715030⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 112721920 113377280 97157120 98631680 ⟨⟨75048759308, 75048759309⟩, ⟨72656281804, 77465027022⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 113377280 114032640 95682560 97157120 ⟨⟨73639229541, 73639229549⟩, ⟨71260537722, 76041558045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 113377280 114032640 97157120 98631680 ⟨⟨74673748967, 74673748975⟩, ⟨72291682612, 77079417813⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 112721920 113377280 98631680 101580800 ⟨⟨76602681738, 76602681741⟩, ⟨73541706857, 79702527014⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 113377280 114032640 98631680 101580800 ⟨⟨76221058160, 76221058170⟩, ⟨73174369630, 79306292171⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 114032640 114688000 95682560 97157120 ⟨⟨73271489479, 73271489486⟩, ⟨70903098595, 75663330982⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 114032640 114688000 97157120 98631680 ⟨⟨74301587983, 74301587990⟩, ⟨71929830130, 76696763080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 114688000 115343360 95682560 97157120 ⟨⟨72906536678, 72906536688⟩, ⟨70548345519, 75287994845⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 114688000 115343360 97157120 98631680 ⟨⟨73932238711, 73932238718⟩, ⟨71570688245, 76317023603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 114032640 114688000 98631680 101580800 ⟨⟨75842320201, 75842320211⟩, ⟨72809780487, 78913084768⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 114688000 115343360 98631680 101580800 ⟨⟨75466429892, 75466429900⟩, ⟨72447903498, 78522864719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 112721920 113377280 101580800 104529920 ⟨⟨78666207908, 78666207912⟩, ⟨75597620778, 81773521380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 113377280 114032640 101580800 104529920 ⟨⟨78275868253, 78275868261⟩, ⟨75221581567, 81368559443⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 112721920 113377280 104529920 107479040 ⟨⟨80720273285, 80720273289⟩, ⟨77644179883, 83834949002⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 113377280 114032640 104529920 107479040 ⟨⟨80321331736, 80321331746⟩, ⟨77259551308, 83421375705⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 114032640 114688000 101580800 104529920 ⟨⟨77888461200, 77888461209⟩, ⟨74848337771, 80966671517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 114688000 115343360 101580800 104529920 ⟨⟨77503948368, 77503948376⟩, ⟨74477853034, 80567817118⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 114032640 114688000 104529920 107479040 ⟨⟨79925368251, 79925368259⟩, ⟨76877763980, 83010921441⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell19 : cellOK 114688000 115343360 104529920 107479040 ⟨⟨79532344054, 79532344064⟩, ⟨76498781140, 82603545353⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 112721920 115343360 95682560 107479040 t = true :=
  ⟨_, (join_sr (m := 101580800) (by decide) (join_su (m := 114032640) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 113377280) (by decide) (join_sr (m := 97157120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 97157120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 113377280) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 98631680) (by decide) (join_su (m := 114688000) (by decide) (join_sr (m := 97157120) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 97157120) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 114688000) (by decide) (leaf_ok cell10) (leaf_ok cell11)))) (join_su (m := 114032640) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 113377280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 113377280) (by decide) (leaf_ok cell14) (leaf_ok cell15))) (join_sr (m := 104529920) (by decide) (join_su (m := 114688000) (by decide) (leaf_ok cell16) (leaf_ok cell17)) (join_su (m := 114688000) (by decide) (leaf_ok cell18) (leaf_ok cell19)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/320 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((112721920 : ℤ) : ℝ) / (D : ℝ)) = (43/320 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
