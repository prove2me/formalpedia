-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u152043520_154664960_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:39:05.769883+00:00
-- url     : https://prove2.me/submissions/f9ae6f11-ed08-4873-9222-250968375905

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [29/160, 59/320]`, `ρ ∈ [5/32, 109/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 152043520 152698880 131072000 134021120 ⟨⟨75249955461, 75249955466⟩, ⟨72788432948, 77736047116⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 152698880 153354240 131072000 134021120 ⟨⟨74922867770, 74922867776⟩, ⟨72470173297, 77399980617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 152043520 152698880 134021120 136970240 ⟨⟨76812182590, 76812182593⟩, ⟨74344647195, 79304248180⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 152698880 153354240 134021120 136970240 ⟨⟨76479141450, 76479141458⟩, ⟨74020448432, 78962214845⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 153354240 154009600 131072000 134021120 ⟨⟨74597483147, 74597483155⟩, ⟨72153554373, 77065680996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 154009600 154664960 131072000 134021120 ⟨⟨74273784676, 74273784683⟩, ⟨71838559942, 76733130626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 153354240 154009600 134021120 136970240 ⟨⟨76147825123, 76147825129⟩, ⟨73697912207, 78621970039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 154009600 154664960 134021120 136970240 ⟨⟨75818216538, 75818216545⟩, ⟨73377022141, 78283495990⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 152043520 152698880 136970240 139919360 ⟨⟨78370172680, 78370172682⟩, ⟨75896662308, 80868174106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 152698880 153354240 136970240 139919360 ⟨⟨78031225095, 78031225101⟩, ⟨75566570893, 80520221474⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 152043520 152698880 139919360 142868480 ⟨⟨79923961498, 79923961501⟩, ⟨77444513604, 82427861107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 152698880 153354240 139919360 142868480 ⟨⟨79579153906, 79579153913⟩, ⟨77108575449, 82074036144⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 153354240 154009600 136970240 139919360 ⟨⟨77694023547, 77694023553⟩, ⟨75238163323, 80174078500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 154009600 154664960 136970240 139919360 ⟨⟨77358550824, 77358550831⟩, ⟨74911423071, 79829727271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 153354240 154009600 139919360 142868480 ⟨⟨79236113069, 79236113075⟩, ⟨76774341944, 81722041455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 154009600 154664960 139919360 142868480 ⟨⟨78894821638, 78894821645⟩, ⟨76441796421, 81371858993⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 152043520 154664960 131072000 142868480 t = true :=
  ⟨_, (join_sr (m := 136970240) (by decide) (join_su (m := 153354240) (by decide) (join_sr (m := 134021120) (by decide) (join_su (m := 152698880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 152698880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 134021120) (by decide) (join_su (m := 154009600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 154009600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 153354240) (by decide) (join_sr (m := 139919360) (by decide) (join_su (m := 152698880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 152698880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 139919360) (by decide) (join_su (m := 154009600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 154009600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (29/160 : ℝ) (59/320 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e1 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
