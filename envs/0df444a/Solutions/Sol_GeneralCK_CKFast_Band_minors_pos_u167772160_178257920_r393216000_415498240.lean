-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_178257920_r393216000_415498240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:03:54.588213+00:00
-- url     : https://prove2.me/submissions/97e66d99-5baa-4960-9ba5-1258945528c1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 17/80]`, `ρ ∈ [15/32, 317/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 170393600 393216000 398786560 ⟨⟨183719013689, 183719013699⟩, ⟨175050454103, 192586005673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 167772160 170393600 398786560 404357120 ⟨⟨185998285249, 185998285258⟩, ⟨177300967946, 194893597739⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 170393600 173015040 393216000 398786560 ⟨⟨181059128137, 181059128146⟩, ⟨172477325322, 189837103734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 170393600 173015040 398786560 404357120 ⟨⟨183313248463, 183313248472⟩, ⟨174702614113, 192119660109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 167772160 170393600 404357120 409927680 ⟨⟨188271666832, 188271666839⟩, ⟨179545713729, 197195172355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 167772160 170393600 409927680 415498240 ⟨⟨190539238691, 190539238698⟩, ⟨181784769743, 199490811770⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 170393600 173015040 404357120 409927680 ⟨⟨185561685225, 185561685233⟩, ⟨176922335914, 194396410764⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 170393600 173015040 409927680 415498240 ⟨⟨187804515014, 187804515023⟩, ⟨179136565475, 196667434162⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 173015040 175636480 393216000 398786560 ⟨⟨178429899610, 178429899619⟩, ⟨169933232379, 187120523320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 173015040 175636480 398786560 404357120 ⟨⟨180658857944, 180658857951⟩, ⟨172133301293, 189378015564⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 175636480 178257920 393216000 398786560 ⟨⟨175830490489, 175830490493⟩, ⟨167417384121, 184435379342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 175636480 178257920 398786560 404357120 ⟨⟨178034280521, 178034280527⟩, ⟨169592241993, 186667784335⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 173015040 175636480 404357120 409927680 ⟨⟨182882333642, 182882333650⟩, ⟨174327998884, 191629908272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 173015040 175636480 409927680 415498240 ⟨⟨185100399784, 185100399793⟩, ⟨176517396499, 193876276284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 175636480 178257920 404357120 409927680 ⟨⟨180232783460, 180232783463⟩, ⟨171761918905, 188894790521⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 175636480 178257920 409927680 415498240 ⟨⟨182426069017, 182426069022⟩, ⟨173926482945, 191116469262⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 178257920 393216000 415498240 t = true :=
  ⟨_, (join_su (m := 173015040) (by decide) (join_sr (m := 404357120) (by decide) (join_su (m := 170393600) (by decide) (join_sr (m := 398786560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 398786560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 170393600) (by decide) (join_sr (m := 409927680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 409927680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 404357120) (by decide) (join_su (m := 175636480) (by decide) (join_sr (m := 398786560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 398786560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 175636480) (by decide) (join_sr (m := 409927680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 409927680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (15/32 : ℝ) (317/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  have e3 : (((415498240 : ℤ) : ℝ) / (D : ℝ)) = (317/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
