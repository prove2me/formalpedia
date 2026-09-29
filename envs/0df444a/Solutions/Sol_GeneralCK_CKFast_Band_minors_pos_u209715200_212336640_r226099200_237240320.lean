-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_212336640_r226099200_237240320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:07:53.054193+00:00
-- url     : https://prove2.me/submissions/8f834995-d334-4ce5-ad2b-582fd7dbef6f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 81/320]`, `ρ ∈ [69/256, 181/640]` by 13 cells of the computing
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
theorem cell0 : cellOK 209715200 210370560 226099200 228884480 ⟨⟨86450394344, 86450394352⟩, ⟨84475108743, 88440538957⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 210370560 211025920 226099200 228884480 ⟨⟨86089676969, 86089676976⟩, ⟨84119785718, 88074366742⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 209715200 210370560 228884480 231669760 ⟨⟨87453274590, 87453274597⟩, ⟨85473860214, 89447549718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 210370560 211025920 228884480 231669760 ⟨⟨87088797844, 87088797850⟩, ⟨85114786719, 89077609457⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 211025920 211681280 226099200 228884480 ⟨⟨85730038231, 85730038234⟩, ⟨83765515409, 87709299472⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 211681280 212336640 226099200 228884480 ⟨⟨85371470179, 85371470185⟩, ⟨83412290068, 87345329000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 211025920 211681280 228884480 231669760 ⟨⟨86725406157, 86725406161⟩, ⟨84756772387, 88708780536⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 211681280 212336640 228884480 231669760 ⟨⟨86363091551, 86363091557⟩, ⟨84399809445, 88341054775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 209715200 211025920 231669760 234455040 ⟨⟨88270760261, 88270760267⟩, ⟨84944462975, 91638025943⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 209715200 211025920 234455040 237240320 ⟨⟨89269487119, 89269487127⟩, ⟨85935628021, 92644337843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 211025920 211681280 231669760 234455040 ⟨⟨87719653683, 87719653685⟩, ⟨85746915145, 89707134927⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 211681280 212336640 231669760 234455040 ⟨⟨87353605157, 87353605163⟩, ⟨85386227123, 89335666629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 211025920 212336640 234455040 237240320 ⟨⟨88527766290, 88527766296⟩, ⟨85209370146, 91886873065⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 212336640 226099200 237240320 t = true :=
  ⟨_, (join_sr (m := 231669760) (by decide) (join_su (m := 211025920) (by decide) (join_sr (m := 228884480) (by decide) (join_su (m := 210370560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 210370560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 228884480) (by decide) (join_su (m := 211681280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 211681280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 211025920) (by decide) (join_sr (m := 234455040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 234455040) (by decide) (join_su (m := 211681280) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (81/320 : ℝ) →
    rho ∈ Set.Icc (69/256 : ℝ) (181/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((212336640 : ℤ) : ℝ) / (D : ℝ)) = (81/320 : ℝ) := by norm_num [D]
  have e2 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  have e3 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
