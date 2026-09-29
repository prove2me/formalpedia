-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u237240320_238551040_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:46:57.225178+00:00
-- url     : https://prove2.me/submissions/ded0d43c-2260-4e26-bf4a-4f33f2ae5756

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [181/640, 91/320]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 237240320 237568000 142540800 143933440 ⟨⟨46131555345, 46131555351⟩, ⟨45302219976, 46963974802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 237568000 237895680 142540800 143933440 ⟨⟨46025944446, 46025944451⟩, ⟨45197648181, 46857318532⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 237240320 237568000 143933440 145326080 ⟨⟨46568619667, 46568619673⟩, ⟨45738326893, 47401997852⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 237568000 237895680 143933440 145326080 ⟨⟨46462057143, 46462057149⟩, ⟨45632804954, 47294388483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 237895680 238223360 142540800 143933440 ⟨⟨45920482547, 45920482553⟩, ⟨45093223030, 46750813642⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 238223360 238551040 142540800 143933440 ⟨⟨45815169089, 45815169092⟩, ⟨44988943973, 46644459555⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 237895680 238223360 143933440 145326080 ⟨⟨46355644653, 46355644660⟩, ⟨45527430689, 47186931530⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 238223360 238551040 143933440 145326080 ⟨⟨46249381632, 46249381635⟩, ⟨45422203545, 47079626411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 237240320 237568000 145326080 146718720 ⟨⟨47005481201, 47005481206⟩, ⟨46174231399, 47839817731⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 237568000 237895680 145326080 146718720 ⟨⟨46897968353, 46897968358⟩, ⟨46067760611, 47731256569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 237240320 237568000 146718720 148111360 ⟨⟨47442140425, 47442140430⟩, ⟨46609933976, 48277434919⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 237568000 237895680 146718720 148111360 ⟨⟨47333678549, 47333678555⟩, ⟨46502515628, 48167923267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 237895680 238223360 145326080 146718720 ⟨⟨46790606564, 46790606569⟩, ⟨45961438521, 47622848850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 238223360 238551040 145326080 146718720 ⟨⟨46683395268, 46683395269⟩, ⟨45855264571, 47514593991⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 237895680 238223360 146718720 148111360 ⟨⟨47225368752, 47225368757⟩, ⟨46395246996, 48058566078⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 238223360 238551040 146718720 148111360 ⟨⟨47117210461, 47117210464⟩, ⟨46288127519, 47949362765⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 237240320 238551040 142540800 148111360 t = true :=
  ⟨_, (join_sr (m := 145326080) (by decide) (join_su (m := 237895680) (by decide) (join_sr (m := 143933440) (by decide) (join_su (m := 237568000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 237568000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 143933440) (by decide) (join_su (m := 238223360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 238223360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 237895680) (by decide) (join_sr (m := 146718720) (by decide) (join_su (m := 237568000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 237568000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 146718720) (by decide) (join_su (m := 238223360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 238223360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (181/640 : ℝ) (91/320 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e1 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
