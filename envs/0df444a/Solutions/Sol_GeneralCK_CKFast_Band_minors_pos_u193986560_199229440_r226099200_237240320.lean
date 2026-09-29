-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_199229440_r226099200_237240320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:25:11.002339+00:00
-- url     : https://prove2.me/submissions/d4ea3afd-bac2-4077-933c-ded5c48662db

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 19/80]`, `ρ ∈ [69/256, 181/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 193986560 195297280 226099200 228884480 ⟨⟨95258402089, 95258402096⟩, ⟨91749805800, 98811642311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 193986560 195297280 228884480 231669760 ⟨⟨96351545038, 96351545046⟩, ⟨92835021377, 99912721146⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 195297280 196608000 226099200 228884480 ⟨⟨94482618594, 94482618600⟩, ⟨90991450509, 98018096676⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 195297280 196608000 228884480 231669760 ⟨⟨95567931880, 95567931888⟩, ⟨92068864104, 99111319652⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 193986560 195297280 231669760 234455040 ⟨⟨97443202210, 97443202216⟩, ⟨93918765354, 101012299669⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 193986560 195297280 234455040 237240320 ⟨⟨98533382449, 98533382455⟩, ⟨95001046481, 102110386818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 195297280 196608000 231669760 234455040 ⟨⟨96651791268, 96651791274⟩, ⟨93144837510, 100203074663⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 195297280 196608000 234455040 237240320 ⟨⟨97734205349, 97734205357⟩, ⟨94219379230, 101293370400⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 196608000 197918720 226099200 228884480 ⟨⟨93711945301, 93711945308⟩, ⟨90238018741, 97229852497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 196608000 197918720 228884480 231669760 ⟨⟨94789457137, 94789457145⟩, ⟨91307658835, 98315247513⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 197918720 199229440 226099200 228884480 ⟨⟨92946304698, 92946304706⟩, ⟨89489435996, 96446829165⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 197918720 199229440 228884480 231669760 ⟨⟨94016043073, 94016043080⟩, ⟨90551330835, 97524423914⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 196608000 197918720 231669760 234455040 ⟨⟨95865546369, 95865546375⟩, ⟨92375889575, 99399206325⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 196608000 197918720 234455040 237240320 ⟨⟨96940221348, 96940221354⟩, ⟨93442719229, 100481737374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 197918720 199229440 231669760 234455040 ⟨⟨95084389565, 95084389571⟩, ⟨91611846592, 98600613635⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 197918720 199229440 234455040 237240320 ⟨⟨96151352290, 96151352298⟩, ⟨92670991303, 99675406533⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 199229440 226099200 237240320 t = true :=
  ⟨_, (join_su (m := 196608000) (by decide) (join_sr (m := 231669760) (by decide) (join_su (m := 195297280) (by decide) (join_sr (m := 228884480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 228884480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 195297280) (by decide) (join_sr (m := 234455040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 234455040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 231669760) (by decide) (join_su (m := 197918720) (by decide) (join_sr (m := 228884480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 228884480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 197918720) (by decide) (join_sr (m := 234455040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 234455040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (69/256 : ℝ) (181/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  have e3 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
