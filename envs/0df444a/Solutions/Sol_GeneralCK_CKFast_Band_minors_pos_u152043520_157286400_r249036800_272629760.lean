-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u152043520_157286400_r249036800_272629760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:55:46.679473+00:00
-- url     : https://prove2.me/submissions/212e4116-8551-4241-a52c-932ea8a7c497

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [29/160, 3/16]`, `ρ ∈ [19/64, 13/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 152043520 153354240 249036800 254935040 ⟨⟨135197592462, 135197592469⟩, ⟨129871879064, 140614526201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 153354240 154664960 249036800 254935040 ⟨⟨134130695755, 134130695758⟩, ⟨128840772227, 139510939795⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 152043520 153354240 254935040 260833280 ⟨⟨138021865137, 138021865146⟩, ⟨132676997841, 143457597300⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 153354240 154664960 254935040 260833280 ⟨⟨136937337199, 136937337203⟩, ⟨131628251920, 142336401550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 154664960 155975680 249036800 254935040 ⟨⟨133072686912, 133072686921⟩, ⟨127818118798, 138416689467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 155975680 157286400 249036800 254935040 ⟨⟨132023415510, 132023415519⟩, ⟨126803776482, 137331616368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 154664960 155975680 254935040 260833280 ⟨⟨135861749864, 135861749871⟩, ⟨130588015710, 141224590655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 155975680 157286400 254935040 260833280 ⟨⟨134794952847, 134794952856⟩, ⟨129556146929, 140122006044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 152043520 153354240 260833280 266731520 ⟨⟨140834133447, 140834133455⟩, ⟨135470300444, 146288474218⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 153354240 154664960 260833280 266731520 ⟨⟨139732205237, 139732205240⟩, ⟨134404142166, 145149904254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 152043520 153354240 266731520 272629760 ⟨⟨143634586555, 143634586563⟩, ⟨138251972002, 149107350198⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 153354240 154664960 266731520 272629760 ⟨⟨142515483993, 142515483997⟩, ⟨137168623198, 147951635969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 154664960 155975680 260833280 266731520 ⟨⟨138639266438, 138639266445⟩, ⟨133346546037, 144020763933⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 155975680 157286400 260833280 266731520 ⟨⟨137555166975, 137555166982⟩, ⟨132297369847, 142900895037⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 154664960 155975680 266731520 272629760 ⟨⟨141405415856, 141405415864⟩, ⟨136093885236, 146805392326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 155975680 157286400 266731520 272629760 ⟨⟨140304232333, 140304232341⟩, ⟨135027616044, 145668461461⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 152043520 157286400 249036800 272629760 t = true :=
  ⟨_, (join_sr (m := 260833280) (by decide) (join_su (m := 154664960) (by decide) (join_sr (m := 254935040) (by decide) (join_su (m := 153354240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 153354240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 254935040) (by decide) (join_su (m := 155975680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 155975680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 154664960) (by decide) (join_sr (m := 266731520) (by decide) (join_su (m := 153354240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 153354240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 266731520) (by decide) (join_su (m := 155975680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 155975680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (29/160 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (19/64 : ℝ) (13/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e3 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
