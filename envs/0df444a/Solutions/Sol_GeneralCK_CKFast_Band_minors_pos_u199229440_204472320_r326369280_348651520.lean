-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_204472320_r326369280_348651520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:41:22.514883+00:00
-- url     : https://prove2.me/submissions/5b347166-b27d-478b-a42d-2e8b4e8dd792

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 39/160]`, `ρ ∈ [249/640, 133/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 200540160 326369280 331939840 ⟨⟨130122239951, 130122239955⟩, ⟨125712026073, 134595269507⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 200540160 201850880 326369280 331939840 ⟨⟨129102347874, 129102347881⟩, ⟨124716164346, 133550898014⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 199229440 200540160 331939840 337510400 ⟨⟨132155315378, 132155315381⟩, ⟨127729138499, 136644261268⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 200540160 201850880 331939840 337510400 ⟨⟨131121906069, 131121906077⟩, ⟨126719793507, 135586343419⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 201850880 203161600 326369280 331939840 ⟨⟨128087950075, 128087950083⟩, ⟨123725583250, 132512239310⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 203161600 204472320 326369280 331939840 ⟨⟨127078971300, 127078971308⟩, ⟨122740210546, 131479215053⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 201850880 203161600 331939840 337510400 ⟨⟨130094012484, 130094012490⟩, ⟨125715751825, 134534158448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 203161600 204472320 331939840 337510400 ⟨⟨129071559423, 129071559430⟩, ⟨124716941235, 133487628112⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 199229440 200540160 337510400 343080960 ⟨⟨134184015529, 134184015533⟩, ⟨129741927097, 138688824807⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 200540160 201850880 337510400 343080960 ⟨⟨133137178304, 133137178311⟩, ⟨128719186591, 137617451492⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 199229440 200540160 343080960 348651520 ⟨⟨136208391781, 136208391785⟩, ⟨131750442530, 140729012212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 200540160 201850880 343080960 348651520 ⟨⟨135148214623, 135148214631⟩, ⟨130714392963, 139644272965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 201850880 203161600 337510400 343080960 ⟨⟨132095876807, 132095876815⟩, ⟨127701770664, 136551829683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 203161600 204472320 337510400 343080960 ⟨⟨131060035919, 131060035927⟩, ⟨126689607133, 135491881256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 201850880 203161600 343080960 348651520 ⟨⟨134093591797, 134093591804⟩, ⟨129683687858, 138565302424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 203161600 204472320 343080960 348651520 ⟨⟨133044448272, 133044448281⟩, ⟨128658255091, 137492022598⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 204472320 326369280 348651520 t = true :=
  ⟨_, (join_sr (m := 337510400) (by decide) (join_su (m := 201850880) (by decide) (join_sr (m := 331939840) (by decide) (join_su (m := 200540160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 200540160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 331939840) (by decide) (join_su (m := 203161600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 203161600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 201850880) (by decide) (join_sr (m := 343080960) (by decide) (join_su (m := 200540160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 200540160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 343080960) (by decide) (join_su (m := 203161600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 203161600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (39/160 : ℝ) →
    rho ∈ Set.Icc (249/640 : ℝ) (133/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e2 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  have e3 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
