-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_241172480_r772014080_794296320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:08:50.3657+00:00
-- url     : https://prove2.me/submissions/34bc291c-78fc-45f4-972e-b195164bac7d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 23/80]`, `ρ ∈ [589/640, 303/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 233308160 772014080 777584640 ⟨⟨237034920323, 237034920332⟩, ⟨228251681280, 245977883256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 233308160 777584640 783155200 ⟨⟨238608942146, 238608942156⟩, ⟨229799103500, 247578443960⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 233308160 235929600 772014080 777584640 ⟨⟨233423295558, 233423295567⟩, ⟨224703231404, 242302926916⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 233308160 235929600 777584640 783155200 ⟨⟨234977112837, 234977112846⟩, ⟨226230466758, 243883288628⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230686720 233308160 783155200 788725760 ⟨⟨240182068945, 240182068954⟩, ⟨231345631979, 249178103861⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230686720 233308160 788725760 794296320 ⟨⟨241754317588, 241754317598⟩, ⟨232891283299, 250776880096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 233308160 235929600 783155200 788725760 ⟨⟨236530070429, 236530070438⟩, ⟨227756842391, 245462786316⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 233308160 235929600 788725760 794296320 ⟨⟨238082184477, 238082184487⟩, ⟨229282374170, 247041436376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 238551040 772014080 777584640 ⟨⟨229825355900, 229825355909⟩, ⟨221168096580, 238642008355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 235929600 238551040 777584640 783155200 ⟨⟨231358877855, 231358877865⟩, ⟨222675063078, 240202070939⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 238551040 241172480 772014080 777584640 ⟨⟨226240815534, 226240815543⟩, ⟨217645996018, 234994837248⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 238551040 241172480 777584640 783155200 ⟨⟨227753953801, 227753953810⟩, ⟨219132613891, 236534503175⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 235929600 238551040 783155200 788725760 ⟨⟨232891574616, 232891574626⟩, ⟨224181203049, 241761305412⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 235929600 238551040 788725760 794296320 ⟨⟨234423461620, 234423461628⟩, ⟨225686531676, 243319727442⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 238551040 241172480 783155200 788725760 ⟨⟨229266300518, 229266300527⟩, ⟨220618437619, 238073376028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 238551040 241172480 788725760 794296320 ⟨⟨230777870440, 230777870449⟩, ⟨222103481709, 239611470780⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 241172480 772014080 794296320 t = true :=
  ⟨_, (join_su (m := 235929600) (by decide) (join_sr (m := 783155200) (by decide) (join_su (m := 233308160) (by decide) (join_sr (m := 777584640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 777584640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 233308160) (by decide) (join_sr (m := 788725760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 788725760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 783155200) (by decide) (join_su (m := 238551040) (by decide) (join_sr (m := 777584640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 777584640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 238551040) (by decide) (join_sr (m := 788725760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 788725760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (589/640 : ℝ) (303/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((772014080 : ℤ) : ℝ) / (D : ℝ)) = (589/640 : ℝ) := by norm_num [D]
  have e3 : (((794296320 : ℤ) : ℝ) / (D : ℝ)) = (303/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
