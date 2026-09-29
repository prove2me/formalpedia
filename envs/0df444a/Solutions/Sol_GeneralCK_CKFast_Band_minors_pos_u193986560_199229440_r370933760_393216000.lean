-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_199229440_r370933760_393216000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:43:12.981865+00:00
-- url     : https://prove2.me/submissions/192b481a-c747-413a-aa19-4f5166300b5f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 19/80]`, `ρ ∈ [283/640, 15/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 193986560 195297280 370933760 376504320 ⟨⟨150827385949, 150827385957⟩, ⟨146191743397, 155527109221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 195297280 196608000 370933760 376504320 ⟨⟨149678507928, 149678507935⟩, ⟨145067965657, 154352704718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 193986560 195297280 376504320 382074880 ⟨⟨152878328478, 152878328487⟩, ⟨148227041344, 157593616793⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 195297280 196608000 376504320 382074880 ⟨⟨151716570511, 151716570518⟩, ⟨147090399786, 156406321646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 196608000 197918720 370933760 376504320 ⟨⟨148535566251, 148535566259⟩, ⟨143949909833, 153184455133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 197918720 199229440 370933760 376504320 ⟨⟨147398481836, 147398481843⟩, ⟨142837499747, 152022278419⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 196608000 197918720 376504320 382074880 ⟨⟨150560758820, 150560758827⟩, ⟨145959491654, 155225189643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 197918720 199229440 376504320 382074880 ⟨⟨149410814550, 149410814559⟩, ⟨144834240957, 154050139018⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 193986560 195297280 382074880 387645440 ⟨⟨154924963520, 154924963529⟩, ⟨150258083461, 159655763710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 195297280 196608000 382074880 387645440 ⟨⟨153750409765, 153750409774⟩, ⟨149108660807, 158455663523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 193986560 195297280 387645440 393216000 ⟨⟨156967343530, 156967343539⟩, ⟨152284921467, 161713603172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 195297280 196608000 387645440 393216000 ⟨⟨155780076852, 155780076860⟩, ⟨151122799169, 160500782230⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 196608000 197918720 382074880 387645440 ⟨⟨152581810958, 152581810967⟩, ⟨147964981848, 157261733433⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 197918720 199229440 382074880 387645440 ⟨⟨151419088487, 151419088496⟩, ⟨146826970793, 156073891958⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 196608000 197918720 387645440 393216000 ⟨⟨154598772561, 154598772569⟩, ⟨149966429620, 159294137086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 197918720 199229440 387645440 393216000 ⟨⟨153423352304, 153423352311⟩, ⟨148815737244, 158093586563⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 199229440 370933760 393216000 t = true :=
  ⟨_, (join_sr (m := 382074880) (by decide) (join_su (m := 196608000) (by decide) (join_sr (m := 376504320) (by decide) (join_su (m := 195297280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 195297280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 376504320) (by decide) (join_su (m := 197918720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 197918720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 196608000) (by decide) (join_sr (m := 387645440) (by decide) (join_su (m := 195297280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 195297280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 387645440) (by decide) (join_su (m := 197918720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 197918720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (283/640 : ℝ) (15/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  have e3 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
