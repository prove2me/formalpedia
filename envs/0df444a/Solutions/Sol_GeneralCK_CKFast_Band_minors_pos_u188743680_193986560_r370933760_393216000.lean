-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_193986560_r370933760_393216000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:42:57.130298+00:00
-- url     : https://prove2.me/submissions/61562be5-d177-42e2-a090-09aadfd1c4eb

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 37/160]`, `ρ ∈ [283/640, 15/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 190054400 370933760 376504320 ⟨⟨155483887958, 155483887966⟩, ⟨150745639964, 160287963947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 190054400 191365120 370933760 376504320 ⟨⟨154310448043, 154310448051⟩, ⟨149598188195, 159088092585⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 188743680 190054400 376504320 382074880 ⟨⟨157586444590, 157586444596⟩, ⟨152832504179, 162406110438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 190054400 191365120 376504320 382074880 ⟨⟨156400087531, 156400087538⟩, ⟨151672144630, 161193318524⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 191365120 192675840 370933760 376504320 ⟨⟨153143273713, 153143273721⟩, ⟨148456775413, 157894717763⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 192675840 193986560 370933760 376504320 ⟨⟨151982280667, 151982280672⟩, ⟨147321320441, 156707752002⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 191365120 192675840 376504320 382074880 ⟨⟨155220004953, 155220004962⟩, ⟨150517834725, 159987030150⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 192675840 193986560 376504320 382074880 ⟨⟨154046112835, 154046112837⟩, ⟨149369493516, 158787158161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 188743680 190054400 382074880 387645440 ⟨⟨159684344210, 159684344219⟩, ⟨154914768981, 164519540788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 190054400 191365120 382074880 387645440 ⟨⟨158485159351, 158485159359⟩, ⟨153741589481, 163293919181⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 188743680 190054400 387645440 393216000 ⟨⟨161777644756, 161777644763⟩, ⟨156992491450, 166628313786⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 190054400 191365120 387645440 393216000 ⟨⟨160565720021, 160565720028⟩, ⟨155806578445, 165389951899⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 191365120 192675840 382074880 387645440 ⟨⟨157292256551, 157292256558⟩, ⟨152574468985, 162074806778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 192675840 193986560 382074880 387645440 ⟨⟨156105552079, 156105552084⟩, ⟨151413326787, 160862116768⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 191365120 192675840 387645440 393216000 ⟨⟨159360083639, 159360083647⟩, ⟨154626732532, 164158103580⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 192675840 193986560 387645440 393216000 ⟨⟨158160652183, 158160652187⟩, ⟨153452873267, 162932682370⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 193986560 370933760 393216000 t = true :=
  ⟨_, (join_sr (m := 382074880) (by decide) (join_su (m := 191365120) (by decide) (join_sr (m := 376504320) (by decide) (join_su (m := 190054400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 190054400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 376504320) (by decide) (join_su (m := 192675840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 192675840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 191365120) (by decide) (join_sr (m := 387645440) (by decide) (join_su (m := 190054400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 190054400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 387645440) (by decide) (join_su (m := 192675840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 192675840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (37/160 : ℝ) →
    rho ∈ Set.Icc (283/640 : ℝ) (15/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e2 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  have e3 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
