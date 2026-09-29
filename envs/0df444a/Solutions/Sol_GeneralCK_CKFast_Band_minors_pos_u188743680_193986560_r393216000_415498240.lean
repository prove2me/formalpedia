-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_193986560_r393216000_415498240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:47:14.535443+00:00
-- url     : https://prove2.me/submissions/5e60f4a6-a5ec-4e85-88a9-dbbac2b5aa36

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 37/160]`, `ρ ∈ [15/32, 317/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 190054400 393216000 398786560 ⟨⟨163866403542, 163866403551⟩, ⟨159065728069, 168732487597⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 190054400 191365120 393216000 398786560 ⟨⟨162641825466, 162641825475⟩, ⟨157867166634, 167481473425⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 188743680 190054400 398786560 404357120 ⟨⟨165950677290, 165950677299⟩, ⟨161134534723, 170832119773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 190054400 191365120 398786560 404357120 ⟨⟨164713531034, 164713531041⟩, ⟨159923408595, 169568539907⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 191365120 192675840 393216000 398786560 ⟨⟨161423540780, 161423540788⟩, ⟨156674679145, 166236975909⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 192675840 193986560 393216000 398786560 ⟨⟨160211466374, 160211466378⟩, ⟨155488185425, 164998908961⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 191365120 192675840 398786560 404357120 ⟨⟨163482681977, 163482681984⟩, ⟨158718362054, 168311478545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 192675840 193986560 398786560 404357120 ⟨⟨162258047341, 162258047347⟩, ⟨157519315205, 167060849982⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 188743680 190054400 404357120 409927680 ⟨⟨168030522125, 168030522132⟩, ⟨163198966724, 172927267261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 190054400 191365120 404357120 409927680 ⟨⟨166780891497, 166780891504⟩, ⟨161975358312, 171651206914⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 188743680 190054400 409927680 415498240 ⟨⟨170105993587, 170105993596⟩, ⟨165259078809, 175017986415⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 190054400 191365120 409927680 415498240 ⟨⟨168843961066, 168843961075⟩, ⟨164023069218, 173729529443⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 191365120 192675840 404357120 409927680 ⟨⟨165537560682, 165537560689⟩, ⟨160757833946, 170381665708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 192675840 193986560 404357120 409927680 ⟨⟨164300447247, 164300447249⟩, ⟨159546314029, 169118558333⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 191365120 192675840 409927680 415498240 ⟨⟨167588229804, 167588229813⟩, ⟨162793146979, 172447591068⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 192675840 193986560 409927680 415498240 ⟨⟨166338717719, 166338717725⟩, ⟨161569232801, 171172086381⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 193986560 393216000 415498240 t = true :=
  ⟨_, (join_sr (m := 404357120) (by decide) (join_su (m := 191365120) (by decide) (join_sr (m := 398786560) (by decide) (join_su (m := 190054400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 190054400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 398786560) (by decide) (join_su (m := 192675840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 192675840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 191365120) (by decide) (join_sr (m := 409927680) (by decide) (join_su (m := 190054400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 190054400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 409927680) (by decide) (join_su (m := 192675840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 192675840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (37/160 : ℝ) →
    rho ∈ Set.Icc (15/32 : ℝ) (317/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e2 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  have e3 : (((415498240 : ℤ) : ℝ) / (D : ℝ)) = (317/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
