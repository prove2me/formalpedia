-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_199229440_r393216000_415498240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:48:11.69598+00:00
-- url     : https://prove2.me/submissions/0f8d04b5-214e-40c2-96c6-3afaea417c8b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 19/80]`, `ρ ∈ [15/32, 317/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 193986560 195297280 393216000 398786560 ⟨⟨159005520433, 159005520441⟩, ⟨154307606552, 163767187837⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 195297280 196608000 393216000 398786560 ⟨⟨157805622419, 157805622428⟩, ⟨153132864814, 162541729124⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 193986560 195297280 398786560 404357120 ⟨⟨161039545632, 161039545641⟩, ⟨156326189403, 165816569838⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 195297280 196608000 398786560 404357120 ⟨⟨159827096615, 159827096622⟩, ⟨155138907191, 164578555057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 196608000 197918720 393216000 398786560 ⟨⟨156611693029, 156611693038⟩, ⟨151963883691, 161322450691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 197918720 199229440 393216000 398786560 ⟨⟨155423654178, 155423654187⟩, ⟨150800587837, 160109271676⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 196608000 197918720 398786560 404357120 ⟨⟨158620621281, 158620621290⟩, ⟨153957392306, 163346723843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 197918720 199229440 398786560 404357120 ⟨⟨157420041828, 157420041836⟩, ⟨152781569637, 162120995663⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 193986560 195297280 404357120 409927680 ⟨⟨163069470021, 163069470028⟩, ⟨158340720196, 167861800785⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 195297280 196608000 404357120 409927680 ⟨⟨161844549094, 161844549101⟩, ⟨157140975268, 166611310370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 193986560 195297280 409927680 415498240 ⟨⟨165095343987, 165095343996⟩, ⟨160351248618, 169902931771⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 195297280 196608000 409927680 415498240 ⟨⟨163858029021, 163858029030⟩, ⟨159139117532, 168640044920⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 196608000 197918720 404357120 409927680 ⟨⟨160625605759, 160625605767⟩, ⟨155947003242, 165367005650⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 197918720 199229440 404357120 409927680 ⟨⟨159412562510, 159412562517⟩, ⟨154758729259, 164128806428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 196608000 197918720 409927680 415498240 ⟨⟨162626694436, 162626694443⟩, ⟨157932763814, 167383344749⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 197918720 199229440 409927680 415498240 ⟨⟨161401263026, 161401263033⟩, ⟨156732112872, 166132751412⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 199229440 393216000 415498240 t = true :=
  ⟨_, (join_sr (m := 404357120) (by decide) (join_su (m := 196608000) (by decide) (join_sr (m := 398786560) (by decide) (join_su (m := 195297280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 195297280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 398786560) (by decide) (join_su (m := 197918720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 197918720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 196608000) (by decide) (join_sr (m := 409927680) (by decide) (join_su (m := 195297280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 195297280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 409927680) (by decide) (join_su (m := 197918720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 197918720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (15/32 : ℝ) (317/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  have e3 : (((415498240 : ℤ) : ℝ) / (D : ℝ)) = (317/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
