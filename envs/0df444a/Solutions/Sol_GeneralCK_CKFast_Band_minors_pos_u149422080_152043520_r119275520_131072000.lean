-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u149422080_152043520_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:09:43.673253+00:00
-- url     : https://prove2.me/submissions/4412f03a-71c7-4233-b798-059a85a55af9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [57/320, 29/160]`, `ρ ∈ [91/640, 5/32]` by 20 cells of the computing
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
theorem cell0 : cellOK 149422080 150077440 119275520 120750080 ⟨⟨69783743361, 69783743367⟩, ⟨67807439407, 71776079245⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 149422080 150077440 120750080 122224640 ⟨⟨70587083062, 70587083069⟩, ⟨68608021016, 72582168963⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 150077440 150732800 119275520 120750080 ⟨⟨69475910246, 69475910252⟩, ⟨67506115381, 71461643971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 150077440 150732800 120750080 122224640 ⟨⟨70276114616, 70276114624⟩, ⟨68303568642, 72264591653⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 149422080 150077440 122224640 125173760 ⟨⟨71789929930, 71789929936⟩, ⟨69310911612, 74294262965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 150077440 150732800 122224640 125173760 ⟨⟨71474282889, 71474282895⟩, ⟨69004303560, 73969417067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 150732800 151388160 119275520 120750080 ⟨⟨69169748912, 69169748918⟩, ⟨67206414306, 71148930243⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 150732800 151388160 120750080 122224640 ⟨⟨69966830405, 69966830414⟩, ⟨68000751683, 71948748323⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 151388160 152043520 119275520 120750080 ⟨⟨68865242244, 68865242251⟩, ⟨66908319618, 70837920379⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 151388160 152043520 120750080 122224640 ⟨⟨69659213226, 69659213233⟩, ⟨67699553492, 71634621205⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 150732800 151388160 122224640 125173760 ⟨⟨71160338490, 71160338497⟩, ⟨68699332730, 73646340827⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 151388160 152043520 122224640 125173760 ⟨⟨70848079393, 70848079399⟩, ⟨68395982525, 73325016146⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 149422080 150077440 125173760 128122880 ⟨⟨73389715075, 73389715082⟩, ⟨70904504003, 75900198590⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 150077440 150732800 125173760 128122880 ⟨⟨73067875035, 73067875042⟩, ⟨70591718719, 75569144938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 149422080 150077440 128122880 131072000 ⟨⟨74984953050, 74984953057⟩, ⟨72493590838, 77501545221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 150077440 150732800 128122880 131072000 ⟨⟨74656970999, 74656971007⟩, ⟨72174678714, 77164335402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 150732800 151388160 125173760 128122880 ⟨⟨72747761669, 72747761677⟩, ⟨70280594753, 75239884896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 151388160 152043520 125173760 128122880 ⟨⟨72429357462, 72429357469⟩, ⟨69971115330, 74912400191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 150732800 151388160 128122880 131072000 ⟨⟨74330739082, 74330739088⟩, ⟨71857451437, 76828942560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell19 : cellOK 151388160 152043520 128122880 131072000 ⟨⟨74006239613, 74006239620⟩, ⟨71541892064, 76495348262⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 149422080 152043520 119275520 131072000 t = true :=
  ⟨_, (join_sr (m := 125173760) (by decide) (join_su (m := 150732800) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 150077440) (by decide) (join_sr (m := 120750080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 120750080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 150077440) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 122224640) (by decide) (join_su (m := 151388160) (by decide) (join_sr (m := 120750080) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 120750080) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 151388160) (by decide) (leaf_ok cell10) (leaf_ok cell11)))) (join_su (m := 150732800) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 150077440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 150077440) (by decide) (leaf_ok cell14) (leaf_ok cell15))) (join_sr (m := 128122880) (by decide) (join_su (m := 151388160) (by decide) (leaf_ok cell16) (leaf_ok cell17)) (join_su (m := 151388160) (by decide) (leaf_ok cell18) (leaf_ok cell19)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (57/320 : ℝ) (29/160 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((149422080 : ℤ) : ℝ) / (D : ℝ)) = (57/320 : ℝ) := by norm_num [D]
  have e1 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
