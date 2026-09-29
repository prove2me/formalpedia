-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_141557760_r225443840_249036800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:43:18.425152+00:00
-- url     : https://prove2.me/submissions/2aee5f11-aab5-486f-840f-32bb31757a64

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 27/160]`, `ρ ∈ [43/160, 19/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 137625600 225443840 231342080 ⟨⟨136437371092, 136437371100⟩, ⟨130722487659, 142257694666⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 137625600 138936320 225443840 231342080 ⟨⟨135326685540, 135326685549⟩, ⟨129653722121, 141103917933⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 136314880 137625600 231342080 237240320 ⟨⟨139540388847, 139540388857⟩, ⟨133805741672, 145379918052⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 137625600 138936320 231342080 237240320 ⟨⟨138410254912, 138410254921⟩, ⟨132717486483, 144206754768⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 138936320 140247040 225443840 231342080 ⟨⟨134226744698, 134226744708⟩, ⟨128595129056, 139961478393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 140247040 141557760 225443840 231342080 ⟨⟨133137348289, 133137348294⟩, ⟨127546520155, 138830163322⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 138936320 140247040 231342080 237240320 ⟨⟨137290935104, 137290935112⟩, ⟨131639478529, 143044992122⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 140247040 141557760 231342080 237240320 ⟨⟨136182229386, 136182229388⟩, ⟨130571529526, 141894417865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 136314880 137625600 237240320 243138560 ⟨⟨142627198355, 142627198363⟩, ⟨136873056947, 148485663098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 137625600 138936320 237240320 243138560 ⟨⟨141477929370, 141477929379⟩, ⟨135765619664, 147293432223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 136314880 137625600 243138560 249036800 ⟨⟨145698083626, 145698083635⟩, ⟨139924710684, 151575220707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 137625600 138936320 243138560 249036800 ⟨⟨144529985125, 144529985134⟩, ⟨138798391295, 150364233158⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 138936320 140247040 237240320 243138560 ⟨⟨140339538341, 140339538351⟩, ⟨134668498866, 146112659773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 140247040 141557760 237240320 243138560 ⟨⟨139211825568, 139211825573⟩, ⟨133581506394, 144943134074⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 138936320 140247040 243138560 249036800 ⟨⟨143372823036, 143372823044⟩, ⟨137682452335, 149164756395⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 140247040 141557760 243138560 249036800 ⟨⟨142226398088, 142226398094⟩, ⟨136576705871, 147976579404⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 141557760 225443840 249036800 t = true :=
  ⟨_, (join_sr (m := 237240320) (by decide) (join_su (m := 138936320) (by decide) (join_sr (m := 231342080) (by decide) (join_su (m := 137625600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 137625600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 231342080) (by decide) (join_su (m := 140247040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 140247040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 138936320) (by decide) (join_sr (m := 243138560) (by decide) (join_su (m := 137625600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 137625600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 243138560) (by decide) (join_su (m := 140247040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 140247040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (27/160 : ℝ) →
    rho ∈ Set.Icc (43/160 : ℝ) (19/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e2 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e3 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
