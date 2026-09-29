-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_152043520_r225443840_249036800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:54:38.358346+00:00
-- url     : https://prove2.me/submissions/05858198-f784-47cd-8eca-188b597a6eee

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 29/160]`, `ρ ∈ [43/160, 19/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 148111360 225443840 231342080 ⟨⟨127841859048, 127841859052⟩, ⟨122446961073, 133333369207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 148111360 149422080 225443840 231342080 ⟨⟨126811788523, 126811788530⟩, ⟨121454550197, 132264617361⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 146800640 148111360 231342080 237240320 ⟨⟨130791243907, 130791243909⟩, ⟨125376390359, 136302299607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 148111360 149422080 231342080 237240320 ⟨⟨129742284757, 129742284765⟩, ⟨124365086846, 135214679243⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 149422080 150732800 225443840 231342080 ⟨⟨125790990025, 125790990032⟩, ⟨120470926258, 131205639460⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 150732800 152043520 225443840 231342080 ⟨⟨124779298616, 124779298624⟩, ⟨119495933947, 130156260565⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 149422080 150732800 231342080 237240320 ⟨⟨128702667870, 128702667879⟩, ⟨123362644371, 134136898719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 150732800 152043520 231342080 237240320 ⟨⟨127672228259, 127672228268⟩, ⟨122368907419, 133068783212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 146800640 148111360 237240320 243138560 ⟨⟨133726776133, 133726776137⟩, ⟨128292192492, 139257150353⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 148111360 149422080 237240320 243138560 ⟨⟨132659199663, 132659199672⟩, ⟨127262262498, 138150937843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 146800640 148111360 243138560 249036800 ⟨⟨136648683048, 136648683052⟩, ⟨131194589646, 142198153971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 148111360 149422080 243138560 249036800 ⟨⟨135562754327, 135562754336⟩, ⟨130146293275, 141073619264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 149422080 150732800 237240320 243138560 ⟨⟨131601030849, 131601030858⟩, ⟨126241262876, 137054626148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 150732800 152043520 237240320 243138560 ⟨⟨130552104740, 130552104749⟩, ⟨125229037997, 135968040655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 149422080 150732800 243138560 249036800 ⟨⟨134486293984, 134486293992⟩, ⟨129106992010, 139959041615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 150732800 152043520 243138560 249036800 ⟨⟨133419137182, 133419137191⟩, ⟨128076530190, 138854246690⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 152043520 225443840 249036800 t = true :=
  ⟨_, (join_sr (m := 237240320) (by decide) (join_su (m := 149422080) (by decide) (join_sr (m := 231342080) (by decide) (join_su (m := 148111360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 148111360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 231342080) (by decide) (join_su (m := 150732800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 150732800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 149422080) (by decide) (join_sr (m := 243138560) (by decide) (join_su (m := 148111360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 148111360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 243138560) (by decide) (join_su (m := 150732800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 150732800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (29/160 : ℝ) →
    rho ∈ Set.Icc (43/160 : ℝ) (19/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e2 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e3 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
