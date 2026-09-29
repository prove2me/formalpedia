-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_37748736_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:35:58.946191+00:00
-- url     : https://prove2.me/submissions/64022152-468c-4437-b037-34ed2b03e0a2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/25, 9/200]`, `ρ ∈ [229/2560, 133/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 33554432 34603008 75038720 78069760 ⟨⟨138858632585, 138858632605⟩, ⟨129080096430, 149003764615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 33554432 34603008 78069760 81100800 ⟨⟨143003164613, 143003164629⟩, ⟨133234396383, 153131547247⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 34603008 35651584 75038720 78069760 ⟨⟨136535586651, 136535586671⟩, ⟨126955262664, 146469565775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 34603008 35651584 78069760 81100800 ⟨⟨140641649115, 140641649131⟩, ⟨131068989412, 150561421386⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 33554432 34603008 81100800 84131840 ⟨⟨147078827604, 147078827624⟩, ⟨137321001594, 157189458962⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 33554432 34603008 84131840 87162880 ⟨⟨151088045276, 151088045292⟩, ⟨141342238823, 161180015848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 34603008 35651584 81100800 84131840 ⟨⟨144680899363, 144680899383⟩, ⟨135117067690, 154585456935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 34603008 35651584 84131840 87162880 ⟨⟨148655643187, 148655643206⟩, ⟨139101710991, 158544066592⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 35651584 36700160 75038720 78069760 ⟨⟨134291722319, 134291722339⟩, ⟨124901223409, 144023643788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 35651584 36700160 78069760 81100800 ⟨⟨138359528731, 138359528750⟩, ⟨128974772123, 148079569873⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 36700160 37748736 75038720 78069760 ⟨⟨132122784168, 132122784183⟩, ⟨122914245609, 141661169368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 36700160 37748736 78069760 81100800 ⟨⟨136152588159, 136152588178⟩, ⟨126948034630, 145681223740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 35651584 36700160 81100800 84131840 ⟨⟨142362505764, 142362505779⟩, ⟨132984641710, 152069657459⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 35651584 36700160 84131840 87162880 ⟨⟨146302848064, 146302848083⟩, ⟨136932939009, 155996185672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 36700160 37748736 81100800 84131840 ⟨⟨140119474271, 140119474291⟩, ⟨130920040142, 149637353781⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 36700160 37748736 84131840 87162880 ⟨⟨144025532374, 144025532389⟩, ⟨134832268491, 153531730039⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 33554432 37748736 75038720 87162880 t = true :=
  ⟨_, (join_su (m := 35651584) (by decide) (join_sr (m := 81100800) (by decide) (join_su (m := 34603008) (by decide) (join_sr (m := 78069760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 78069760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 34603008) (by decide) (join_sr (m := 84131840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 84131840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 81100800) (by decide) (join_su (m := 36700160) (by decide) (join_sr (m := 78069760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 78069760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 36700160) (by decide) (join_sr (m := 84131840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 84131840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (9/200 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e1 : (((37748736 : ℤ) : ℝ) / (D : ℝ)) = (9/200 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
