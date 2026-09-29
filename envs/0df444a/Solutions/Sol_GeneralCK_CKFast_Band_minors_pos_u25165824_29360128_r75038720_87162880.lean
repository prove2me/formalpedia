-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u25165824_29360128_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:20:34.742891+00:00
-- url     : https://prove2.me/submissions/7392d88b-6cb7-4f69-974a-bab9b11da1a7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/100, 7/200]`, `ρ ∈ [229/2560, 133/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 25165824 26214400 75038720 78069760 ⟨⟨160935117386, 160935117409⟩, ⟨149187705286, 173186378415⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 25165824 26214400 78069760 81100800 ⟨⟨165387277840, 165387277860⟩, ⟨153675876429, 177590238976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 26214400 27262976 75038720 78069760 ⟨⟨157775849783, 157775849802⟩, ⟨146319612529, 169714693124⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 26214400 27262976 78069760 81100800 ⟨⟨162190435040, 162190435058⟩, ⟨150765718564, 174086364579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 25165824 26214400 81100800 84131840 ⟨⟨169751155053, 169751155073⟩, ⟨158076808403, 181905179313⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 25165824 26214400 84131840 87162880 ⟨⟨174030424607, 174030424626⟩, ⟨162394038054, 186134997460⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 26214400 27262976 81100800 84131840 ⟨⟨166519470760, 166519470779⟩, ⟨155127368671, 178371756343⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 26214400 27262976 84131840 87162880 ⟨⟨170766440357, 170766440380⟩, ⟨159407912818, 182574471421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 27262976 28311552 75038720 78069760 ⟨⟨154745716708, 154745716727⟩, ⟨143565804320, 166388366559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 27262976 28311552 78069760 81100800 ⟨⟨159122235862, 159122235885⟩, ⟨147969777751, 170726852607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 28311552 29360128 75038720 78069760 ⟨⟨151836426706, 151836426728⟩, ⟨140919099711, 163197879454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 28311552 29360128 78069760 81100800 ⟨⟨156174531916, 156174531938⟩, ⟨145280970989, 167502381018⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 27262976 28311552 81100800 84131840 ⟨⟨163415848470, 163415848493⟩, ⟨152291974769, 174981627080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 27262976 28311552 84131840 87162880 ⟨⟨167629857311, 167629857334⟩, ⟨156535570096, 179156109025⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 28311552 29360128 81100800 84131840 ⟨⟨160432283823, 160432283840⟩, ⟨149563644724, 171725664839⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 28311552 29360128 84131840 87162880 ⟨⟨164612815390, 164612815407⟩, ⟨153770131249, 175870976478⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 25165824 29360128 75038720 87162880 t = true :=
  ⟨_, (join_su (m := 27262976) (by decide) (join_sr (m := 81100800) (by decide) (join_su (m := 26214400) (by decide) (join_sr (m := 78069760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 78069760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 26214400) (by decide) (join_sr (m := 84131840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 84131840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 81100800) (by decide) (join_su (m := 28311552) (by decide) (join_sr (m := 78069760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 78069760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 28311552) (by decide) (join_sr (m := 84131840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 84131840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/100 : ℝ) (7/200 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e1 : (((29360128 : ℤ) : ℝ) / (D : ℝ)) = (7/200 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
