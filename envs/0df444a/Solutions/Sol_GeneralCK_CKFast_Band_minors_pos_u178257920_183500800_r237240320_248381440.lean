-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_183500800_r237240320_248381440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:18:42.339663+00:00
-- url     : https://prove2.me/submissions/b59f00a7-3c40-4b09-a408-5454e8c668be

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 7/32]`, `ρ ∈ [181/640, 379/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 179568640 237240320 240025600 ⟨⟨109742788699, 109742788707⟩, ⟨105976490695, 113558073598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178257920 179568640 240025600 242810880 ⟨⟨110924571368, 110924571376⟩, ⟨107150121677, 114747993298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 179568640 180879360 237240320 240025600 ⟨⟨108866561022, 108866561026⟩, ⟨105120281819, 112661439336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 179568640 180879360 240025600 242810880 ⟨⟨110040315349, 110040315353⟩, ⟨106285905364, 113843311892⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 178257920 179568640 242810880 245596160 ⟨⟨112104485596, 112104485604⟩, ⟨108321904196, 115936024163⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 178257920 179568640 245596160 248381440 ⟨⟨113282543477, 113282543484⟩, ⟨109491850196, 117122178438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 179568640 180879360 242810880 245596160 ⟨⟨111212239594, 111212239598⟩, ⟨107449718235, 115023334544⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 179568640 180879360 245596160 248381440 ⟨⟨112382345516, 112382345518⟩, ⟨108611732047, 116201519203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 180879360 182190080 237240320 240025600 ⟨⟨107996618148, 107996618154⟩, ⟨104270131140, 111771322007⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 180879360 182190080 240025600 242810880 ⟨⟨109162372100, 109162372108⟩, ⟨105427775730, 112945174815⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 182190080 183500800 237240320 240025600 ⟨⟨107132861554, 107132861560⟩, ⟨103425943986, 110887619125⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 182190080 183500800 240025600 242810880 ⟨⟨108290642943, 108290642950⟩, ⟨104575637923, 112053479449⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 180879360 182190080 242810880 245596160 ⟨⟨110326333645, 110326333653⟩, ⟨106583646761, 114117215961⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 180879360 182190080 245596160 248381440 ⟨⟨111488514221, 111488514228⟩, ⟨107737755531, 115287457019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 182190080 183500800 242810880 245596160 ⟨⟨109446668932, 109446668939⟩, ⟨105723594758, 113217565669⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 182190080 183500800 245596160 248381440 ⟨⟨110600950640, 110600950647⟩, ⟨106869825479, 114379889042⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 183500800 237240320 248381440 t = true :=
  ⟨_, (join_su (m := 180879360) (by decide) (join_sr (m := 242810880) (by decide) (join_su (m := 179568640) (by decide) (join_sr (m := 240025600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 240025600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 179568640) (by decide) (join_sr (m := 245596160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 245596160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 242810880) (by decide) (join_su (m := 182190080) (by decide) (join_sr (m := 240025600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 240025600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 182190080) (by decide) (join_sr (m := 245596160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 245596160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (7/32 : ℝ) →
    rho ∈ Set.Icc (181/640 : ℝ) (379/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e2 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e3 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
