-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u247726080_249036800_r159252480_164823040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:26:54.130185+00:00
-- url     : https://prove2.me/submissions/2106160a-b419-42bb-a8fd-5f32b8babd2c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [189/640, 19/64]`, `ρ ∈ [243/1280, 503/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 247726080 248053760 159252480 160645120 ⟨⟨47697728956, 47697728961⟩, ⟨46889602155, 48508766878⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 248053760 248381440 159252480 160645120 ⟨⟨47585647522, 47585647524⟩, ⟨46778505402, 48395695167⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247726080 248053760 160645120 162037760 ⟨⟨48102888388, 48102888395⟩, ⟨47293853356, 48914836003⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 248053760 248381440 160645120 162037760 ⟨⟨47989899728, 47989899730⟩, ⟨47181850752, 48800855694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 248381440 248709120 159252480 160645120 ⟨⟨47473708965, 47473708970⟩, ⟨46667549414, 48282768468⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 248709120 249036800 159252480 160645120 ⟨⟨47361912760, 47361912766⟩, ⟨46556733676, 48169986243⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 248381440 248709120 160645120 162037760 ⟨⟨47877054806, 47877054811⟩, ⟨47069989774, 48687021262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 248709120 249036800 160645120 162037760 ⟨⟨47764353096, 47764353103⟩, ⟨46958269902, 48573332164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 247726080 248053760 162037760 163430400 ⟨⟨48507887780, 48507887786⟩, ⟨47697944735, 49320744865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 248053760 248381440 162037760 163430400 ⟨⟨48393992952, 48393992955⟩, ⟨47585037335, 49205857023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 247726080 248053760 163430400 164823040 ⟨⟨48912727491, 48912727497⟩, ⟨48101876651, 49726493825⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 248053760 248381440 163430400 164823040 ⟨⟨48797927553, 48797927556⟩, ⟨47988065508, 49610699512⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 248381440 248709120 162037760 163430400 ⟨⟨48280242720, 48280242725⟩, ⟨47472272415, 49091115916⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 248709120 249036800 162037760 163430400 ⟨⟨48166636555, 48166636560⟩, ⟨47359649455, 48976520997⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 248381440 248709120 163430400 164823040 ⟨⟨48683273062, 48683273067⟩, ⟨47874397694, 49495052784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 248709120 249036800 163430400 164823040 ⟨⟨48568763485, 48568763491⟩, ⟨47760872688, 49379553096⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 247726080 249036800 159252480 164823040 t = true :=
  ⟨_, (join_sr (m := 162037760) (by decide) (join_su (m := 248381440) (by decide) (join_sr (m := 160645120) (by decide) (join_su (m := 248053760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 248053760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 160645120) (by decide) (join_su (m := 248709120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 248709120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 248381440) (by decide) (join_sr (m := 163430400) (by decide) (join_su (m := 248053760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 248053760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 163430400) (by decide) (join_su (m := 248709120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 248709120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (189/640 : ℝ) (19/64 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (503/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((247726080 : ℤ) : ℝ) / (D : ℝ)) = (189/640 : ℝ) := by norm_num [D]
  have e1 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
