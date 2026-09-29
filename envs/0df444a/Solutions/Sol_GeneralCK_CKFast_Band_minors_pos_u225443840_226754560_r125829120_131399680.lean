-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_226754560_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:49:08.957592+00:00
-- url     : https://prove2.me/submissions/59bb4dbe-3c13-4f78-97d6-b37c219a6b44

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 173/640]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 225771520 125829120 127221760 ⟨⟨44353186423, 44353186429⟩, ⟨43496983470, 45212700492⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 225771520 226099200 125829120 127221760 ⟨⟨44253832473, 44253832478⟩, ⟨43398740760, 45112228128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 225443840 225771520 127221760 128614400 ⟨⟨44828329673, 44828329680⟩, ⟨43971107655, 45688863923⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 225771520 226099200 127221760 128614400 ⟨⟨44727965390, 44727965397⟩, ⟨43871856235, 45587379613⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 226099200 226426880 125829120 127221760 ⟨⟨44154634953, 44154634958⟩, ⟨43300651796, 45011914904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 226426880 226754560 125829120 127221760 ⟨⟨44055593251, 44055593257⟩, ⟨43202715974, 44911760200⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 226099200 226426880 127221760 128614400 ⟨⟨44627758797, 44627758804⟩, ⟨43772759818, 45486055704⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 226426880 226754560 127221760 128614400 ⟨⟨44527709278, 44527709285⟩, ⟨43673817797, 45384891574⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 225771520 128614400 130007040 ⟨⟨45303210636, 45303210641⟩, ⟨44444970170, 46164764447⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 225771520 226099200 128614400 130007040 ⟨⟨45201837654, 45201837661⟩, ⟨44344711667, 46062269830⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 225443840 225771520 130007040 131399680 ⟨⟨45777829972, 45777829977⟩, ⟨44918571673, 46640402722⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 225771520 226099200 130007040 131399680 ⟨⟨45675449919, 45675449926⟩, ⟨44817307708, 46536899436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 226099200 226426880 128614400 130007040 ⟨⟨45100623614, 45100623619⟩, ⟨44244609414, 45959936869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 226426880 226754560 128614400 130007040 ⟨⟨44999567894, 44999567899⟩, ⟨44144662803, 45857764933⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 226099200 226426880 130007040 131399680 ⟨⟨45573230051, 45573230056⟩, ⟨44716201232, 46433559049⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 226426880 226754560 130007040 131399680 ⟨⟨45471169741, 45471169746⟩, ⟨44615251634, 46330380927⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 226754560 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 226099200) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 225771520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 225771520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 226426880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 226426880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 226099200) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 225771520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 225771520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 226426880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 226426880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (173/640 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((226754560 : ℤ) : ℝ) / (D : ℝ)) = (173/640 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
