-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u238551040_241172480_r159252480_164823040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:13:59.32766+00:00
-- url     : https://prove2.me/submissions/edf8469f-0a90-4463-af77-4af3617dc88e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [91/320, 23/80]`, `ρ ∈ [243/1280, 503/2560]` by 18 cells of the computing
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
theorem cell0 : cellOK 238551040 239206400 159252480 160645120 ⟨⟨50838057415, 50838057420⟩, ⟨49413706519, 52271017734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 238551040 239206400 160645120 162037760 ⟨⟨51268513994, 51268514001⟩, ⟨49842415806, 52703227260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 239206400 239861760 159252480 160645120 ⟨⟨50605763884, 50605763889⟩, ⟨49184344597, 52035763924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 239206400 239861760 160645120 162037760 ⟨⟨51034357372, 51034357377⟩, ⟨49611195464, 52466105716⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 238551040 239206400 162037760 163430400 ⟨⟨51698779078, 51698779084⟩, ⟨50270934009, 53135244868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 238551040 239206400 163430400 164823040 ⟨⟨52128853117, 52128853123⟩, ⟨50699261581, 53567071009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 239206400 239861760 162037760 163430400 ⟨⟨51462761808, 51462761815⟩, ⟨50037857678, 52896258046⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 239206400 239861760 163430400 164823040 ⟨⟨51890977638, 51890977643⟩, ⟨50464331680, 53326221365⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 239861760 240189440 159252480 160645120 ⟨⟨50431957877, 50431957878⟩, ⟨49599544506, 51267421999⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 240189440 240517120 159252480 160645120 ⟨⟨50316283311, 50316283316⟩, ⟨49484907698, 51150703644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 239861760 240517120 160645120 162037760 ⟨⟨50800835171, 50800835177⟩, ⟨49380595449, 52229632874⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 240517120 240844800 159252480 160645120 ⟨⟨50200764952, 50200764957⟩, ⟨49370424794, 51034143818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 240844800 241172480 159252480 160645120 ⟨⟨50085402217, 50085402223⟩, ⟨49256095214, 50917741933⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 240517120 241172480 160645120 162037760 ⟨⟨50567942683, 50567942685⟩, ⟨49150611149, 51993803924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 239861760 240517120 162037760 163430400 ⟨⟨51227382679, 51227382685⟩, ⟨49805405382, 52657923656⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 239861760 240517120 163430400 164823040 ⟨⟨51653743990, 51653743996⟩, ⟨50230029500, 53086027850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 240517120 241172480 162037760 163430400 ⟨⟨50992636957, 50992636959⟩, ⟨49573572489, 52420236856⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 240517120 241172480 163430400 164823040 ⟨⟨51417147420, 51417147423⟩, ⟨49996350386, 52846485604⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 238551040 241172480 159252480 164823040 t = true :=
  ⟨_, (join_su (m := 239861760) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 239206400) (by decide) (join_sr (m := 160645120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 160645120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 239206400) (by decide) (join_sr (m := 163430400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 163430400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 162037760) (by decide) (join_su (m := 240517120) (by decide) (join_sr (m := 160645120) (by decide) (join_su (m := 240189440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 160645120) (by decide) (join_su (m := 240844800) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))) (join_su (m := 240517120) (by decide) (join_sr (m := 163430400) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_sr (m := 163430400) (by decide) (leaf_ok cell16) (leaf_ok cell17)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (91/320 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (503/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
