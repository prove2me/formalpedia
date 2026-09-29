-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u237240320_238551040_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:34:50.962989+00:00
-- url     : https://prove2.me/submissions/87c8cb05-969c-454e-8593-8ba25c19716c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [181/640, 91/320]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 237240320 237568000 125829120 127221760 ⟨⟨40870789612, 40870789619⟩, ⟨40052972983, 41691674184⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 237568000 237895680 125829120 127221760 ⟨⟨40776701050, 40776701056⟩, ⟨39959905350, 41596558355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 237240320 237568000 127221760 128614400 ⟨⟨41310325261, 41310325266⟩, ⟨40491546606, 42132173221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 237568000 237895680 127221760 128614400 ⟨⟨41215269165, 41215269170⟩, ⟨40397512984, 42036088319⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 237895680 238223360 125829120 127221760 ⟨⟨40682748555, 40682748560⟩, ⟨39866971450, 41501580949⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 238223360 238551040 125829120 127221760 ⟨⟨40588931607, 40588931610⟩, ⟨39774170772, 41406741432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 237895680 238223360 127221760 128614400 ⟨⟨41120350252, 41120350257⟩, ⟨40303614209, 41940142960⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 238223360 238551040 127221760 128614400 ⟨⟨41025568000, 41025568003⟩, ⟨40209849769, 41844336604⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 237240320 237568000 128614400 130007040 ⟨⟨41749652273, 41749652278⟩, ⟨40929911984, 42572463228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 237568000 237895680 128614400 130007040 ⟨⟨41653629989, 41653629996⟩, ⟨40834913715, 42475410607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 237240320 237568000 130007040 131399680 ⟨⟨42188771141, 42188771146⟩, ⟨41368069608, 43012544700⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 237568000 237895680 130007040 131399680 ⟨⟨42091784016, 42091784021⟩, ⟨41272108029, 42914525707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 237895680 238223360 128614400 130007040 ⟨⟨41557746001, 41557746006⟩, ⟨40740051400, 42378498640⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 238223360 238551040 128614400 130007040 ⟨⟨41461999778, 41461999781⟩, ⟨40645324524, 42281726785⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 237895680 238223360 130007040 131399680 ⟨⟨41994936286, 41994936292⟩, ⟨41176283507, 42816648474⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 238223360 238551040 130007040 131399680 ⟨⟨41898227423, 41898227426⟩, ⟨41080595519, 42718912455⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 237240320 238551040 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 237895680) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 237568000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 237568000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 238223360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 238223360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 237895680) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 237568000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 237568000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 238223360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 238223360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (181/640 : ℝ) (91/320 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e1 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
