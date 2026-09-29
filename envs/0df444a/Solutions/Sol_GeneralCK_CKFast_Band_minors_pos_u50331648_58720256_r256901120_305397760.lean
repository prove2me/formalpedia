-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_58720256_r256901120_305397760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:16:35.569532+00:00
-- url     : https://prove2.me/submissions/49ed5465-37fc-4e33-8502-08f6d7238896

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 7/100]`, `ρ ∈ [49/160, 233/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 50331648 52428800 256901120 269025280 ⟨⟨274468415147, 274468415161⟩, ⟨255389073682, 294311579168⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 52428800 54525952 256901120 269025280 ⟨⟨269944594062, 269944594074⟩, ⟨251239735968, 289393741136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 50331648 52428800 269025280 281149440 ⟨⟨282881868401, 282881868417⟩, ⟨263889803226, 302603651773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 52428800 54525952 269025280 281149440 ⟨⟨278322309621, 278322309637⟩, ⟨259693673415, 297662999941⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 54525952 56623104 256901120 269025280 ⟨⟨265551591393, 265551591405⟩, ⟨247207306133, 284621333450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 56623104 58720256 256901120 269025280 ⟨⟨261282769793, 261282769806⟩, ⟨243285942309, 279986894995⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 54525952 56623104 269025280 281149440 ⟨⟨273890928590, 273890928603⟩, ⟨255612591347, 292864242430⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 56623104 58720256 269025280 281149440 ⟨⟨269581343471, 269581343483⟩, ⟨251640910574, 288200241888⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 50331648 52428800 281149440 293273600 ⟨⟨291113170772, 291113170788⟩, ⟨272209006986, 310714673469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 52428800 54525952 281149440 293273600 ⟨⟨286521853496, 286521853509⟩, ⟨267970437834, 305754661756⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 50331648 52428800 293273600 305397760 ⟨⟨299173754544, 299173754561⟩, ⟨280357763026, 318656310556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 52428800 54525952 293273600 305397760 ⟨⟨294554222261, 294554222276⟩, ⟨276080664207, 313679978866⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 54525952 56623104 281149440 293273600 ⟨⟨282056078647, 282056078662⟩, ⟨263845011884, 300933076959⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 56623104 58720256 281149440 293273600 ⟨⟨277709707131, 277709707146⟩, ⟨259827270825, 296243085941⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 54525952 56623104 293273600 305397760 ⟨⟨290057614849, 290057614864⟩, ⟨271914775413, 308838682681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 56623104 58720256 293273600 305397760 ⟨⟨285678023537, 285678023553⟩, ⟨267854819014, 304125874637⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 58720256 256901120 305397760 t = true :=
  ⟨_, (join_sr (m := 281149440) (by decide) (join_su (m := 54525952) (by decide) (join_sr (m := 269025280) (by decide) (join_su (m := 52428800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 52428800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 269025280) (by decide) (join_su (m := 56623104) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 56623104) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 54525952) (by decide) (join_sr (m := 293273600) (by decide) (join_su (m := 52428800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 52428800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 293273600) (by decide) (join_su (m := 56623104) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 56623104) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (7/100 : ℝ) →
    rho ∈ Set.Icc (49/160 : ℝ) (233/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e2 : (((256901120 : ℤ) : ℝ) / (D : ℝ)) = (49/160 : ℝ) := by norm_num [D]
  have e3 : (((305397760 : ℤ) : ℝ) / (D : ℝ)) = (233/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
