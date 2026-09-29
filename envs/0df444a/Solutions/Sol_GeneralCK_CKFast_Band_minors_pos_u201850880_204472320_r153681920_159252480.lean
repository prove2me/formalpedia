-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u201850880_204472320_r153681920_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:52:38.816981+00:00
-- url     : https://prove2.me/submissions/17eb20bc-d55c-4961-9013-f40f55c0513c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [77/320, 39/160]`, `ρ ∈ [469/2560, 243/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 201850880 202506240 153681920 155074560 ⟨⟨62847926548, 62847926553⟩, ⟨61241346130, 64465065427⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 201850880 202506240 155074560 156467200 ⟨⟨63390983194, 63390983201⟩, ⟨61782375980, 65010152039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 202506240 203161600 153681920 155074560 ⟨⟨62579916442, 62579916448⟩, ⟨60977235973, 64193112773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 202506240 203161600 155074560 156467200 ⟨⟨63120841873, 63120841880⟩, ⟨61516139748, 64736063097⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 201850880 202506240 156467200 157859840 ⟨⟨63933657890, 63933657897⟩, ⟨62323025606, 65554854951⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 201850880 202506240 157859840 159252480 ⟨⟨64475951730, 64475951737⟩, ⟨62863296099, 66099175263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 202506240 203161600 156467200 157859840 ⟨⟨63661389757, 63661389763⟩, ⟨62054667670, 65278634158⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 202506240 203161600 157859840 159252480 ⟨⟨64201561173, 64201561180⟩, ⟨62592820813, 65820827040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 203161600 203816960 153681920 155074560 ⟨⟨62312855693, 62312855700⟩, ⟨60714053345, 63922131621⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 203161600 203816960 155074560 156467200 ⟨⟨62851655346, 62851655353⟩, ⟨61250836476, 64462951097⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 203816960 204472320 153681920 155074560 ⟨⟨62046736681, 62046736688⟩, ⟨60451790810, 63652114164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 203816960 204472320 155074560 156467200 ⟨⟨62583415958, 62583415966⟩, ⟨60986458697, 64190808199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 203161600 203816960 156467200 157859840 ⟨⟨63390081810, 63390081817⟩, ⟨61787248083, 65003395701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 203161600 203816960 157859840 159252480 ⟨⟨63928136151, 63928136156⟩, ⟨62323289222, 65543466503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 203816960 204472320 156467200 157859840 ⟨⟨63119726363, 63119726369⟩, ⟨61520759343, 64729131710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 203816960 204472320 157859840 159252480 ⟨⟨63655668943, 63655668949⟩, ⟨62054693790, 65267085751⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 201850880 204472320 153681920 159252480 t = true :=
  ⟨_, (join_su (m := 203161600) (by decide) (join_sr (m := 156467200) (by decide) (join_su (m := 202506240) (by decide) (join_sr (m := 155074560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 155074560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 202506240) (by decide) (join_sr (m := 157859840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 157859840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 156467200) (by decide) (join_su (m := 203816960) (by decide) (join_sr (m := 155074560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 155074560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 203816960) (by decide) (join_sr (m := 157859840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 157859840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (77/320 : ℝ) (39/160 : ℝ) →
    rho ∈ Set.Icc (469/2560 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e1 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e2 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
