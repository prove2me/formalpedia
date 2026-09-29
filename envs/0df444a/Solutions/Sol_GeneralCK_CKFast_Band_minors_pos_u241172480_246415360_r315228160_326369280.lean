-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_246415360_r315228160_326369280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:43:49.750161+00:00
-- url     : https://prove2.me/submissions/a718876d-dbe2-4da1-9f78-5f50c6fae981

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 47/160]`, `ρ ∈ [481/1280, 249/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 242483200 315228160 318013440 ⟨⟨96242967121, 96242967127⟩, ⟨93044976520, 99477233771⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241172480 242483200 318013440 320798720 ⟨⟨97051292297, 97051292303⟩, ⟨93846540029, 100292357636⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 242483200 243793920 315228160 318013440 ⟨⟨95395777474, 95395777480⟩, ⟨92210937563, 98616701656⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 242483200 243793920 318013440 320798720 ⟨⟨96197619212, 96197619218⟩, ⟨93006043300, 99425317083⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241172480 242483200 320798720 323584000 ⟨⟨97859066439, 97859066445⟩, ⟨94647554445, 101106928352⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 241172480 242483200 323584000 326369280 ⟨⟨98666292270, 98666292276⟩, ⟨95448022482, 101920948654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 242483200 243793920 320798720 323584000 ⟨⟨96998923242, 96998923249⟩, ⟨93800613097, 100233392868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 242483200 243793920 323584000 326369280 ⟨⟨97799692210, 97799692215⟩, ⟨94594649583, 101040931670⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 245104640 315228160 318013440 ⟨⟨94552111749, 94552111754⟩, ⟨91380316178, 97759801761⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 243793920 245104640 318013440 320798720 ⟨⟨95347481401, 95347481407⟩, ⟨92168975658, 98561919926⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245104640 246415360 315228160 318013440 ⟨⟨93711923160, 93711923161⟩, ⟨90553066919, 96906485936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245104640 246415360 318013440 320798720 ⟨⟨94500832011, 94500832015⟩, ⟨91335291582, 97702117953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243793920 245104640 320798720 323584000 ⟨⟨96142326428, 96142326435⟩, ⟨92957112107, 99363511710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 243793920 245104640 323584000 326369280 ⟨⟨96936649397, 96936649405⟩, ⟨93744728077, 100164579692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245104640 246415360 320798720 323584000 ⟨⟨95289229080, 95289229083⟩, ⟨92117005883, 98497236605⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245104640 246415360 323584000 326369280 ⟨⟨96077116856, 96077116860⟩, ⟨92898212305, 99291844393⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 246415360 315228160 326369280 t = true :=
  ⟨_, (join_su (m := 243793920) (by decide) (join_sr (m := 320798720) (by decide) (join_su (m := 242483200) (by decide) (join_sr (m := 318013440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 318013440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 242483200) (by decide) (join_sr (m := 323584000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 323584000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 320798720) (by decide) (join_su (m := 245104640) (by decide) (join_sr (m := 318013440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 318013440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 245104640) (by decide) (join_sr (m := 323584000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 323584000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (481/1280 : ℝ) (249/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((315228160 : ℤ) : ℝ) / (D : ℝ)) = (481/1280 : ℝ) := by norm_num [D]
  have e3 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
