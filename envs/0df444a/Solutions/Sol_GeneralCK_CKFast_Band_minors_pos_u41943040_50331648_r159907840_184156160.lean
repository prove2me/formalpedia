-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u41943040_50331648_r159907840_184156160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:49:29.554752+00:00
-- url     : https://prove2.me/submissions/bc1b31af-5240-4df6-88ed-2879eed98b0f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/20, 3/50]`, `ρ ∈ [61/320, 281/1280]` by 17 cells of the computing
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
theorem cell0 : cellOK 41943040 44040192 159907840 165969920 ⟨⟨213837015376, 213837015394⟩, ⟨197663839766, 230742598809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 41943040 44040192 165969920 172032000 ⟨⟨219328332759, 219328332776⟩, ⟨203192434625, 236177058270⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 44040192 46137344 159907840 165969920 ⟨⟨209136121880, 209136121897⟩, ⟨193390834581, 225584006267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 44040192 46137344 165969920 172032000 ⟨⟨214583159207, 214583159221⟩, ⟨198867639986, 230983245369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 41943040 44040192 172032000 178094080 ⟨⟨224720740664, 224720740681⟩, ⟨208623388474, 241512005031⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 41943040 44040192 178094080 184156160 ⟨⟨230018576508, 230018576526⟩, ⟨213960863026, 246751923215⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 44040192 46137344 172032000 178094080 ⟨⟨219934603495, 219934603512⟩, ⟨204250240155, 236286087200⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 44040192 46137344 178094080 184156160 ⟨⟨225194545548, 225194545565⟩, ⟨209542555154, 241496769274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 46137344 48234496 159907840 165969920 ⟨⟨204631330072, 204631330089⟩, ⟨189290973321, 220646336346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 46137344 48234496 165969920 172032000 ⟨⟨210032370548, 210032370565⟩, ⟨194715036537, 226007728730⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 48234496 49283072 159907840 165969920 ⟨⟨201373323822, 201373323835⟩, ⟨191061376218, 211982662450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 49283072 50331648 159907840 165969920 ⟨⟨199255829456, 199255829469⟩, ⟨189076011629, 209727091652⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 48234496 50331648 165969920 172032000 ⟨⟨205662881608, 205662881624⟩, ⟨190723276883, 221235550674⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 46137344 48234496 172032000 178094080 ⟨⟨215341053070, 215341053087⟩, ⟨200048220380, 231275797075⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 46137344 48234496 178094080 184156160 ⟨⟨220561235998, 220561236014⟩, ⟨205294218232, 236454544819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 48234496 50331648 172032000 178094080 ⟨⟨210927304858, 210927304874⟩, ⟨196006202190, 226466572524⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 48234496 50331648 178094080 184156160 ⟨⟨216106158160, 216106158176⟩, ⟨201204944426, 231611071611⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 41943040 50331648 159907840 184156160 t = true :=
  ⟨_, (join_su (m := 46137344) (by decide) (join_sr (m := 172032000) (by decide) (join_su (m := 44040192) (by decide) (join_sr (m := 165969920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 165969920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 44040192) (by decide) (join_sr (m := 178094080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 178094080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 172032000) (by decide) (join_su (m := 48234496) (by decide) (join_sr (m := 165969920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 165969920) (by decide) (join_su (m := 49283072) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))) (join_su (m := 48234496) (by decide) (join_sr (m := 178094080) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_sr (m := 178094080) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/20 : ℝ) (3/50 : ℝ) →
    rho ∈ Set.Icc (61/320 : ℝ) (281/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e1 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e2 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e3 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
