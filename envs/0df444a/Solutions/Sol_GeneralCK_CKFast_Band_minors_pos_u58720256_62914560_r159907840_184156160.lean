-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u58720256_62914560_r159907840_184156160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:14:22.943404+00:00
-- url     : https://prove2.me/submissions/6780a79c-1bd7-44e2-95a0-97912da8327b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/100, 3/40]`, `ρ ∈ [61/320, 281/1280]` by 13 cells of the computing
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
theorem cell0 : cellOK 58720256 59768832 159907840 165969920 ⟨⟨181931367835, 181931367850⟩, ⟨172804781884, 191303209430⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 59768832 60817408 159907840 165969920 ⟨⟨180177799928, 180177799943⟩, ⟨171155031100, 189441396944⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 58720256 59768832 165969920 172032000 ⟨⟨187047673517, 187047673531⟩, ⟨177925654353, 196409716882⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 59768832 60817408 165969920 172032000 ⟨⟨185268444874, 185268444888⟩, ⟨176248939647, 194523732648⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 60817408 61865984 159907840 165969920 ⟨⟨178454794264, 178454794276⟩, ⟨169533528223, 187612582975⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 61865984 62914560 159907840 165969920 ⟨⟨176761461685, 176761461700⟩, ⟨167939461392, 185815796596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 60817408 61865984 165969920 172032000 ⟨⟨183519715768, 183519715782⟩, ⟨174600473115, 192670613514⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 61865984 62914560 165969920 172032000 ⟨⟨181800610768, 181800610780⟩, ⟨172979453459, 190849405827⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 58720256 60817408 172032000 178094080 ⟨⟨191182834488, 191182834502⟩, ⟨177870580929, 205012947596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 58720256 60817408 178094080 184156160 ⟨⟨196139363475, 196139363487⟩, ⟨182824785134, 209961797576⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 60817408 61865984 172032000 178094080 ⟨⟨188511754156, 188511754171⟩, ⟨179595589347, 197654824071⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 61865984 62914560 172032000 178094080 ⟨⟨186768153396, 186768153407⟩, ⟨177948891870, 195810466659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 60817408 62914560 178094080 184156160 ⟨⟨192546442801, 192546442813⟩, ⟨179508127813, 206076336585⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 58720256 62914560 159907840 184156160 t = true :=
  ⟨_, (join_sr (m := 172032000) (by decide) (join_su (m := 60817408) (by decide) (join_sr (m := 165969920) (by decide) (join_su (m := 59768832) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 59768832) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 165969920) (by decide) (join_su (m := 61865984) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 61865984) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 60817408) (by decide) (join_sr (m := 178094080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 178094080) (by decide) (join_su (m := 61865984) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/100 : ℝ) (3/40 : ℝ) →
    rho ∈ Set.Icc (61/320 : ℝ) (281/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e1 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e2 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e3 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
