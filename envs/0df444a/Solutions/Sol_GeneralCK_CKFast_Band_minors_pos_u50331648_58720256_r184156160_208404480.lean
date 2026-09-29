-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_58720256_r184156160_208404480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:14:34.852222+00:00
-- url     : https://prove2.me/submissions/c326f75b-3115-4e9b-9580-0c79eed2a6f2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 7/100]`, `ρ ∈ [281/1280, 159/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 50331648 52428800 184156160 190218240 ⟨⟨216874693244, 216874693257⟩, ⟨202337365695, 231981341475⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 50331648 52428800 190218240 196280320 ⟨⟨221855040673, 221855040686⟩, ⟨207334718446, 236931999473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 52428800 54525952 184156160 190218240 ⟨⟨212701857991, 212701858003⟩, ⟨198491307951, 227462476330⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 52428800 54525952 190218240 196280320 ⟨⟨217643490893, 217643490908⟩, ⟨203445184400, 232380063290⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 50331648 52428800 196280320 202342400 ⟨⟨226761910933, 226761910949⟩, ⟨212259652908, 241808465721⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 50331648 52428800 202342400 208404480 ⟨⟨231598069792, 231598069805⟩, ⟨217114828658, 246613600141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 52428800 54525952 196280320 202342400 ⟨⟨222513920950, 222513920963⟩, ⟨208328969000, 237225642148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 52428800 54525952 202342400 208404480 ⟨⟨227315771421, 227315771433⟩, ⟨213145182202, 242001928881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 54525952 56623104 184156160 190218240 ⟨⟨208675091004, 208675091016⟩, ⟨194776449200, 223105554377⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 54525952 56623104 190218240 196280320 ⟨⟨213576978596, 213576978611⟩, ⟨199686247509, 227988539606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 56623104 58720256 184156160 190218240 ⟨⟨204785873340, 204785873352⟩, ⟨191185275992, 218900983187⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 56623104 58720256 190218240 196280320 ⟨⟨209647150998, 209647151010⟩, ⟨196050519237, 223748050148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 54525952 56623104 196280320 202342400 ⟨⟨218409884290, 218409884304⟩, ⟨204528213868, 232801664597⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 54525952 56623104 202342400 208404480 ⟨⟨223176296238, 223176296254⟩, ⟨209304737252, 237547508221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 56623104 58720256 196280320 202342400 ⟨⟨214441612308, 214441612320⟩, ⟨200850123833, 228527364406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 56623104 58720256 202342400 208404480 ⟨⟨219171617408, 219171617422⟩, ⟨205586354536, 233241374408⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 58720256 184156160 208404480 t = true :=
  ⟨_, (join_su (m := 54525952) (by decide) (join_sr (m := 196280320) (by decide) (join_su (m := 52428800) (by decide) (join_sr (m := 190218240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 190218240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 52428800) (by decide) (join_sr (m := 202342400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 202342400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 196280320) (by decide) (join_su (m := 56623104) (by decide) (join_sr (m := 190218240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 190218240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 56623104) (by decide) (join_sr (m := 202342400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 202342400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (7/100 : ℝ) →
    rho ∈ Set.Icc (281/1280 : ℝ) (159/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e2 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  have e3 : (((208404480 : ℤ) : ℝ) / (D : ℝ)) = (159/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
