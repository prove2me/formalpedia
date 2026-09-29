-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u20971520_25165824_r87162880_99287040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:18:44.756977+00:00
-- url     : https://prove2.me/submissions/fc959926-2d5e-45f2-bad7-07c77ca4f38b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/40, 3/100]`, `ρ ∈ [133/1280, 303/2560]` by 14 cells of the computing
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
theorem cell0 : cellOK 20971520 22020096 87162880 90193920 ⟨⟨192852338582, 192852338602⟩, ⟨180005550475, 206240658760⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 20971520 22020096 90193920 93224960 ⟨⟨197071934835, 197071934860⟩, ⟨184286266392, 210384641357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 22020096 23068672 87162880 90193920 ⟨⟨188958802281, 188958802307⟩, ⟨176450139272, 201985724251⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 22020096 23068672 90193920 93224960 ⟨⟨193155737468, 193155737488⟩, ⟨180701957885, 206114355407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 20971520 22020096 93224960 99287040 ⟨⟨203245945900, 203245945920⟩, ⟨185809130938, 221634976847⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 22020096 23068672 93224960 99287040 ⟨⟨199299882197, 199299882217⟩, ⟨182307030033, 217205596297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 23068672 24117248 87162880 90193920 ⟨⟨185230941048, 185230941068⟩, ⟨173042242691, 197916148255⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 23068672 24117248 90193920 93224960 ⟨⟨189403601995, 189403602020⟩, ⟨177264130024, 202027135790⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 24117248 25165824 87162880 90193920 ⟨⟨181657573388, 181657573407⟩, ⟨169772117985, 194019180311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 24117248 25165824 90193920 93224960 ⟨⟨185804598801, 185804598820⟩, ⟨173963229476, 198110557563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 23068672 24117248 93224960 96256000 ⟨⟨193497217007, 193497217031⟩, ⟨181407360989, 206059117278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 23068672 24117248 96256000 99287040 ⟨⟨197514999446, 197514999471⟩, ⟨185475054174, 210015382191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 24117248 25165824 93224960 96256000 ⟨⟨189874727295, 189874727314⟩, ⟨178077930141, 202124936785⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 24117248 25165824 96256000 99287040 ⟨⟨193871018653, 193871018672⟩, ⟨182119186171, 206065455297⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 20971520 25165824 87162880 99287040 t = true :=
  ⟨_, (join_su (m := 23068672) (by decide) (join_sr (m := 93224960) (by decide) (join_su (m := 22020096) (by decide) (join_sr (m := 90193920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 90193920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 22020096) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 93224960) (by decide) (join_su (m := 24117248) (by decide) (join_sr (m := 90193920) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 90193920) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 24117248) (by decide) (join_sr (m := 96256000) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 96256000) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/40 : ℝ) (3/100 : ℝ) →
    rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((20971520 : ℤ) : ℝ) / (D : ℝ)) = (1/40 : ℝ) := by norm_num [D]
  have e1 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e2 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  have e3 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
