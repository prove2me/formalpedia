-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u58720256_67108864_r208404480_232652800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:15:46.184186+00:00
-- url     : https://prove2.me/submissions/2838655d-c340-41e6-8827-4e8f0254603e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/100, 2/25]`, `ρ ∈ [159/640, 71/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 58720256 60817408 208404480 214466560 ⟨⟨219926773189, 219926773203⟩, ⟨206619573711, 233695087422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 58720256 60817408 214466560 220528640 ⟨⟨224500917689, 224500917704⟩, ⟨211198350720, 238255865545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 60817408 62914560 208404480 214466560 ⟨⟨216133943457, 216133943472⟩, ⟨203086698457, 229629089250⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 60817408 62914560 214466560 220528640 ⟨⟨220673715713, 220673715725⟩, ⟨207627889654, 234159254493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 58720256 60817408 220528640 226590720 ⟨⟨229018713127, 229018713141⟩, ⟨215721646730, 242759618041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 58720256 60817408 226590720 232652800 ⟨⟨233482019417, 233482019432⟩, ⟨220191253933, 247208267102⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 60817408 62914560 220528640 226590720 ⟨⟨225158773553, 225158773567⟩, ⟨212115257639, 238633985502⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 60817408 62914560 226590720 232652800 ⟨⟨229590888662, 229590888677⟩, ⟨216550508634, 243055114812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 62914560 65011712 208404480 214466560 ⟨⟨212454704751, 212454704765⟩, ⟨199657178746, 225687504825⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 62914560 65011712 214466560 220528640 ⟨⟨216959432074, 216959432086⟩, ⟨204160373173, 230186084367⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 65011712 67108864 208404480 214466560 ⟨⟨208883282295, 208883282309⟩, ⟨196325840953, 221863924598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 65011712 67108864 214466560 220528640 ⟨⟨213352390742, 213352390756⟩, ⟨200790704238, 226330069698⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 62914560 65011712 220528640 226590720 ⟨⟨221411043307, 221411043319⟩, ⟨208611359137, 234630793535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 62914560 65011712 226590720 232652800 ⟨⟨225811226082, 225811226096⟩, ⟨213011761160, 239023379186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 65011712 67108864 220528640 226590720 ⟨⟨217769944218, 217769944232⟩, ⟨205204930810, 230743878720⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 65011712 67108864 226590720 232652800 ⟨⟨222137550326, 222137550340⟩, ⟨209570067557, 235107016716⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 58720256 67108864 208404480 232652800 t = true :=
  ⟨_, (join_su (m := 62914560) (by decide) (join_sr (m := 220528640) (by decide) (join_su (m := 60817408) (by decide) (join_sr (m := 214466560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 214466560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 60817408) (by decide) (join_sr (m := 226590720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 226590720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 220528640) (by decide) (join_su (m := 65011712) (by decide) (join_sr (m := 214466560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 214466560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 65011712) (by decide) (join_sr (m := 226590720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 226590720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/100 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (159/640 : ℝ) (71/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((208404480 : ℤ) : ℝ) / (D : ℝ)) = (159/640 : ℝ) := by norm_num [D]
  have e3 : (((232652800 : ℤ) : ℝ) / (D : ℝ)) = (71/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
