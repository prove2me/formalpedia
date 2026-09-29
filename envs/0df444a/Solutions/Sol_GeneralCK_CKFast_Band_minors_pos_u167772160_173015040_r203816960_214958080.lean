-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_173015040_r203816960_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:37:54.021823+00:00
-- url     : https://prove2.me/submissions/5cc3ddb4-5974-4afa-8dc2-ef7935c7bc87

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 33/160]`, `ρ ∈ [311/1280, 41/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 169082880 203816960 206602240 ⟨⟨101849601624, 101849601631⟩, ⟨98016097295, 105735777261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 167772160 169082880 206602240 209387520 ⟨⟨103124272032, 103124272040⟩, ⟨99282153846, 107019033274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 169082880 170393600 203816960 206602240 ⟨⟨101021994232, 101021994239⟩, ⟨97210225877, 104885966463⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 169082880 170393600 206602240 209387520 ⟨⟨102287842479, 102287842487⟩, ⟨98467484784, 106160378390⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 167772160 169082880 209387520 212172800 ⟨⟨104396550588, 104396550596⟩, ⟨100545846134, 108299869368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 167772160 169082880 212172800 214958080 ⟨⟨105666453853, 105666453859⟩, ⟨101807190483, 109578302342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 169082880 170393600 209387520 212172800 ⟨⟨103551348448, 103551348457⟩, ⟨99722428240, 107432420742⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 169082880 170393600 212172800 214958080 ⟨⟨104812528234, 104812528241⟩, ⟨100975072112, 108702109837⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 170393600 171704320 203816960 206602240 ⟨⟨100201121809, 100201121816⟩, ⟨96410820990, 104043166437⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 170393600 171704320 206602240 209387520 ⟨⟨101458187271, 101458187277⟩, ⟨97659322179, 105308773029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 171704320 173015040 203816960 206602240 ⟨⟨99386870997, 99386871003⟩, ⟨95617774253, 103207258697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 171704320 173015040 206602240 209387520 ⟨⟨100635192742, 100635192750⟩, ⟨96857557317, 104464098424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 170393600 171704320 209387520 212172800 ⟨⟨102712959102, 102712959109⟩, ⟨98905555817, 106572059443⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 170393600 171704320 212172800 214958080 ⟨⟨103965452937, 103965452945⟩, ⟨100149537320, 107833041535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 171704320 173015040 209387520 212172800 ⟨⟨101881268594, 101881268602⟩, ⟨98095119832, 105718666448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 171704320 173015040 212172800 214958080 ⟨⟨103125113740, 103125113748⟩, ⟨99330476781, 106970978167⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 173015040 203816960 214958080 t = true :=
  ⟨_, (join_su (m := 170393600) (by decide) (join_sr (m := 209387520) (by decide) (join_su (m := 169082880) (by decide) (join_sr (m := 206602240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 206602240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 169082880) (by decide) (join_sr (m := 212172800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 212172800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 209387520) (by decide) (join_su (m := 171704320) (by decide) (join_sr (m := 206602240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 206602240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 171704320) (by decide) (join_sr (m := 212172800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 212172800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (33/160 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
