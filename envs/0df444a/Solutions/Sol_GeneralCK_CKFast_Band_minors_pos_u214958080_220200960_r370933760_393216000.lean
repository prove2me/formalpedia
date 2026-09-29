-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_220200960_r370933760_393216000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:16:58.032988+00:00
-- url     : https://prove2.me/submissions/0edf7e5b-d150-4311-9a2e-7ae46bd7ad2c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 21/80]`, `ρ ∈ [283/640, 15/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 214958080 216268800 370933760 376504320 ⟨⟨133115544419, 133115544426⟩, ⟨128857314074, 137431505006⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 216268800 217579520 370933760 376504320 ⟨⟨132052802645, 132052802651⟩, ⟨127816563749, 136346405917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 214958080 216268800 376504320 382074880 ⟨⟨134961709733, 134961709740⟩, ⟨130688260210, 139292883366⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 216268800 217579520 376504320 382074880 ⟨⟨133886268934, 133886268941⟩, ⟨129634847682, 138195052172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 217579520 218890240 370933760 376504320 ⟨⟨130994866101, 130994866109⟩, ⟨126780445163, 135266288936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 218890240 220200960 370933760 376504320 ⟨⟨129941672594, 129941672597⟩, ⟨125748898325, 134191089619⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 217579520 218890240 376504320 382074880 ⟨⟨132815645833, 132815645841⟩, ⟨128586080370, 137102214453⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 218890240 220200960 376504320 382074880 ⟨⟨131749778327, 131749778329⟩, ⟨127541898349, 136014305885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 216268800 382074880 387645440 ⟨⟨136804770528, 136804770534⟩, ⟨132516132759, 141151124992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 216268800 217579520 382074880 387645440 ⟨⟨135716696323, 135716696329⟩, ⟨131450122510, 140040628462⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 214958080 216268800 387645440 393216000 ⟨⟨138644761661, 138644761669⟩, ⟨134340966173, 143006265148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 216268800 217579520 387645440 393216000 ⟨⟨137544118768, 137544118775⟩, ⟨133262421802, 141883169136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 217579520 218890240 382074880 387645440 ⟨⟨134633451234, 134633451242⟩, ⟨130388769928, 138935135708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 218890240 220200960 382074880 387645440 ⟨⟨133554973262, 133554973265⟩, ⟨129332015158, 137834582539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 217579520 218890240 387645440 393216000 ⟨⟨136448315381, 136448315389⟩, ⟨132188546537, 140765086156⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 218890240 220200960 387645440 393216000 ⟨⟨135357289615, 135357289619⟩, ⟨131119280610, 139651952161⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 220200960 370933760 393216000 t = true :=
  ⟨_, (join_sr (m := 382074880) (by decide) (join_su (m := 217579520) (by decide) (join_sr (m := 376504320) (by decide) (join_su (m := 216268800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 216268800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 376504320) (by decide) (join_su (m := 218890240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 218890240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 217579520) (by decide) (join_sr (m := 387645440) (by decide) (join_su (m := 216268800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 216268800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 387645440) (by decide) (join_su (m := 218890240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 218890240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (283/640 : ℝ) (15/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  have e3 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
