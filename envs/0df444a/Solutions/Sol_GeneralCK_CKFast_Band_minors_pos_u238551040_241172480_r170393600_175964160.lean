-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u238551040_241172480_r170393600_175964160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:42:53.413622+00:00
-- url     : https://prove2.me/submissions/35bbec72-a9f9-4255-a980-f4e8869719fd

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [91/320, 23/80]`, `ρ ∈ [13/64, 537/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 238551040 239206400 170393600 171786240 ⟨⟨54276373392, 54276373399⟩, ⟨52838055659, 55723345493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 238551040 239206400 171786240 173178880 ⟨⟨54705310600, 54705310606⟩, ⟨53265248849, 56154032292⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 239206400 239861760 170393600 171786240 ⟨⟨54029243166, 54029243172⟩, ⟨52593893986, 55473218271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 239206400 239861760 171786240 173178880 ⟨⟨54456336636, 54456336641⟩, ⟨53019247986, 55902056809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 238551040 239206400 173178880 174571520 ⟨⟨55134059901, 55134059907⟩, ⟨53692254536, 56584530766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 238551040 239206400 174571520 175964160 ⟨⟨55562621737, 55562621744⟩, ⟨54119073164, 57014841363⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 239206400 239861760 173178880 174571520 ⟨⟨54883244584, 54883244589⟩, ⟨53444416856, 56330709427⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 239206400 239861760 174571520 175964160 ⟨⟨55309967449, 55309967456⟩, ⟨53869401031, 56759176563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 239861760 240517120 170393600 171786240 ⟨⟨53782772858, 53782772864⟩, ⟨52350378086, 55223765294⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 239861760 240517120 171786240 173178880 ⟨⟨54208026131, 54208026138⟩, ⟨52773896433, 55650759123⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 240517120 241172480 170393600 171786240 ⟨⟨53536957604, 53536957607⟩, ⟨52107503193, 54974981596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 240517120 241172480 171786240 173178880 ⟨⟨53960374203, 53960374206⟩, ⟨52529189402, 55400134241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 239861760 240517120 173178880 174571520 ⟨⟨54633096247, 54633096252⟩, ⟨53197231997, 56077569408⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 239861760 240517120 174571520 175964160 ⟨⟨55057983634, 55057983639⟩, ⟨53620385206, 56504196582⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 240517120 241172480 173178880 174571520 ⟨⟨54383609982, 54383609984⟩, ⟨52950695151, 55825105697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 240517120 241172480 174571520 175964160 ⟨⟨54806665364, 54806665367⟩, ⟨53372020862, 56249896387⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 238551040 241172480 170393600 175964160 t = true :=
  ⟨_, (join_su (m := 239861760) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 239206400) (by decide) (join_sr (m := 171786240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 171786240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 239206400) (by decide) (join_sr (m := 174571520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 174571520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 173178880) (by decide) (join_su (m := 240517120) (by decide) (join_sr (m := 171786240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 171786240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 240517120) (by decide) (join_sr (m := 174571520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 174571520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (91/320 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (537/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((175964160 : ℤ) : ℝ) / (D : ℝ)) = (537/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
