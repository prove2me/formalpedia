-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u239861760_241172480_r153681920_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:13:08.477242+00:00
-- url     : https://prove2.me/submissions/de392b5a-9822-4b00-9f59-e96d849f443a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [183/640, 23/80]`, `ρ ∈ [469/2560, 243/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 239861760 240189440 153681920 155074560 ⟨⟨48721282188, 48721282191⟩, ⟨47892638620, 49552971156⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 240189440 240517120 153681920 155074560 ⟨⟨48609334692, 48609334698⟩, ⟨47781723206, 49439985523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 239861760 240189440 155074560 156467200 ⟨⟨49149234171, 49149234173⟩, ⟨48319647657, 49981867426⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 240189440 240517120 155074560 156467200 ⟨⟨49036353084, 49036353091⟩, ⟨48207800080, 49867946782⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 240517120 240844800 153681920 155074560 ⟨⟨48497539624, 48497539630⟩, ⟨47670957922, 49327154634⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 240844800 241172480 153681920 155074560 ⟨⟨48385896413, 48385896420⟩, ⟨47560342202, 49214477915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 240517120 240844800 155074560 156467200 ⟨⟨48923625381, 48923625387⟩, ⟨48096103586, 49754181839⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 240844800 241172480 155074560 156467200 ⟨⟨48811050486, 48811050493⟩, ⟨47984557605, 49640572018⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 239861760 240189440 156467200 157859840 ⟨⟨49576997151, 49576997154⟩, ⟨48746468023, 50410574360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 240189440 240517120 156467200 157859840 ⟨⟨49463183692, 49463183698⟩, ⟨48633689495, 50295719929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 239861760 240189440 157859840 159252480 ⟨⟨50004571572, 50004571575⟩, ⟨49173100159, 50839092404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 240189440 240517120 157859840 159252480 ⟨⟨49889826956, 49889826961⟩, ⟨49059391889, 50723305403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 240517120 240844800 156467200 157859840 ⟨⟨49349524564, 49349524571⟩, ⟨48521062996, 50181022147⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 240844800 241172480 156467200 157859840 ⟨⟨49236019190, 49236019195⟩, ⟨48408587954, 50066480434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 240517120 240844800 157859840 159252480 ⟨⟨49775237610, 49775237615⟩, ⟨48945836587, 50607675996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 240844800 241172480 157859840 159252480 ⟨⟨49660802956, 49660802962⟩, ⟨48832433680, 50492203595⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 239861760 241172480 153681920 159252480 t = true :=
  ⟨_, (join_sr (m := 156467200) (by decide) (join_su (m := 240517120) (by decide) (join_sr (m := 155074560) (by decide) (join_su (m := 240189440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 240189440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 155074560) (by decide) (join_su (m := 240844800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 240844800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 240517120) (by decide) (join_sr (m := 157859840) (by decide) (join_su (m := 240189440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 240189440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 157859840) (by decide) (join_su (m := 240844800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 240844800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (183/640 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (469/2560 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((239861760 : ℤ) : ℝ) / (D : ℝ)) = (183/640 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
