-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u239861760_241172480_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:46:01.704889+00:00
-- url     : https://prove2.me/submissions/99f31449-0876-49dd-9805-efe75ec0c5be

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [183/640, 23/80]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 239861760 240189440 142540800 143933440 ⟨⟨45290808818, 45290808820⟩, ⟨44469720786, 46114931382⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 240189440 240517120 142540800 143933440 ⟨⟨45186374290, 45186374296⟩, ⟨44366306752, 46009470261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 239861760 240189440 143933440 145326080 ⟨⟨45720288868, 45720288871⟩, ⟨44898255220, 46545358418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 240189440 240517120 143933440 145326080 ⟨⟨45614910883, 45614910889⟩, ⟨44793899196, 46438952378⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 240517120 240844800 142540800 143933440 ⟨⟨45082084325, 45082084330⟩, ⟨44263034995, 45904156004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 240844800 241172480 142540800 143933440 ⟨⟨44977938375, 44977938382⟩, ⟨44159904973, 45798988064⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 240517120 240844800 143933440 145326080 ⟨⟨45509678467, 45509678473⟩, ⟨44689686452, 46332694213⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 240844800 241172480 143933440 145326080 ⟨⟨45404591070, 45404591076⟩, ⟨44585616446, 46226583368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 239861760 240189440 145326080 146718720 ⟨⟨46149576341, 46149576343⟩, ⟨45326597414, 46975592535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 240189440 240517120 145326080 146718720 ⟨⟨46043256145, 46043256150⟩, ⟨45221300640, 46868242830⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 239861760 240189440 146718720 148111360 ⟨⟨46578671685, 46578671688⟩, ⟨45754747817, 47405634186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 240189440 240517120 146718720 148111360 ⟨⟨46471410521, 46471410526⟩, ⟨45648511531, 47297342061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 240517120 240844800 145326080 146718720 ⟨⟨45937082517, 45937082522⟩, ⟨45116148145, 46761041998⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 240844800 241172480 145326080 146718720 ⟨⟨45831054905, 45831054910⟩, ⟨45011139381, 46653989486⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 240517120 240844800 146718720 148111360 ⟨⟨46364296918, 46364296923⟩, ⟨45542420513, 47189199805⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 240844800 241172480 146718720 148111360 ⟨⟨46257330321, 46257330326⟩, ⟨45436474217, 47081206861⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 239861760 241172480 142540800 148111360 t = true :=
  ⟨_, (join_sr (m := 145326080) (by decide) (join_su (m := 240517120) (by decide) (join_sr (m := 143933440) (by decide) (join_su (m := 240189440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 240189440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 143933440) (by decide) (join_su (m := 240844800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 240844800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 240517120) (by decide) (join_sr (m := 146718720) (by decide) (join_su (m := 240189440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 240189440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 146718720) (by decide) (join_su (m := 240844800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 240844800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (183/640 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((239861760 : ℤ) : ℝ) / (D : ℝ)) = (183/640 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
