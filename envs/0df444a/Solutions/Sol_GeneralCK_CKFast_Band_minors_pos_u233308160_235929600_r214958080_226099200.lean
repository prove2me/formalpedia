-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u233308160_235929600_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:29:38.103342+00:00
-- url     : https://prove2.me/submissions/3fa9b5e0-d735-4358-a2fa-038758e4e49d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [89/320, 9/32]`, `ρ ∈ [41/160, 69/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 233308160 233963520 214958080 217743360 ⟨⟨70597986434, 70597986441⟩, ⟨68817099350, 72391745356⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 233963520 234618880 214958080 217743360 ⟨⟨70285815810, 70285815813⟩, ⟨68509464104, 72074990473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 233308160 233963520 217743360 220528640 ⟨⟨71472419740, 71472419746⟩, ⟨69687724063, 73269995603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 233963520 234618880 217743360 220528640 ⟨⟨71156666408, 71156666410⟩, ⟨69376515870, 72949648380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 234618880 235274240 214958080 217743360 ⟨⟨69974453262, 69974453267⟩, ⟨68202617080, 71759063820⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235274240 235929600 214958080 217743360 ⟨⟨69663892997, 69663893004⟩, ⟨67896552624, 71443959459⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 234618880 235274240 217743360 220528640 ⟨⟨70841726947, 70841726954⟩, ⟨69066101698, 72630135180⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 235274240 235929600 217743360 220528640 ⟨⟨70527595540, 70527595547⟩, ⟨68756475866, 72311450036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 233308160 233963520 220528640 223313920 ⟨⟨72346086708, 72346086715⟩, ⟨70557585481, 74147476410⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 233963520 234618880 220528640 223313920 ⟨⟨72026760028, 72026760031⟩, ⟨70242813623, 73823546286⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 233308160 233963520 223313920 226099200 ⟨⟨73218991099, 73218991105⟩, ⟨71426687344, 75024191553⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 233963520 234618880 223313920 226099200 ⟨⟨72896100373, 72896100376⟩, ⟨71108361046, 74696687910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 234618880 235274240 220528640 223313920 ⟨⟨71708252926, 71708252932⟩, ⟨69928841494, 73500455887⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 235274240 235929600 220528640 223313920 ⟨⟨71390559554, 71390559560⟩, ⟨69615663385, 73178199215⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 234618880 235274240 223313920 226099200 ⟨⟨72574034841, 72574034847⟩, ⟨70790840098, 74370029600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 235274240 235929600 223313920 226099200 ⟨⟨72252788625, 72252788632⟩, ⟨70474118758, 74044210599⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 233308160 235929600 214958080 226099200 t = true :=
  ⟨_, (join_sr (m := 220528640) (by decide) (join_su (m := 234618880) (by decide) (join_sr (m := 217743360) (by decide) (join_su (m := 233963520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 233963520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 217743360) (by decide) (join_su (m := 235274240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 235274240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 234618880) (by decide) (join_sr (m := 223313920) (by decide) (join_su (m := 233963520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 233963520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 223313920) (by decide) (join_su (m := 235274240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 235274240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (89/320 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
