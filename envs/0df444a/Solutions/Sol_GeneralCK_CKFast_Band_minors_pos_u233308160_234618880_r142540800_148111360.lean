-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u233308160_234618880_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:29:40.543347+00:00
-- url     : https://prove2.me/submissions/c44287f6-939c-4b0c-b06e-8678fad35627

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [89/320, 179/640]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 233308160 233635840 142540800 143933440 ⟨⟨47410716603, 47410716606⟩, ⟨46568724829, 48255869294⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 233635840 233963520 142540800 143933440 ⟨⟨47303272864, 47303272870⟩, ⟨46462349187, 48147350940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 233308160 233635840 143933440 145326080 ⟨⟨47859282154, 47859282157⟩, ⟨47016315089, 48705411381⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 233635840 233963520 143933440 145326080 ⟨⟨47750874143, 47750874148⟩, ⟨46908976674, 48595927260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 233963520 234291200 142540800 143933440 ⟨⟨47195985079, 47195985084⟩, ⟨46356127033, 48038991023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 234291200 234618880 142540800 143933440 ⟨⟨47088852650, 47088852657⟩, ⟨46250057778, 47930788945⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 233963520 234291200 143933440 145326080 ⟨⟨47642623156, 47642623161⟩, ⟨46801792817, 48486602652⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 234291200 234618880 143933440 145326080 ⟨⟨47534528596, 47534528602⟩, ⟨46694762926, 48377436952⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 233308160 233635840 145326080 146718720 ⟨⟨48307628767, 48307628768⟩, ⟨47463686855, 49154734078⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 233635840 233963520 145326080 146718720 ⟨⟨48198257866, 48198257871⟩, ⟨47355387046, 49044285583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 233308160 233635840 146718720 148111360 ⟨⟨48755756967, 48755756970⟩, ⟨47910840654, 49603837917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 233635840 233963520 146718720 148111360 ⟨⟨48645424559, 48645424565⟩, ⟨47801580826, 49492426433⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 233963520 234291200 145326080 146718720 ⟨⟨48089045056, 48089045061⟩, ⟨47247242858, 48933997666⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 234291200 234618880 145326080 146718720 ⟨⟨47979989735, 47979989741⟩, ⟨47139253698, 48823869721⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 233963520 234291200 146718720 148111360 ⟨⟨48535251301, 48535251306⟩, ⟨47692477676, 49381176588⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 234291200 234618880 146718720 148111360 ⟨⟨48425236585, 48425236592⟩, ⟨47583530606, 49270087770⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 233308160 234618880 142540800 148111360 t = true :=
  ⟨_, (join_sr (m := 145326080) (by decide) (join_su (m := 233963520) (by decide) (join_sr (m := 143933440) (by decide) (join_su (m := 233635840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 233635840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 143933440) (by decide) (join_su (m := 234291200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 234291200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 233963520) (by decide) (join_sr (m := 146718720) (by decide) (join_su (m := 233635840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 233635840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 146718720) (by decide) (join_su (m := 234291200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 234291200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (89/320 : ℝ) (179/640 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e1 : (((234618880 : ℤ) : ℝ) / (D : ℝ)) = (179/640 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
