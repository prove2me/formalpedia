-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_241172480_r460062720_482344960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:19:15.435889+00:00
-- url     : https://prove2.me/submissions/c6e46558-998a-41a2-9ad0-3ec6075053c3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 23/80]`, `ρ ∈ [351/640, 23/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 237240320 460062720 465633280 ⟨⟨142718835473, 142718835481⟩, ⟨138562134157, 146928384885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 237240320 238551040 460062720 465633280 ⟨⟨141531796855, 141531796863⟩, ⟨137395260126, 145720908221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 235929600 237240320 465633280 471203840 ⟨⟨144331209751, 144331209759⟩, ⟨140160200703, 148555095137⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 237240320 238551040 465633280 471203840 ⟨⟨143132411978, 143132411986⟩, ⟨138981605012, 147335824667⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 238551040 239861760 460062720 465633280 ⟨⟨140348780230, 140348780232⟩, ⟨136232277980, 144517585438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 239861760 241172480 460062720 465633280 ⟨⟨139169736754, 139169736762⟩, ⟨135073140284, 143318366285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 238551040 239861760 465633280 471203840 ⟨⟨141937637216, 141937637220⟩, ⟨137806903096, 146120708164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 239861760 241172480 465633280 471203840 ⟨⟨140746836767, 140746836774⟩, ⟨136636047644, 144909695542⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 237240320 471203840 476774400 ⟨⟨145941755704, 145941755712⟩, ⟨141756450740, 150179964237⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 237240320 238551040 471203840 476774400 ⟨⟨144731239792, 144731239800⟩, ⟨140566173692, 148948941707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 235929600 237240320 476774400 482344960 ⟨⟨147550493791, 147550493799⟩, ⟨143350904533, 151803012828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 237240320 238551040 476774400 482344960 ⟨⟨146328300222, 146328300230⟩, ⟨142148985911, 150560279438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 238551040 239861760 471203840 476774400 ⟨⟨143524747253, 143524747258⟩, ⟨139379791669, 147722072559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 239861760 241172480 471203840 476774400 ⟨⟨142322229540, 142322229548⟩, ⟨138197257484, 146499306880⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 238551040 239861760 476774400 482344960 ⟨⟨145110129744, 145110129749⟩, ⟨140950962926, 149321698193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 239861760 241172480 476774400 482344960 ⟨⟨143895933965, 143895933973⟩, ⟨139756788529, 148087219354⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 241172480 460062720 482344960 t = true :=
  ⟨_, (join_sr (m := 471203840) (by decide) (join_su (m := 238551040) (by decide) (join_sr (m := 465633280) (by decide) (join_su (m := 237240320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 237240320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 465633280) (by decide) (join_su (m := 239861760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 239861760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 238551040) (by decide) (join_sr (m := 476774400) (by decide) (join_su (m := 237240320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 237240320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 476774400) (by decide) (join_su (m := 239861760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 239861760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (351/640 : ℝ) (23/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((460062720 : ℤ) : ℝ) / (D : ℝ)) = (351/640 : ℝ) := by norm_num [D]
  have e3 : (((482344960 : ℤ) : ℝ) / (D : ℝ)) = (23/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
