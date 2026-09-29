-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_71303168_r135659520_159907840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:43:03.132884+00:00
-- url     : https://prove2.me/submissions/a3c541a9-81a8-4ae4-b78a-c6c62e0689b0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 17/200]`, `ρ ∈ [207/1280, 61/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 67108864 68157440 135659520 141721600 ⟨⟨148367884498, 148367884512⟩, ⟨140040081204, 156925331583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 68157440 69206016 135659520 141721600 ⟨⟨146951940794, 146951940808⟩, ⟨138714817000, 155414557198⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 67108864 68157440 141721600 147783680 ⟨⟨153564298341, 153564298352⟩, ⟨145227294211, 162126655427⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 68157440 69206016 141721600 147783680 ⟨⟨152117240158, 152117240171⟩, ⟨143870091461, 160585744750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 69206016 70254592 135659520 141721600 ⟨⟨145560002825, 145560002839⟩, ⟨137411602510, 153929859689⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 70254592 71303168 135659520 141721600 ⟨⟨144191394307, 144191394321⟩, ⟨136129824759, 152470495192⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 69206016 70254592 141721600 147783680 ⟨⟨150694315732, 150694315745⟩, ⟨142535110654, 159070988319⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 70254592 71303168 141721600 147783680 ⟨⟨149294854474, 149294854484⟩, ⟨141221742227, 157581650564⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 67108864 68157440 147783680 153845760 ⟨⟨158685225853, 158685225867⟩, ⟨150340392865, 167251210993⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 68157440 69206016 147783680 153845760 ⟨⟨157208489271, 157208489282⟩, ⟨148952669751, 165681612562⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 67108864 68157440 153845760 159907840 ⟨⟨163733333968, 163733333979⟩, ⟨155381948274, 172301759240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 68157440 69206016 153845760 159907840 ⟨⟨162228275473, 162228275484⟩, ⟨153965046432, 170704839155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 69206016 70254592 147783680 153845760 ⟨⟨155755984641, 155755984652⟩, ⟨147587310581, 164138216657⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 70254592 71303168 147783680 153845760 ⟨⟨154327047700, 154327047713⟩, ⟨146243709903, 162620296551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 69206016 70254592 153845760 159907840 ⟨⟨160747519958, 160747519968⟩, ⟨152570622864, 169134143520⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 70254592 71303168 153845760 159907840 ⟨⟨159290410017, 159290410027⟩, ⟨151198076838, 167588954882⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 71303168 135659520 159907840 t = true :=
  ⟨_, (join_sr (m := 147783680) (by decide) (join_su (m := 69206016) (by decide) (join_sr (m := 141721600) (by decide) (join_su (m := 68157440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 68157440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 141721600) (by decide) (join_su (m := 70254592) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 70254592) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 69206016) (by decide) (join_sr (m := 153845760) (by decide) (join_su (m := 68157440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 68157440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 153845760) (by decide) (join_su (m := 70254592) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 70254592) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (17/200 : ℝ) →
    rho ∈ Set.Icc (207/1280 : ℝ) (61/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((71303168 : ℤ) : ℝ) / (D : ℝ)) = (17/200 : ℝ) := by norm_num [D]
  have e2 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  have e3 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
