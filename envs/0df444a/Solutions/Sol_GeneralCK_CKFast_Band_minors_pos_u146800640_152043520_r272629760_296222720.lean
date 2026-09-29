-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_152043520_r272629760_296222720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:59:13.94089+00:00
-- url     : https://prove2.me/submissions/d0fa1f24-4339-45bb-9501-253565876348

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 29/160]`, `ρ ∈ [13/40, 113/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 148111360 272629760 278528000 ⟨⟨151061498221, 151061498225⟩, ⟨145512990234, 156703298147⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 148111360 149422080 272629760 278528000 ⟨⟨149887577305, 149887577313⟩, ⟨144376562383, 155490988871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 146800640 148111360 278528000 284426240 ⟨⟨153906192975, 153906192979⟩, ⟨148339396482, 159565860588⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 148111360 149422080 278528000 284426240 ⟨⟨152715388163, 152715388171⟩, ⟨147186044246, 158336723306⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 149422080 150732800 272629760 278528000 ⟨⟨148723363874, 148723363882⟩, ⟨143249389756, 154288852531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 150732800 152043520 272629760 278528000 ⟨⟨147568694738, 147568694748⟩, ⟨142131317569, 153096717276⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 149422080 150732800 278528000 284426240 ⟨⟨151534326792, 151534326802⟩, ⟨146041987544, 157117790143⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 150732800 152043520 278528000 284426240 ⟨⟨150362846190, 150362846199⟩, ⟨144907071953, 155908889924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 146800640 148111360 284426240 290324480 ⟨⟨156738738881, 156738738885⟩, ⟨151153841756, 162416085182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 148111360 149422080 284426240 290324480 ⟨⟨155531275932, 155531275940⟩, ⟨149983787021, 161170349436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 146800640 148111360 290324480 296222720 ⟨⟨159559331703, 159559331705⟩, ⟨153956517636, 165254171915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 148111360 149422080 290324480 296222720 ⟨⟨158335431319, 158335431329⟩, ⟨152769977373, 163992062052⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 149422080 150732800 284426240 290324480 ⟨⟨154333588748, 154333588757⟩, ⟨148823064537, 159934845321⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 150732800 152043520 284426240 290324480 ⟨⟨153145515222, 153145515231⟩, ⟨147671520298, 158709402393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 149422080 150732800 290324480 296222720 ⟨⟨157121335522, 157121335530⟩, ⟨151592802608, 162740207798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 150732800 152043520 290324480 296222720 ⟨⟨155916882814, 155916882822⟩, ⟨150424839801, 161498439485⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 152043520 272629760 296222720 t = true :=
  ⟨_, (join_sr (m := 284426240) (by decide) (join_su (m := 149422080) (by decide) (join_sr (m := 278528000) (by decide) (join_su (m := 148111360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 148111360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 278528000) (by decide) (join_su (m := 150732800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 150732800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 149422080) (by decide) (join_sr (m := 290324480) (by decide) (join_su (m := 148111360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 148111360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 290324480) (by decide) (join_su (m := 150732800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 150732800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (29/160 : ℝ) →
    rho ∈ Set.Icc (13/40 : ℝ) (113/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e2 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  have e3 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
