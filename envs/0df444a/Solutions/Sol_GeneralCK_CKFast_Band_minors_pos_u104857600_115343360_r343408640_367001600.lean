-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_115343360_r343408640_367001600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:43:29.755901+00:00
-- url     : https://prove2.me/submissions/d0b9bf10-eb19-4fce-837b-ef70f55756da

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 11/80]`, `ρ ∈ [131/320, 7/16]` by 15 cells of the computing
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
theorem cell0 : cellOK 104857600 107479040 343408640 349306880 ⟨⟨233513736283, 233513736295⟩, ⟨222136633025, 245188140047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 104857600 107479040 349306880 355205120 ⟨⟨236672876507, 236672876519⟩, ⟨225273070134, 248367422082⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 107479040 110100480 343408640 349306880 ⟨⟨229975911412, 229975911424⟩, ⟨218755889107, 241488283996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 107479040 110100480 349306880 355205120 ⟨⟨233107657954, 233107657965⟩, ⟨221864025019, 244641228804⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 104857600 107479040 355205120 367001600 ⟨⟨241380237435, 241380237447⟩, ⟨227110440994, 256102632334⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 107479040 110100480 355205120 361103360 ⟨⟨236223138985, 236223138997⟩, ⟨224956236330, 247777576827⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 107479040 110100480 361103360 367001600 ⟨⟨239322671605, 239322671616⟩, ⟨228032829942, 250897655304⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 110100480 112721920 343408640 349306880 ⟨⟨226504990743, 226504990750⟩, ⟨215437800175, 237859710019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 110100480 112721920 349306880 355205120 ⟨⟨229609107103, 229609107107⟩, ⟨218517466969, 240986004951⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 112721920 115343360 343408640 349306880 ⟨⟨223098519557, 223098519569⟩, ⟨212180085574, 234299785605⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 112721920 115343360 349306880 355205120 ⟨⟨226174795002, 226174795013⟩, ⟨215231136822, 237399148490⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 110100480 112721920 355205120 361103360 ⟨⟨232697456499, 232697456507⟩, ⟨221581702031, 244096205365⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 110100480 112721920 361103360 367001600 ⟨⟨235770341811, 235770341817⟩, ⟨224630798508, 247190623833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 112721920 115343360 355205120 361103360 ⟨⟨229235790894, 229235790905⟩, ⟨218267237491, 240482908747⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 112721920 115343360 361103360 367001600 ⟨⟨232281796479, 232281796488⟩, ⟨221288667559, 243551364891⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 115343360 343408640 367001600 t = true :=
  ⟨_, (join_su (m := 110100480) (by decide) (join_sr (m := 355205120) (by decide) (join_su (m := 107479040) (by decide) (join_sr (m := 349306880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 349306880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 107479040) (by decide) (leaf_ok cell4) (join_sr (m := 361103360) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 355205120) (by decide) (join_su (m := 112721920) (by decide) (join_sr (m := 349306880) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 349306880) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 112721920) (by decide) (join_sr (m := 361103360) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 361103360) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (131/320 : ℝ) (7/16 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((343408640 : ℤ) : ℝ) / (D : ℝ)) = (131/320 : ℝ) := by norm_num [D]
  have e3 : (((367001600 : ℤ) : ℝ) / (D : ℝ)) = (7/16 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
