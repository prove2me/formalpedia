-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_199229440_r248381440_259522560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:26:22.337559+00:00
-- url     : https://prove2.me/submissions/657be3fe-7bad-4141-abc2-7c06e074a312

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 19/80]`, `ρ ∈ [379/1280, 99/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 193986560 195297280 248381440 251166720 ⟨⟨103962435545, 103962435551⟩, ⟨100390812021, 107578761125⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 193986560 195297280 251166720 253952000 ⟨⟨105043936999, 105043937005⟩, ⟨101464496921, 108668084803⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 195297280 196608000 248381440 251166720 ⟨⟨103124893512, 103124893520⟩, ⟨99570906756, 106723260406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 195297280 196608000 251166720 253952000 ⟨⟨104198813465, 104198813471⟩, ⟨100637034201, 107804980060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 193986560 195297280 253952000 256737280 ⟨⟨106124021978, 106124021985⟩, ⟨102536778788, 109755978211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 193986560 195297280 256737280 259522560 ⟨⟨107202698918, 107202698924⟩, ⟨103607665967, 110842449878⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 195297280 196608000 253952000 256737280 ⟨⟨105271346883, 105271346891⟩, ⟨101701788119, 108885299830⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 195297280 196608000 256737280 259522560 ⟨⟨106342501972, 106342501978⟩, ⟨102765176623, 109964228004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 196608000 197918720 248381440 251166720 ⟨⟨102292671436, 102292671443⟩, ⟨98756137176, 105873268154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 196608000 197918720 251166720 253952000 ⟨⟨103359033619, 103359033627⟩, ⟨99814731243, 106947407136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 197918720 199229440 248381440 251166720 ⟨⟨101465690291, 101465690298⟩, ⟨97946427166, 105028702366⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 197918720 199229440 251166720 253952000 ⟨⟨102524518295, 102524518303⟩, ⟨98997511768, 106095283900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 196608000 197918720 253952000 256737280 ⟨⟨104424038682, 104424038690⟩, ⟨100871980763, 108020176081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 196608000 197918720 256737280 259522560 ⟨⟨105487694598, 105487694606⟩, ⟨101927893633, 109091583044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 197918720 199229440 253952000 256737280 ⟨⟨103582018066, 103582018074⟩, ⟨100047280293, 107160524708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 197918720 199229440 256737280 259522560 ⟨⟨104638197359, 104638197367⟩, ⟨101095740418, 108224432625⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 199229440 248381440 259522560 t = true :=
  ⟨_, (join_su (m := 196608000) (by decide) (join_sr (m := 253952000) (by decide) (join_su (m := 195297280) (by decide) (join_sr (m := 251166720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 251166720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 195297280) (by decide) (join_sr (m := 256737280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 256737280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 253952000) (by decide) (join_su (m := 197918720) (by decide) (join_sr (m := 251166720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 251166720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 197918720) (by decide) (join_sr (m := 256737280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 256737280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (379/1280 : ℝ) (99/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  have e3 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
