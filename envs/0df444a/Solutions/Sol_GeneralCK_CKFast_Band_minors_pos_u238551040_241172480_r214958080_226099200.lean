-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u238551040_241172480_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:34:06.817333+00:00
-- url     : https://prove2.me/submissions/9453a17e-3da5-48dc-8593-df48207f18c3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [91/320, 23/80]`, `ρ ∈ [41/160, 69/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 238551040 239206400 214958080 217743360 ⟨⟨68122926275, 68122926280⟩, ⟨66377774115, 69880567391⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 239206400 239861760 214958080 217743360 ⟨⟨67817060535, 67817060541⟩, ⟨66076288811, 69570274634⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 238551040 239206400 217743360 220528640 ⟨⟨68968858592, 68968858599⟩, ⟨67219975971, 70730239500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 239206400 239861760 217743360 220528640 ⟨⟨68659455700, 68659455707⟩, ⟨66914963284, 70416399938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 239861760 240517120 214958080 217743360 ⟨⟨67511957759, 67511957766⟩, ⟨65775547716, 69260763875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 240517120 241172480 214958080 217743360 ⟨⟨67207612506, 67207612509⟩, ⟨65475545520, 68952029533⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 239861760 240517120 217743360 220528640 ⟨⟨68350821336, 68350821343⟩, ⟨66610700370, 70103347934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 240517120 241172480 217743360 220528640 ⟨⟨68042950030, 68042950032⟩, ⟨66307181885, 69791077882⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 238551040 239206400 220528640 223313920 ⟨⟨69814096930, 69814096936⟩, ⟨68061486289, 71579215133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 239206400 239861760 220528640 223313920 ⟨⟨69501165534, 69501165540⟩, ⟨67752954796, 71261837483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 238551040 239206400 223313920 226099200 ⟨⟨70658644611, 70658644616⟩, ⟨68902308379, 72427497625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 239206400 239861760 223313920 226099200 ⟨⟨70342193308, 70342193313⟩, ⟨68590266606, 72106590554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 239861760 240517120 220528640 223313920 ⟨⟨69189008144, 69189008151⟩, ⟨67445178553, 70945252868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 240517120 241172480 220528640 223313920 ⟨⟨68877619260, 68877619263⟩, ⟨67138152192, 70629455652⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 239861760 240517120 223313920 226099200 ⟨⟨70026521403, 70026521409⟩, ⟨68278985478, 71786481910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 240517120 241172480 223313920 226099200 ⟨⟨69711623369, 69711623372⟩, ⟨67968459597, 71467166025⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 238551040 241172480 214958080 226099200 t = true :=
  ⟨_, (join_sr (m := 220528640) (by decide) (join_su (m := 239861760) (by decide) (join_sr (m := 217743360) (by decide) (join_su (m := 239206400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 239206400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 217743360) (by decide) (join_su (m := 240517120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 240517120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 239861760) (by decide) (join_sr (m := 223313920) (by decide) (join_su (m := 239206400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 239206400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 223313920) (by decide) (join_su (m := 240517120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 240517120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (91/320 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
