-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u165150720_167772160_r95682560_101580800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:24:04.209429+00:00
-- url     : https://prove2.me/submissions/dde9c246-888a-447f-b057-9c18d4792aca

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [63/320, 1/5]`, `ρ ∈ [73/640, 31/256]` by 18 cells of the computing
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
theorem cell0 : cellOK 165150720 165806080 95682560 97157120 ⟨⟨51000824856, 51000824860⟩, ⟨49210495913, 52805222749⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 165150720 165806080 97157120 98631680 ⟨⟨51746716076, 51746716077⟩, ⟨49953705915, 53553793235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 165806080 166461440 95682560 97157120 ⟨⟨50775984003, 50775984009⟩, ⟨48991004339, 52574956022⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 165806080 166461440 97157120 98631680 ⟨⟨51518848009, 51518848015⟩, ⟨49731195673, 53320490923⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 165150720 165806080 98631680 100106240 ⟨⟨52491671424, 52491671428⟩, ⟨50695986063, 54301421788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 165150720 165806080 100106240 101580800 ⟨⟨53235694595, 53235694600⟩, ⟨51437340018, 55048112132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 165806080 166461440 98631680 100106240 ⟨⟨52260787008, 52260787015⟩, ⟨50470467921, 54065094850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 165806080 166461440 100106240 101580800 ⟨⟨53001804632, 53001804639⟩, ⟨51208824684, 54808771466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 166461440 166789120 95682560 97157120 ⟨⟨50608098738, 50608098744⟩, ⟨49500085534, 51721572713⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 166789120 167116800 95682560 97157120 ⟨⟨50496527553, 50496527559⟩, ⟨49390373162, 51608126339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 166461440 167116800 97157120 98631680 ⟨⟨51292127135, 51292127141⟩, ⟨49509795279, 53088373872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 167116800 167444480 95682560 97157120 ⟨⟨50385236616, 50385236622⟩, ⟨49280934816, 51494966511⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 167444480 167772160 95682560 97157120 ⟨⟨50274224557, 50274224563⟩, ⟨49171769159, 51382091827⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 167116800 167772160 97157120 98631680 ⟨⟨51066542238, 51066542244⟩, ⟨49289493912, 52857430463⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 166461440 167116800 98631680 100106240 ⟨⟨52031061975, 52031061982⟩, ⟨50246071795, 53829965383⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 166461440 167116800 100106240 101580800 ⟨⟨52769086118, 52769086126⟩, ⟨50981443409, 54570640355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 167116800 167772160 98631680 100106240 ⟨⟨51802485010, 51802485018⟩, ⟨50022786765, 53596021668⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 167116800 167772160 100106240 101580800 ⟨⟨52537527644, 52537527650⟩, ⟨50755185182, 54333706985⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 165150720 167772160 95682560 101580800 t = true :=
  ⟨_, (join_su (m := 166461440) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 165806080) (by decide) (join_sr (m := 97157120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 97157120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 165806080) (by decide) (join_sr (m := 100106240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 100106240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 98631680) (by decide) (join_su (m := 167116800) (by decide) (join_sr (m := 97157120) (by decide) (join_su (m := 166789120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 97157120) (by decide) (join_su (m := 167444480) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))) (join_su (m := 167116800) (by decide) (join_sr (m := 100106240) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_sr (m := 100106240) (by decide) (leaf_ok cell16) (leaf_ok cell17)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (63/320 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (31/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((101580800 : ℤ) : ℝ) / (D : ℝ)) = (31/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
