-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_146800640_r414187520_437780480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:52:21.160326+00:00
-- url     : https://prove2.me/submissions/8afbb633-1653-4871-a3eb-8ad1a7c50bdf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 7/40]`, `ρ ∈ [79/160, 167/320]` by 14 cells of the computing
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
theorem cell0 : cellOK 136314880 138936320 414187520 420085760 ⟨⟨228114254483, 228114254488⟩, ⟨218033007370, 238426584812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 136314880 138936320 420085760 425984000 ⟨⟨230809061021, 230809061026⟩, ⟨220700686023, 241147288895⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 138936320 141557760 414187520 420085760 ⟨⟨224917129264, 224917129275⟩, ⟨214947400117, 235115244155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 138936320 141557760 420085760 425984000 ⟨⟨227587058003, 227587058014⟩, ⟨217589806038, 237811540144⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 136314880 138936320 425984000 437780480 ⟨⟨234833860203, 234833860207⟩, ⟨222407019913, 247604083552⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 138936320 141557760 425984000 437780480 ⟨⟨231575077693, 231575077703⟩, ⟨219298655807, 244190504397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 141557760 144179200 414187520 420085760 ⟨⟨221763103503, 221763103514⟩, ⟨211902609157, 231849333223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 141557760 144179200 420085760 425984000 ⟨⟨224408026734, 224408026744⟩, ⟨214519646422, 234521058541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 144179200 146800640 414187520 420085760 ⟨⟨218650904840, 218650904850⟩, ⟨208897434135, 228627506954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 144179200 146800640 420085760 425984000 ⟨⟨221270705855, 221270705865⟩, ⟨211489016247, 231274511742⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 141557760 144179200 425984000 431882240 ⟨⟨227044207443, 227044207452⟩, ⟨217128128178, 237183850405⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 141557760 144179200 431882240 437780480 ⟨⟨229671787396, 229671787407⟩, ⟨219728192285, 239837854523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 144179200 146800640 425984000 431882240 ⟨⟨223882039494, 223882039504⟩, ⟨214072312445, 233912863364⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 144179200 146800640 431882240 437780480 ⟨⟨226485041482, 226485041491⟩, ⟨216647454752, 236542701285⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 146800640 414187520 437780480 t = true :=
  ⟨_, (join_su (m := 141557760) (by decide) (join_sr (m := 425984000) (by decide) (join_su (m := 138936320) (by decide) (join_sr (m := 420085760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 420085760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 138936320) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 425984000) (by decide) (join_su (m := 144179200) (by decide) (join_sr (m := 420085760) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 420085760) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 144179200) (by decide) (join_sr (m := 431882240) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 431882240) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (79/160 : ℝ) (167/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((414187520 : ℤ) : ℝ) / (D : ℝ)) = (79/160 : ℝ) := by norm_num [D]
  have e3 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
