-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_146800640_r390594560_414187520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:51:20.947341+00:00
-- url     : https://prove2.me/submissions/994172f1-ba96-461c-bfec-85115288b5c6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 7/40]`, `ρ ∈ [149/320, 79/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 138936320 390594560 396492800 ⟨⟨217238730818, 217238730823⟩, ⟨207268062972, 227445373177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 136314880 138936320 396492800 402391040 ⟨⟨219972381338, 219972381343⟩, ⟨209973749261, 230205769695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 138936320 141557760 390594560 396492800 ⟨⟨214144128987, 214144128995⟩, ⟨204286501144, 224234729497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 138936320 141557760 396492800 402391040 ⟨⟨216851682793, 216851682803⟩, ⟨206965719332, 226969477582⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 136314880 138936320 402391040 408289280 ⟨⟨222696075763, 222696075768⟩, ⟨212669695536, 232955990945⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 136314880 138936320 408289280 414187520 ⟨⟨225409979323, 225409979326⟩, ⟨215356062291, 235696206938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 138936320 141557760 402391040 408289280 ⟨⟨219549595847, 219549595857⟩, ⟨209635506609, 229694371447⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 138936320 141557760 408289280 414187520 ⟨⟨222238026188, 222238026196⟩, ⟨212296016518, 232409573675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 141557760 144179200 390594560 396492800 ⟨⟨211093069777, 211093069787⟩, ⟨201346070514, 221070099892⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 141557760 144179200 396492800 402391040 ⟨⟨213774426782, 213774426792⟩, ⟨203998752725, 223779063917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 144179200 146800640 390594560 396492800 ⟨⟨208084237272, 208084237282⟩, ⟨198445533774, 217950088552⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 144179200 146800640 396492800 402391040 ⟨⟨210739308188, 210739308197⟩, ⟨201071621244, 220633145535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 141557760 144179200 402391040 408289280 ⟨⟨216446451052, 216446451063⟩, ⟨206642305709, 226478487603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 141557760 144179200 408289280 414187520 ⟨⟨219109293724, 219109293732⟩, ⟨209276876340, 229168526396⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 144179200 146800640 402391040 408289280 ⟨⟨213385347130, 213385347140⟩, ⟨203688873847, 223306968927⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 144179200 146800640 408289280 414187520 ⟨⟨216022498604, 216022498612⟩, ⟨206297432051, 225971707322⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 146800640 390594560 414187520 t = true :=
  ⟨_, (join_su (m := 141557760) (by decide) (join_sr (m := 402391040) (by decide) (join_su (m := 138936320) (by decide) (join_sr (m := 396492800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 396492800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 138936320) (by decide) (join_sr (m := 408289280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 408289280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 402391040) (by decide) (join_su (m := 144179200) (by decide) (join_sr (m := 396492800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 396492800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 144179200) (by decide) (join_sr (m := 408289280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 408289280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (149/320 : ℝ) (79/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((390594560 : ℤ) : ℝ) / (D : ℝ)) = (149/320 : ℝ) := by norm_num [D]
  have e3 : (((414187520 : ℤ) : ℝ) / (D : ℝ)) = (79/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
