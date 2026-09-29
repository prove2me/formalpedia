-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u141557760_146800640_r225443840_249036800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:43:17.065073+00:00
-- url     : https://prove2.me/submissions/9172065e-1d67-4f4a-824e-8df3bb9f2068

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [27/160, 7/40]`, `ρ ∈ [43/160, 19/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 141557760 142868480 225443840 231342080 ⟨⟨132058300951, 132058300960⟩, ⟨126507711711, 137709765260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 142868480 144179200 225443840 231342080 ⟨⟨130989412104, 130989412114⟩, ⟨125478524455, 136600081860⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 141557760 142868480 231342080 237240320 ⟨⟨135083942590, 135083942598⟩, ⟨129513455760, 140754824956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 142868480 144179200 231342080 237240320 ⟨⟨133995884293, 133995884303⟩, ⟨128465077924, 139626011417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 144179200 145489920 225443840 231342080 ⟨⟨129930495778, 129930495788⟩, ⟨124458783440, 135500915700⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 145489920 146800640 225443840 231342080 ⟨⟨128881370479, 128881370488⟩, ⟨123448317889, 134412074148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 144179200 145489920 231342080 237240320 ⟨⟨132917868640, 132917868649⟩, ⟨127426220992, 138507780151⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 145489920 146800640 231342080 237240320 ⟨⟨131849714216, 131849714224⟩, ⟨126396714090, 137399938802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 141557760 142868480 237240320 243138560 ⟨⟨138094596179, 138094596189⟩, ⟨132504458626, 143784648602⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 142868480 144179200 237240320 243138560 ⟨⟨136987660000, 136987660009⟩, ⟨131437176308, 142637001843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 141557760 142868480 243138560 249036800 ⟨⟨141090515797, 141090515807⟩, ⟨135480968460, 146799496267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 142868480 144179200 243138560 249036800 ⟨⟨139964986329, 139964986339⟩, ⟨134395060993, 145633306026⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 144179200 145489920 237240320 243138560 ⟨⟨135890831385, 135890831393⟩, ⟨130379484437, 141499997116⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 145489920 146800640 237240320 243138560 ⟨⟨134803929089, 134803929096⟩, ⟨129331212131, 140373442432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 144179200 145489920 243138560 249036800 ⟨⟨138849624334, 138849624344⟩, ⟨133318808580, 144477812500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 145489920 146800640 243138560 249036800 ⟨⟨137744248828, 137744248836⟩, ⟨132252040415, 143332824158⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 141557760 146800640 225443840 249036800 t = true :=
  ⟨_, (join_sr (m := 237240320) (by decide) (join_su (m := 144179200) (by decide) (join_sr (m := 231342080) (by decide) (join_su (m := 142868480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 142868480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 231342080) (by decide) (join_su (m := 145489920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 145489920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 144179200) (by decide) (join_sr (m := 243138560) (by decide) (join_su (m := 142868480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 142868480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 243138560) (by decide) (join_su (m := 145489920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 145489920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (27/160 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (43/160 : ℝ) (19/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e3 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
