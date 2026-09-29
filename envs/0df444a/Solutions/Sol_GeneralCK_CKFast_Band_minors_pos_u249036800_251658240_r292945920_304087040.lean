-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_251658240_r292945920_304087040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:31:41.511979+00:00
-- url     : https://prove2.me/submissions/c79fe270-2ca9-4560-b072-b34fa63ec141

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 3/10]`, `ρ ∈ [447/1280, 29/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 249036800 249692160 292945920 295731200 ⟨⟨85231889835, 85231889842⟩, ⟨83455070165, 87020774903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249692160 250347520 292945920 295731200 ⟨⟨84843609389, 84843609395⟩, ⟨83071136816, 86628107671⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249036800 249692160 295731200 298516480 ⟨⟨86006994164, 86006994169⟩, ⟨84226636551, 87799426857⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249692160 250347520 295731200 298516480 ⟨⟨85615453453, 85615453459⟩, ⟨83839451159, 87403491245⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 250347520 251002880 292945920 295731200 ⟨⟨84456126138, 84456126141⟩, ⟨82687984022, 86236254473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 251002880 251658240 292945920 295731200 ⟨⟨84069434694, 84069434699⟩, ⟨82305606502, 85845209817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 250347520 251002880 295731200 298516480 ⟨⟨85224713155, 85224713158⟩, ⟨83453049552, 87008372870⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 251002880 251658240 295731200 298516480 ⟨⟨84834767866, 84834767873⟩, ⟨83067426439, 86614066226⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 249692160 298516480 301301760 ⟨⟨86781602170, 86781602176⟩, ⟨84997707798, 88577581258⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249692160 250347520 298516480 301301760 ⟨⟨86386807485, 86386807491⟩, ⟨84607276601, 88178383610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 249036800 249692160 301301760 304087040 ⟨⟨87555716210, 87555716215⟩, ⟨85768286253, 89355240472⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 249692160 250347520 301301760 304087040 ⟨⟨87157673806, 87157673812⟩, ⟨85374615458, 88952787093⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 250347520 251002880 298516480 301301760 ⟨⟨85992816370, 85992816373⟩, ⟨84217632364, 87780006339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 251002880 251658240 298516480 301301760 ⟨⟨85599623410, 85599623415⟩, ⟨83828769778, 87382443926⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 250347520 251002880 301301760 304087040 ⟨⟨86760438070, 86760438072⟩, ⟨84981734735, 88551157169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 251002880 251658240 301301760 304087040 ⟨⟨86364003572, 86364003577⟩, ⟨84589638765, 88150345171⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 251658240 292945920 304087040 t = true :=
  ⟨_, (join_sr (m := 298516480) (by decide) (join_su (m := 250347520) (by decide) (join_sr (m := 295731200) (by decide) (join_su (m := 249692160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 249692160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 295731200) (by decide) (join_su (m := 251002880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 251002880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 250347520) (by decide) (join_sr (m := 301301760) (by decide) (join_su (m := 249692160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 249692160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 301301760) (by decide) (join_su (m := 251002880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 251002880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (447/1280 : ℝ) (29/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  have e3 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
