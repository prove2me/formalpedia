-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_162529280_r249036800_272629760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:58:43.692371+00:00
-- url     : https://prove2.me/submissions/ca36b501-6026-4bb0-9a92-15ec603da68b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 31/160]`, `ρ ∈ [19/64, 13/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 158597120 249036800 254935040 ⟨⟨130982734411, 130982734421⟩, ⟨125797606088, 136255565141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 158597120 159907840 249036800 254935040 ⟨⟨129950499689, 129950499698⟩, ⟨124799471442, 135188383841⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 157286400 158597120 254935040 260833280 ⟨⟨133736799132, 133736799141⟩, ⟨128532506378, 139028492621⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 158597120 159907840 254935040 260833280 ⟨⟨132687144880, 132687144887⟩, ⟨127516957845, 137943898659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 159907840 161218560 249036800 254935040 ⟨⟨128926570531, 128926570535⟩, ⟨123809239285, 134129923831⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 161218560 162529280 249036800 254935040 ⟨⟨127910809143, 127910809150⟩, ⟨122826779215, 133080039688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 159907840 161218560 254935040 260833280 ⟨⟨131645849341, 131645849347⟩, ⟨126509368023, 136868075723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 161218560 162529280 254935040 260833280 ⟨⟨130612774767, 130612774776⟩, ⟨125509606434, 135800878548⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 157286400 158597120 260833280 266731520 ⟨⟨136479760006, 136479760013⟩, ⟨131256474449, 141790142784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 158597120 159907840 260833280 266731520 ⟨⟨135412901844, 135412901851⟩, ⟨130223723660, 140688355736⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 157286400 158597120 266731520 272629760 ⟨⟨139211786819, 139211786827⟩, ⟨133969676583, 144540688967⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 158597120 159907840 266731520 272629760 ⟨⟨138127935839, 138127935848⟩, ⟨132919930761, 143421923749⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 159907840 161218560 260833280 266731520 ⟨⟨134354451869, 134354451871⟩, ⟨129198984182, 139595385706⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 161218560 162529280 260833280 266731520 ⟨⟨133304272430, 133304272437⟩, ⟨128182125524, 138511087664⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 159907840 161218560 266731520 272629760 ⟨⟨137052538955, 137052538961⟩, ⟨131878245341, 142312017935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 161218560 162529280 266731520 272629760 ⟨⟨135985458680, 135985458688⟩, ⟨130844489882, 141210826773⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 162529280 249036800 272629760 t = true :=
  ⟨_, (join_sr (m := 260833280) (by decide) (join_su (m := 159907840) (by decide) (join_sr (m := 254935040) (by decide) (join_su (m := 158597120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 158597120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 254935040) (by decide) (join_su (m := 161218560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 161218560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 159907840) (by decide) (join_sr (m := 266731520) (by decide) (join_su (m := 158597120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 158597120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 266731520) (by decide) (join_su (m := 161218560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 161218560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (19/64 : ℝ) (13/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e3 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
