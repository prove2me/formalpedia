-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u131072000_136314880_r249036800_272629760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:43:02.639149+00:00
-- url     : https://prove2.me/submissions/ae61754b-b839-4eb6-9f8e-317dba22f7a2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [5/32, 13/80]`, `ρ ∈ [19/64, 13/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 131072000 132382720 249036800 254935040 ⟨⟨153613889611, 153613889621⟩, ⟨147648918661, 159686610609⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 132382720 133693440 249036800 254935040 ⟨⟨152381213004, 152381213014⟩, ⟨146460282518, 158408728376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 131072000 132382720 254935040 260833280 ⟨⟨156727188324, 156727188333⟩, ⟨150743804215, 162817676473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 132382720 133693440 254935040 260833280 ⟨⟨155476084514, 155476084523⟩, ⟨149536653152, 161521477233⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 133693440 135004160 249036800 254935040 ⟨⟨151160371628, 151160371634⟩, ⟨145282883495, 157143298952⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 135004160 136314880 249036800 254935040 ⟨⟨149951146187, 149951146195⟩, ⟨144116514728, 155890090188⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 133693440 135004160 254935040 260833280 ⟨⟨154236861317, 154236861322⟩, ⟨148340791123, 160237768983⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 135004160 136314880 254935040 260833280 ⟨⟨153009300260, 153009300270⟩, ⟨147156011844, 158966320666⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 131072000 132382720 260833280 266731520 ⟨⟨159824197090, 159824197098⟩, ⟨153822663299, 165932189356⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 132382720 133693440 260833280 266731520 ⟨⟨158554969386, 158554969394⟩, ⟨152597295542, 164617981288⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 131072000 132382720 266731520 272629760 ⟨⟨162905207061, 162905207072⟩, ⟨156885780149, 169030447384⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 132382720 133693440 266731520 272629760 ⟨⟨161618151030, 161618151039⟩, ⟨155642486406, 167698530710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 133693440 135004160 260833280 266731520 ⟨⟨157297662591, 157297662593⟩, ⟨151383263692, 163316297281⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 135004160 136314880 260833280 266731520 ⟨⟨156052059137, 156052059145⟩, ⟨150180362122, 162026907443⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 133693440 135004160 266731520 272629760 ⟨⟨160343051327, 160343051332⟩, ⟨154410570598, 166379166265⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 135004160 136314880 266731520 272629760 ⟨⟨159079691362, 159079691372⟩, ⟨153189827842, 165072125392⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 131072000 136314880 249036800 272629760 t = true :=
  ⟨_, (join_sr (m := 260833280) (by decide) (join_su (m := 133693440) (by decide) (join_sr (m := 254935040) (by decide) (join_su (m := 132382720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 132382720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 254935040) (by decide) (join_su (m := 135004160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 135004160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 133693440) (by decide) (join_sr (m := 266731520) (by decide) (join_su (m := 132382720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 132382720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 266731520) (by decide) (join_su (m := 135004160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 135004160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (5/32 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (19/64 : ℝ) (13/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e3 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
