-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u62914560_65011712_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:04:04.592+00:00
-- url     : https://prove2.me/submissions/3c05aa5c-2ce5-4752-95e7-6a834d7a4b9b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/40, 31/400]`, `ρ ∈ [3/40, 229/2560]` by 20 cells of the computing
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
theorem cell0 : cellOK 62914560 63438848 62914560 64430080 ⟨⟨80431310769, 80431310780⟩, ⟨77295580168, 83610294988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 62914560 63438848 64430080 65945600 ⟨⟨82113548093, 82113548103⟩, ⟨78973894196, 85296253183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 63438848 63963136 62914560 64430080 ⟨⟨79950753078, 79950753091⟩, ⟨76834780391, 83109472890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 63438848 63963136 64430080 65945600 ⟨⟨81624998668, 81624998682⟩, ⟨78505090258, 84787456522⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 62914560 63438848 65945600 68976640 ⟨⟨84620225258, 84620225272⟩, ⟨80323246518, 88996551577⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 63438848 63963136 65945600 68976640 ⟨⟨84119909305, 84119909316⟩, ⟨79850815615, 88467402893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 63963136 64487424 62914560 64430080 ⟨⟨79475647996, 79475648006⟩, ⟨76379159683, 82614386404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 63963136 64487424 64430080 65945600 ⟨⟨81141964381, 81141964391⟩, ⟨78041528936, 84284456848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 64487424 65011712 62914560 64430080 ⟨⟨79005895408, 79005895421⟩, ⟨75928623667, 82124929459⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 64487424 65011712 64430080 65945600 ⟨⟨80664344433, 80664344446⟩, ⟨77583115132, 83787147451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 63963136 64487424 65945600 68976640 ⟨⟨83625198558, 83625198571⟩, ⟨79383611227, 87944255674⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 64487424 65011712 65945600 68976640 ⟨⟨83135991287, 83135991297⟩, ⟨78921539444, 87426999920⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 62914560 63438848 68976640 72007680 ⟨⟨87931870908, 87931870919⟩, ⟨83626405541, 92315857169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 63438848 63963136 68976640 72007680 ⟨⟨87416267755, 87416267768⟩, ⟨83138632049, 91771495325⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 62914560 63438848 72007680 75038720 ⟨⟨91209294735, 91209294746⟩, ⟨86895828378, 95600464025⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 63438848 63963136 72007680 75038720 ⟨⟨90678848236, 90678848249⟩, ⟨86393148941, 95041339745⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 63963136 64487424 68976640 72007680 ⟨⟨86906383249, 86906383259⟩, ⟨82656201703, 91233244680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 64487424 65011712 68976640 72007680 ⟨⟨86402114530, 86402114543⟩, ⟨82179019351, 90700994252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 63963136 64487424 72007680 75038720 ⟨⟨90154226570, 90154226580⟩, ⟨85895922147, 94488429040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell19 : cellOK 64487424 65011712 72007680 75038720 ⟨⟨89635325907, 89635325918⟩, ⟨85404051738, 93941620110⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 62914560 65011712 62914560 75038720 t = true :=
  ⟨_, (join_sr (m := 68976640) (by decide) (join_su (m := 63963136) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 63438848) (by decide) (join_sr (m := 64430080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 64430080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 63438848) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 65945600) (by decide) (join_su (m := 64487424) (by decide) (join_sr (m := 64430080) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 64430080) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 64487424) (by decide) (leaf_ok cell10) (leaf_ok cell11)))) (join_su (m := 63963136) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 63438848) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 63438848) (by decide) (leaf_ok cell14) (leaf_ok cell15))) (join_sr (m := 72007680) (by decide) (join_su (m := 64487424) (by decide) (leaf_ok cell16) (leaf_ok cell17)) (join_su (m := 64487424) (by decide) (leaf_ok cell18) (leaf_ok cell19)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/40 : ℝ) (31/400 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e1 : (((65011712 : ℤ) : ℝ) / (D : ℝ)) = (31/400 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
