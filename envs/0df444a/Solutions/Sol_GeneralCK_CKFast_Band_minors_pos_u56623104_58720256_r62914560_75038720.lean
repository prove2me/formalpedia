-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u56623104_58720256_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:59:04.842378+00:00
-- url     : https://prove2.me/submissions/58c8d74d-a96a-4661-b7d8-e9af8874f34d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [27/400, 7/100]`, `ρ ∈ [3/40, 229/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 56623104 57147392 62914560 65945600 ⟨⟨87556479079, 87556479094⟩, ⟨82900301536, 92306039651⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 57147392 57671680 62914560 65945600 ⟨⟨86997238333, 86997238344⟩, ⟨82374284596, 91712349508⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 56623104 57147392 65945600 68976640 ⟨⟨91102045278, 91102045292⟩, ⟨86437737510, 95858624478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 57147392 57671680 65945600 68976640 ⟨⟨90525501447, 90525501458⟩, ⟨85894321351, 95247754330⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 57671680 58195968 62914560 65945600 ⟨⟨86444914385, 86444914399⟩, ⟨81854687275, 91126098304⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 58195968 58720256 62914560 65945600 ⟨⟨85899369560, 85899369571⟩, ⟨81341383151, 90547136409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 57671680 58195968 65945600 68976640 ⟨⟨89956011401, 89956011415⟩, ⟨85357466812, 94644454293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 58195968 58720256 65945600 68976640 ⟨⟨89393436119, 89393436129⟩, ⟨84827045918, 94048573622⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 56623104 57147392 68976640 72007680 ⟨⟨94606397803, 94606397817⟩, ⟨89934570004, 99369399590⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 57147392 57671680 68976640 72007680 ⟨⟨94013117044, 94013117055⟩, ⟨89374311430, 98741924380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 56623104 57147392 72007680 75038720 ⟨⟨98070577370, 98070577381⟩, ⟨93391810670, 102839434729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 57147392 57671680 72007680 75038720 ⟨⟨97461103566, 97461103577⟩, ⟨92815244943, 102195906395⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 57671680 58195968 68976640 72007680 ⟨⟨93427017135, 93427017149⟩, ⟨88820746690, 98122140411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 58195968 58720256 68976640 72007680 ⟨⟨92847957923, 92847957934⟩, ⟨88273746487, 97509896041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 57671680 58195968 72007680 75038720 ⟨⟨96858928327, 96858928339⟩, ⟨92245496044, 101560180984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 58195968 58720256 72007680 75038720 ⟨⟨96263910568, 96263910579⟩, ⟨91682433538, 100932106155⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 56623104 58720256 62914560 75038720 t = true :=
  ⟨_, (join_sr (m := 68976640) (by decide) (join_su (m := 57671680) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 57147392) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 57147392) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 65945600) (by decide) (join_su (m := 58195968) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 58195968) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 57671680) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 57147392) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 57147392) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 72007680) (by decide) (join_su (m := 58195968) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 58195968) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (27/400 : ℝ) (7/100 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((56623104 : ℤ) : ℝ) / (D : ℝ)) = (27/400 : ℝ) := by norm_num [D]
  have e1 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
