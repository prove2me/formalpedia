-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u60817408_62914560_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:03:37.018207+00:00
-- url     : https://prove2.me/submissions/9ec0e063-1f26-49eb-96f1-849d3296338a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [29/400, 3/40]`, `ρ ∈ [3/40, 229/2560]` by 20 cells of the computing
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
theorem cell0 : cellOK 60817408 61341696 62914560 64430080 ⟨⟨82410161445, 82410161459⟩, ⟨79192543606, 85673158737⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 60817408 61341696 64430080 65945600 ⟨⟨84125004802, 84125004816⟩, ⟨80903524491, 87391641753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 61341696 61865984 62914560 64430080 ⟨⟨81906739596, 81906739606⟩, ⟨78710034371, 85148277307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 61341696 61865984 64430080 65945600 ⟨⟨83613334183, 83613334194⟩, ⟨80412749519, 86858533842⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 60817408 61341696 65945600 68976640 ⟨⟨86679667940, 86679667953⟩, ⟨82267197941, 91175461199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 61341696 61865984 65945600 68976640 ⟨⟨86155860927, 86155860938⟩, ⟨81772873403, 90621149074⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 61865984 62390272 62914560 64430080 ⟨⟨81409197326, 81409197339⟩, ⟨78233106601, 84629584094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 61865984 62390272 64430080 65945600 ⟨⟨83107608453, 83107608464⟩, ⟨79927622528, 86331678096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 62390272 62914560 62914560 64430080 ⟨⟨80917423740, 80917423753⟩, ⟨77761655812, 84116961513⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 62390272 62914560 64430080 65945600 ⟨⟨82607716011, 82607716024⟩, ⟨79448038280, 85810956285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 61865984 62390272 65945600 68976640 ⟨⟨85638092714, 85638092728⟩, ⟨81284175439, 90073307455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 62390272 62914560 65945600 68976640 ⟨⟨85126250737, 85126250747⟩, ⟨80801000216, 89531814532⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 60817408 61341696 68976640 72007680 ⟨⟨90053619299, 90053619313⟩, ⟨85632918847, 94556736277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 61341696 61865984 68976640 72007680 ⟨⟨89514060054, 89514060068⟩, ⟨85122772569, 93986762299⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 60817408 61341696 72007680 75038720 ⟨⟨93391497825, 93391497836⟩, ⟨88963082499, 97901433161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 61341696 61865984 72007680 75038720 ⟨⟨92836660761, 92836660772⟩, ⟨88437581231, 97316279008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 61865984 62390272 68976640 72007680 ⟨⟨88980657572, 88980657583⟩, ⟨84618374560, 93423372467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 62390272 62914560 68976640 72007680 ⟨⟨88453298143, 88453298156⟩, ⟨84119619717, 92866443988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 61865984 62390272 72007680 75038720 ⟨⟨92288090538, 92288090549⟩, ⟨87917942171, 96737814652⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell19 : cellOK 62390272 62914560 72007680 75038720 ⟨⟨91745672474, 91745672484⟩, ⟨87404059088, 96165916496⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 60817408 62914560 62914560 75038720 t = true :=
  ⟨_, (join_sr (m := 68976640) (by decide) (join_su (m := 61865984) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 61341696) (by decide) (join_sr (m := 64430080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 64430080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 61341696) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 65945600) (by decide) (join_su (m := 62390272) (by decide) (join_sr (m := 64430080) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 64430080) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 62390272) (by decide) (leaf_ok cell10) (leaf_ok cell11)))) (join_su (m := 61865984) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 61341696) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 61341696) (by decide) (leaf_ok cell14) (leaf_ok cell15))) (join_sr (m := 72007680) (by decide) (join_su (m := 62390272) (by decide) (leaf_ok cell16) (leaf_ok cell17)) (join_su (m := 62390272) (by decide) (leaf_ok cell18) (leaf_ok cell19)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (29/400 : ℝ) (3/40 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((60817408 : ℤ) : ℝ) / (D : ℝ)) = (29/400 : ℝ) := by norm_num [D]
  have e1 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
