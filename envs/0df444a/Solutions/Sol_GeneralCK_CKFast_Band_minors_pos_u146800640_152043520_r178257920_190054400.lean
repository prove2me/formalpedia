-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_152043520_r178257920_190054400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:47:59.255168+00:00
-- url     : https://prove2.me/submissions/c4b4ba55-e687-4859-9032-79925c399173

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 29/160]`, `ρ ∈ [17/80, 29/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 148111360 178257920 181207040 ⟨⟨102949542195, 102949542198⟩, ⟨98753602707, 107209319585⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 146800640 148111360 181207040 184156160 ⟨⟨104488023056, 104488023058⟩, ⟨100282163888, 108757632665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 148111360 149422080 178257920 181207040 ⟨⟨102086533330, 102086533338⟩, ⟨97917834583, 106318396983⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 148111360 149422080 181207040 184156160 ⟨⟨103614278235, 103614278242⟩, ⟨99435682512, 107855956087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 146800640 148111360 184156160 187105280 ⟨⟨106022492771, 106022492775⟩, ⟨101806766701, 110301881202⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 146800640 148111360 187105280 190054400 ⟨⟨107552985332, 107552985336⟩, ⟨103327444546, 111842099786⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 148111360 149422080 184156160 187105280 ⟨⟨105138095445, 105138095452⟩, ⟨100949654158, 109389535461⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 148111360 149422080 187105280 190054400 ⟨⟨106658017953, 106658017962⟩, ⟨102459781947, 110919168677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 149422080 150732800 178257920 181207040 ⟨⟨101232007365, 101232007374⟩, ⟨97090164402, 105436354463⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 149422080 150732800 181207040 184156160 ⟨⟨102749075971, 102749075978⟩, ⟨98597359769, 106963218064⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 150732800 152043520 178257920 181207040 ⟨⟨100385803800, 100385803807⟩, ⟨96270439834, 104563023062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 150732800 152043520 181207040 184156160 ⟨⟨101892255255, 101892255262⟩, ⟨97767042766, 106079249179⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 149422080 150732800 184156160 187105280 ⟨⟨104262298670, 104262298679⟩, ⟨100100759305, 108486185060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 149422080 150732800 187105280 190054400 ⟨⟨105771707488, 105771707496⟩, ⟨101600394484, 110005288031⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 150732800 152043520 184156160 187105280 ⟨⟨103394940965, 103394940972⟩, ⟨99259928719, 107591660164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 150732800 152043520 187105280 190054400 ⟨⟨104893892010, 104893892017⟩, ⟨100749128246, 109100287630⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 152043520 178257920 190054400 t = true :=
  ⟨_, (join_su (m := 149422080) (by decide) (join_sr (m := 184156160) (by decide) (join_su (m := 148111360) (by decide) (join_sr (m := 181207040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 181207040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 148111360) (by decide) (join_sr (m := 187105280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 187105280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 184156160) (by decide) (join_su (m := 150732800) (by decide) (join_sr (m := 181207040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 181207040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 150732800) (by decide) (join_sr (m := 187105280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 187105280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (29/160 : ℝ) →
    rho ∈ Set.Icc (17/80 : ℝ) (29/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e2 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e3 : (((190054400 : ℤ) : ℝ) / (D : ℝ)) = (29/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
