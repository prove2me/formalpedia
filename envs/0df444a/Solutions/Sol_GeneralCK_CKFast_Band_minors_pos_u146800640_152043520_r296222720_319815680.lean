-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_152043520_r296222720_319815680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:59:34.703663+00:00
-- url     : https://prove2.me/submissions/ca64fb60-80c2-4461-a708-d722670e85cf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 29/160]`, `ρ ∈ [113/320, 61/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 148111360 296222720 302120960 ⟨⟨162368163694, 162368163698⟩, ⟨156747612307, 168080317156⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 148111360 149422080 296222720 302120960 ⟨⟨161128041658, 161128041668⟩, ⟨155544798689, 166802052467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 146800640 148111360 302120960 308019200 ⟨⟨165165423697, 165165423701⟩, ⟨159527310634, 170894713755⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 148111360 149422080 302120960 308019200 ⟨⟨163909290983, 163909290992⟩, ⟨158308431157, 169600508604⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 149422080 150732800 296222720 302120960 ⟨⟨159897749641, 159897749650⟩, ⟨154351380464, 165534063957⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 150732800 152043520 296222720 302120960 ⟨⟨158677126809, 158677126819⟩, ⟨153167204611, 164276182777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 149422080 150732800 302120960 308019200 ⟨⟨162663010458, 162663010467⟩, ⟨157098973737, 168316596910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 150732800 152043520 302120960 308019200 ⟨⟨161426421994, 161426422004⟩, ⟨155898785911, 167042810691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 146800640 148111360 308019200 313917440 ⟨⟨167951297218, 167951297222⟩, ⟨162295794244, 173697551132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 148111360 149422080 308019200 313917440 ⟨⟨166679360118, 166679360127⟩, ⟨161061051846, 172387615072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 146800640 148111360 313917440 319815680 ⟨⟨170725966511, 170725966516⟩, ⟨165053241618, 176489015356⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 148111360 149422080 313917440 319815680 ⟨⟨169438426751, 169438426761⟩, ⟨163802834784, 175163553260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 149422080 150732800 308019200 313917440 ⟨⟨165417294228, 165417294236⟩, ⟨159835755044, 171087986584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 150732800 152043520 308019200 313917440 ⟨⟨164164940166, 164164940175⟩, ⟨158619751976, 169798498582⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 149422080 150732800 313917440 319815680 ⟨⟨168160774182, 168160774192⟩, ⟨162561894070, 173848409790⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 150732800 152043520 313917440 319815680 ⟨⟨166892850208, 166892850217⟩, ⟨161330268255, 172543418801⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 152043520 296222720 319815680 t = true :=
  ⟨_, (join_sr (m := 308019200) (by decide) (join_su (m := 149422080) (by decide) (join_sr (m := 302120960) (by decide) (join_su (m := 148111360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 148111360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 302120960) (by decide) (join_su (m := 150732800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 150732800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 149422080) (by decide) (join_sr (m := 313917440) (by decide) (join_su (m := 148111360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 148111360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 313917440) (by decide) (join_su (m := 150732800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 150732800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (29/160 : ℝ) →
    rho ∈ Set.Icc (113/320 : ℝ) (61/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e2 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  have e3 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
