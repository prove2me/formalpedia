-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_157286400_r461373440_508559360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:08:55.894539+00:00
-- url     : https://prove2.me/submissions/b6961828-4df0-4937-b16f-8f9e5d2fb01b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 3/16]`, `ρ ∈ [11/20, 97/160]` by 17 cells of the computing
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
theorem cell0 : cellOK 146800640 149422080 461373440 473169920 ⟨⟨237380642860, 237380642870⟩, ⟨225364559844, 249712521733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 149422080 152043520 461373440 473169920 ⟨⟨234141213581, 234141213586⟩, ⟨222262024846, 246332685034⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 146800640 149422080 473169920 484966400 ⟨⟨242431283509, 242431283520⟩, ⟨230358794018, 254816057347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 149422080 152043520 473169920 484966400 ⟨⟨239145550697, 239145550702⟩, ⟨227209107341, 251390959870⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 152043520 154664960 461373440 473169920 ⟨⟨230939154884, 230939154894⟩, ⟨219194488369, 242992631802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 154664960 157286400 461373440 467271680 ⟨⟨226541615564, 226541615574⟩, ⟨216965525885, 236324581608⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 154664960 157286400 467271680 473169920 ⟨⟨229003631755, 229003631763⟩, ⟨219399453895, 238813875878⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 152043520 154664960 473169920 484966400 ⟨⟨235896918107, 235896918117⟩, ⟨224094215423, 248005301561⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 154664960 157286400 473169920 484966400 ⟨⟨232684386691, 232684386701⟩, ⟨221013181260, 244658021678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 146800640 149422080 484966400 496762880 ⟨⟨247453768853, 247453768863⟩, ⟨235325588247, 259890712636⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 149422080 152043520 484966400 496762880 ⟨⟨244122589950, 244122589954⟩, ⟨232129588594, 256421228042⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 146800640 149422080 496762880 508559360 ⟨⟨252448997525, 252448997536⟩, ⟨240265810872, 264937416468⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 149422080 152043520 496762880 508559360 ⟨⟨249073193880, 249073193886⟩, ⟨237024302237, 261424380983⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 152043520 154664960 484966400 496762880 ⟨⟨240828223721, 240828223732⟩, ⟨228968162230, 252990821918⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 154664960 157286400 484966400 496762880 ⟨⟨237569688673, 237569688683⟩, ⟨225840386809, 249598454223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 152043520 154664960 496762880 508559360 ⟨⟨245733899418, 245733899427⟩, ⟨233817128915, 257950048143⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 154664960 157286400 496762880 508559360 ⟨⟨242430150159, 242430150169⟩, ⟨230643383271, 254513398469⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 157286400 461373440 508559360 t = true :=
  ⟨_, (join_sr (m := 484966400) (by decide) (join_su (m := 152043520) (by decide) (join_sr (m := 473169920) (by decide) (join_su (m := 149422080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 149422080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 473169920) (by decide) (join_su (m := 154664960) (by decide) (leaf_ok cell4) (join_sr (m := 467271680) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 154664960) (by decide) (leaf_ok cell7) (leaf_ok cell8)))) (join_su (m := 152043520) (by decide) (join_sr (m := 496762880) (by decide) (join_su (m := 149422080) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (join_su (m := 149422080) (by decide) (leaf_ok cell11) (leaf_ok cell12))) (join_sr (m := 496762880) (by decide) (join_su (m := 154664960) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_su (m := 154664960) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (11/20 : ℝ) (97/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((461373440 : ℤ) : ℝ) / (D : ℝ)) = (11/20 : ℝ) := by norm_num [D]
  have e3 : (((508559360 : ℤ) : ℝ) / (D : ℝ)) = (97/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
