-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_199229440_r616038400_660602880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:02:03.225242+00:00
-- url     : https://prove2.me/submissions/98a867df-3fc5-4c57-9266-06965fce73a2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 19/80]`, `ρ ∈ [47/64, 63/80]` by 17 cells of the computing
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
theorem cell0 : cellOK 188743680 191365120 616038400 627179520 ⟨⟨244418090650, 244418090656⟩, ⟨233721266779, 255353821047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 191365120 193986560 616038400 627179520 ⟨⟨241072480439, 241072480448⟩, ⟨230475799311, 251906654905⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 188743680 191365120 627179520 638320640 ⟨⟨248294040107, 248294040113⟩, ⟨237541604957, 259284052557⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 191365120 193986560 627179520 638320640 ⟨⟨244908144662, 244908144672⟩, ⟨234255598438, 255796949758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 193986560 196608000 616038400 627179520 ⟨⟨237749402762, 237749402772⟩, ⟨227251769215, 248483106509⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 196608000 199229440 616038400 621608960 ⟨⟨233508301750, 233508301760⟩, ⟨224604305511, 242581653203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 196608000 199229440 621608960 627179520 ⟨⟨235387828537, 235387828546⟩, ⟨226457100317, 244487646754⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 193986560 196608000 627179520 638320640 ⟨⟨241544567787, 241544567797⟩, ⟨230990846762, 252333216484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 196608000 199229440 627179520 638320640 ⟨⟨238202814689, 238202814699⟩, ⟨227746874206, 248892339870⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 188743680 191365120 638320640 649461760 ⟨⟨252160014321, 252160014324⟩, ⟨241352182695, 263204070039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 191365120 193986560 638320640 649461760 ⟨⟨248734164882, 248734164891⟩, ⟨238025958273, 259677371942⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 188743680 191365120 649461760 660602880 ⟨⟨256016315187, 256016315194⟩, ⟨245153294041, 267114183104⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 191365120 193986560 649461760 660602880 ⟨⟨252550831152, 252550831162⟩, ⟨241787161398, 263548218839⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 193986560 196608000 638320640 649461760 ⟨⟨245330413313, 245330413323⟩, ⟨234720799420, 256173788470⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 196608000 199229440 638320640 649461760 ⟨⟨241948272728, 241948272738⟩, ⟨231436237330, 252692815724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 193986560 196608000 649461760 660602880 ⟨⟨249107217905, 249107217915⟩, ⟨238441898654, 260005107999⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 196608000 199229440 649461760 660602880 ⟨⟨245684996459, 245684996469⟩, ⟨235117043929, 256484355604⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 199229440 616038400 660602880 t = true :=
  ⟨_, (join_sr (m := 638320640) (by decide) (join_su (m := 193986560) (by decide) (join_sr (m := 627179520) (by decide) (join_su (m := 191365120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 191365120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 627179520) (by decide) (join_su (m := 196608000) (by decide) (leaf_ok cell4) (join_sr (m := 621608960) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 196608000) (by decide) (leaf_ok cell7) (leaf_ok cell8)))) (join_su (m := 193986560) (by decide) (join_sr (m := 649461760) (by decide) (join_su (m := 191365120) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (join_su (m := 191365120) (by decide) (leaf_ok cell11) (leaf_ok cell12))) (join_sr (m := 649461760) (by decide) (join_su (m := 196608000) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_su (m := 196608000) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (47/64 : ℝ) (63/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((616038400 : ℤ) : ℝ) / (D : ℝ)) = (47/64 : ℝ) := by norm_num [D]
  have e3 : (((660602880 : ℤ) : ℝ) / (D : ℝ)) = (63/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
