-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u204472320_207093760_r181534720_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:16:52.154018+00:00
-- url     : https://prove2.me/submissions/11fc4d43-6e24-4188-a37b-249d9e4508e0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/160, 79/320]`, `ρ ∈ [277/1280, 147/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 204472320 205127680 181534720 184320000 ⟨⟨72668500496, 72668500499⟩, ⟨70717330146, 74635017869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 205127680 205783040 181534720 184320000 ⟨⟨72361820262, 72361820270⟩, ⟨70416102451, 74322817421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 204472320 205127680 184320000 187105280 ⟨⟨73722741493, 73722741496⟩, ⟨71767247225, 75693584177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 205127680 205783040 184320000 187105280 ⟨⟨73412013053, 73412013060⟩, ⟨71461982152, 75377324935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 205783040 206438400 181534720 184320000 ⟨⟨72056159811, 72056159817⟩, ⟨70115866616, 74011665149⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 206438400 207093760 181534720 184320000 ⟨⟨71751511225, 71751511232⟩, ⟨69816614958, 73701552906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 205783040 206438400 184320000 187105280 ⟨⟨73102313299, 73102313304⟩, ⟨71157717853, 75062122760⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 206438400 207093760 184320000 187105280 ⟨⟨72793634265, 72793634271⟩, ⟨70854446589, 74747969457⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 204472320 205127680 187105280 189890560 ⟨⟨74775610216, 74775610219⟩, ⟨72815800235, 76750769908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 205127680 205783040 187105280 189890560 ⟨⟨74460849183, 74460849190⟩, ⟨72506513252, 76430467629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 204472320 205127680 189890560 192675840 ⟨⟨75827114410, 75827114412⟩, ⟨73862996864, 77806582859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 205127680 205783040 189890560 192675840 ⟨⟨75508336280, 75508336286⟩, ⟨73549703326, 77482253182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 205783040 206438400 187105280 189890560 ⟨⟨74147125584, 74147125591⟩, ⟨72198235802, 76111231151⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 206438400 207093760 187105280 189890560 ⟨⟨73834431409, 73834431416⟩, ⟨71890960102, 75793052238⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 205783040 206438400 189890560 192675840 ⟨⟨75190604182, 75190604188⟩, ⟨73237427929, 77158997892⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 206438400 207093760 189890560 192675840 ⟨⟨74873910062, 74873910068⟩, ⟨72926162849, 76836808702⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 204472320 207093760 181534720 192675840 t = true :=
  ⟨_, (join_sr (m := 187105280) (by decide) (join_su (m := 205783040) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 205127680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 205127680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184320000) (by decide) (join_su (m := 206438400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 206438400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 205783040) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 205127680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 205127680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 189890560) (by decide) (join_su (m := 206438400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 206438400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/160 : ℝ) (79/320 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e1 : (((207093760 : ℤ) : ℝ) / (D : ℝ)) = (79/320 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
