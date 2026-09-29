-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u29360128_33554432_r99287040_111411200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:24:57.727847+00:00
-- url     : https://prove2.me/submissions/cbde7a7c-a102-4879-9dcd-ac2028d96d4f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/200, 1/25]`, `ρ ∈ [303/2560, 17/128]` by 12 cells of the computing
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
theorem cell0 : cellOK 29360128 30408704 99287040 102318080 ⟨⟨181411304585, 181411304606⟩, ⟨170934076533, 192248764756⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 29360128 30408704 102318080 105349120 ⟨⟨185162788540, 185162788557⟩, ⟨174712579745, 195965932419⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 30408704 31457280 99287040 102318080 ⟨⟨178470456762, 178470456784⟩, ⟨168207380986, 189081634036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 30408704 31457280 102318080 105349120 ⟨⟨182198561779, 182198561796⟩, ⟨171959643805, 192778723123⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 29360128 30408704 105349120 111411200 ⟨⟨190681929403, 190681929419⟩, ⟨176415932947, 205586703241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 30408704 31457280 105349120 111411200 ⟨⟨187685306645, 187685306662⟩, ⟨173705643535, 202282790305⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 31457280 32505856 99287040 102318080 ⟨⟨175627421966, 175627421982⟩, ⟨165569494968, 186021949645⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 31457280 32505856 102318080 105349120 ⟨⟨179331648842, 179331648858⟩, ⟨169295239754, 189698206564⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 32505856 33554432 99287040 102318080 ⟨⟨172877005312, 172877005333⟩, ⟨163015782618, 183063914539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 32505856 33554432 102318080 105349120 ⟨⟨176556938118, 176556938135⟩, ⟨166714795583, 186718691345⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 31457280 32505856 105349120 111411200 ⟨⟨184785187835, 184785187852⟩, ⟨171080345853, 199087938622⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 32505856 33554432 105349120 111411200 ⟨⟨181976585270, 181976585291⟩, ⟨168535738347, 195996405409⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 29360128 33554432 99287040 111411200 t = true :=
  ⟨_, (join_su (m := 31457280) (by decide) (join_sr (m := 105349120) (by decide) (join_su (m := 30408704) (by decide) (join_sr (m := 102318080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 102318080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 30408704) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 105349120) (by decide) (join_su (m := 32505856) (by decide) (join_sr (m := 102318080) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 102318080) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 32505856) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/200 : ℝ) (1/25 : ℝ) →
    rho ∈ Set.Icc (303/2560 : ℝ) (17/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((29360128 : ℤ) : ℝ) / (D : ℝ)) = (7/200 : ℝ) := by norm_num [D]
  have e1 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e2 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  have e3 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
