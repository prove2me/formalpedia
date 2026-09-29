-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u41943040_46137344_r99287040_111411200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:43:16.223099+00:00
-- url     : https://prove2.me/submissions/b122bf0b-5a59-43a4-b94e-0b6a59360ad3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/20, 11/200]`, `ρ ∈ [303/2560, 17/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 41943040 42991616 99287040 102318080 ⟨⟨151596102603, 151596102617⟩, ⟨143198022474, 160242461978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 41943040 42991616 102318080 105349120 ⟨⟨155048493651, 155048493665⟩, ⟨146654265750, 163687326758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 42991616 44040192 99287040 102318080 ⟨⟨149554493242, 149554493260⟩, ⟨141291271655, 158059220113⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 42991616 44040192 102318080 105349120 ⟨⟨152981384654, 152981384668⟩, ⟨144720871612, 161479915900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 41943040 42991616 105349120 108380160 ⟨⟨158457977797, 158457977815⟩, ⟨150068217618, 167088737946⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 41943040 42991616 108380160 111411200 ⟨⟨161825740079, 161825740097⟩, ⟨153441024386, 170447917913⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 42991616 44040192 105349120 108380160 ⟨⟨156366416436, 156366416454⟩, ⟨148109223620, 164858203677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 42991616 44040192 108380160 111411200 ⟨⟨159710726518, 159710726535⟩, ⟨151457428375, 168195257388⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 44040192 45088768 99287040 102318080 ⟨⟨147567161176, 147567161193⟩, ⟨139434279755, 155935062793⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 44040192 45088768 102318080 105349120 ⟨⟨150968616644, 150968616658⟩, ⟨142837380306, 159331561421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 45088768 46137344 99287040 102318080 ⟨⟨145631792674, 145631792687⟩, ⟨137624956890, 153867436009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 45088768 46137344 102318080 105349120 ⟨⟨149007895692, 149007895705⟩, ⟨141001715761, 157239735976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 44040192 45088768 105349120 108380160 ⟨⟨154329230512, 154329230529⟩, ⟨146200246011, 162686669965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 44040192 45088768 108380160 111411200 ⟨⟨157650095761, 157650095778⟩, ⟨149523934067, 166001516133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 45088768 46137344 105349120 108380160 ⟨⟨152344146640, 152344146653⟩, ⟨144339223434, 160571636667⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 45088768 46137344 108380160 111411200 ⟨⟨155641595610, 155641595627⟩, ⟨147638495634, 163864221633⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 41943040 46137344 99287040 111411200 t = true :=
  ⟨_, (join_su (m := 44040192) (by decide) (join_sr (m := 105349120) (by decide) (join_su (m := 42991616) (by decide) (join_sr (m := 102318080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 102318080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 42991616) (by decide) (join_sr (m := 108380160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 108380160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 105349120) (by decide) (join_su (m := 45088768) (by decide) (join_sr (m := 102318080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 102318080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 45088768) (by decide) (join_sr (m := 108380160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 108380160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/20 : ℝ) (11/200 : ℝ) →
    rho ∈ Set.Icc (303/2560 : ℝ) (17/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e1 : (((46137344 : ℤ) : ℝ) / (D : ℝ)) = (11/200 : ℝ) := by norm_num [D]
  have e2 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  have e3 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
