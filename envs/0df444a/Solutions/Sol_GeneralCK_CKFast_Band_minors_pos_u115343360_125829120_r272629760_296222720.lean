-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_125829120_r272629760_296222720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:43:02.317677+00:00
-- url     : https://prove2.me/submissions/49dd3094-be17-40f1-9975-d57f045a9150

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 3/20]`, `ρ ∈ [13/40, 113/320]` by 17 cells of the computing
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
theorem cell0 : cellOK 115343360 117964800 272629760 278528000 ⟨⟨181911316098, 181911316107⟩, ⟨171477743866, 192647573469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 115343360 117964800 278528000 284426240 ⟨⟨185161103565, 185161103574⟩, ⟨174696926542, 195925909508⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 117964800 120586240 272629760 278528000 ⟨⟨179006584477, 179006584488⟩, ⟨168721247945, 189588577861⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 117964800 120586240 278528000 284426240 ⟨⟨182221465321, 182221465332⟩, ⟨171904994531, 192832676169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 115343360 117964800 284426240 290324480 ⟨⟨188392253426, 188392253437⟩, ⟨177897924470, 199185158426⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 115343360 117964800 290324480 296222720 ⟨⟨191605126617, 191605126628⟩, ⟨181081085667, 202425694220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 117964800 120586240 284426240 290324480 ⟨⟨185418358572, 185418358583⟩, ⟨175071192109, 196058350045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 117964800 120586240 290324480 296222720 ⟨⟨188597606900, 188597606911⟩, ⟨178220171185, 199265954479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 120586240 123207680 272629760 278528000 ⟨⟨176160286135, 176160286143⟩, ⟨166018919324, 186592480540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 120586240 123207680 278528000 284426240 ⟨⟨179340299941, 179340299950⟩, ⟨169167325070, 189802316979⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 123207680 124518400 272629760 278528000 ⟨⟨174062570227, 174062570238⟩, ⟨167750851126, 180486292696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 124518400 125829120 272629760 278528000 ⟨⟨172681215741, 172681215751⟩, ⟨166416845978, 179056403136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 123207680 125829120 278528000 284426240 ⟨⟨176515404215, 176515404221⟩, ⟨166481893880, 186832441732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 120586240 123207680 284426240 290324480 ⟨⟨182502956437, 182502956445⟩, ⟨172298797766, 192994372190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 120586240 123207680 290324480 296222720 ⟨⟨185648580944, 185648580953⟩, ⟨175413651288, 196168983099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 123207680 125829120 284426240 290324480 ⟨⟨179643859781, 179643859787⟩, ⟨169578729226, 189990855031⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 123207680 125829120 290324480 296222720 ⟨⟨182755877911, 182755877914⟩, ⟨172659526323, 193132430978⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 125829120 272629760 296222720 t = true :=
  ⟨_, (join_su (m := 120586240) (by decide) (join_sr (m := 284426240) (by decide) (join_su (m := 117964800) (by decide) (join_sr (m := 278528000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 278528000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 117964800) (by decide) (join_sr (m := 290324480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 290324480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 284426240) (by decide) (join_su (m := 123207680) (by decide) (join_sr (m := 278528000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 278528000) (by decide) (join_su (m := 124518400) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))) (join_su (m := 123207680) (by decide) (join_sr (m := 290324480) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_sr (m := 290324480) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (13/40 : ℝ) (113/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  have e3 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
