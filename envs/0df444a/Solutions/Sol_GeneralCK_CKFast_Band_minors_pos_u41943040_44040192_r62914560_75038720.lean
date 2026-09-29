-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u41943040_44040192_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:40:33.302607+00:00
-- url     : https://prove2.me/submissions/93d55e71-7a77-47ea-bc75-64d48437b5eb

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/20, 21/400]`, `ρ ∈ [3/40, 229/2560]` by 15 cells of the computing
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
theorem cell0 : cellOK 41943040 42467328 62914560 65945600 ⟨⟨106731953998, 106731954016⟩, ⟨100883967745, 112721566607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 42467328 42991616 62914560 65945600 ⟨⟨105902713156, 105902713169⟩, ⟨100108363072, 111836346674⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 41943040 42467328 65945600 68976640 ⟨⟨110822768722, 110822768740⟩, ⟨104972610518, 116812186809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 42467328 42991616 65945600 68976640 ⟨⟨109971899263, 109971899277⟩, ⟨104175001226, 115905783462⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 42991616 43515904 62914560 65945600 ⟨⟨105086494177, 105086494195⟩, ⟨99344754319, 110965234528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 43515904 44040192 62914560 65945600 ⟨⟨104282971702, 104282971716⟩, ⟨98592845529, 110107873316⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 42991616 43515904 65945600 68976640 ⟨⟨109134217729, 109134217746⟩, ⟨103389571185, 115013634149⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 43515904 44040192 65945600 68976640 ⟨⟨108309398510, 108309398524⟩, ⟨102616023390, 114135382687⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 41943040 42467328 68976640 72007680 ⟨⟨114851390278, 114851390296⟩, ⟨108999988961, 120839732930⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 42467328 42991616 68976640 72007680 ⟨⟨113979853425, 113979853442⟩, ⟨108181323389, 119913118098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 41943040 42991616 72007680 75038720 ⟨⟨118372462431, 118372462445⟩, ⟨109975201018, 127054389876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 42991616 43515904 68976640 72007680 ⟨⟨113121651460, 113121651473⟩, ⟨107375001354, 119000884501⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 43515904 44040192 68976640 72007680 ⟨⟨112276458973, 112276458990⟩, ⟨106580725261, 118102677072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 42991616 43515904 72007680 75038720 ⟨⟨117050692432, 117050692445⟩, ⟨111302883446, 122928940396⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 43515904 44040192 72007680 75038720 ⟨⟨116186004079, 116186004093⟩, ⟨110488745294, 122011663653⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 41943040 44040192 62914560 75038720 t = true :=
  ⟨_, (join_sr (m := 68976640) (by decide) (join_su (m := 42991616) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 42467328) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 42467328) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 65945600) (by decide) (join_su (m := 43515904) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 43515904) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 42991616) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 42467328) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 72007680) (by decide) (join_su (m := 43515904) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 43515904) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/20 : ℝ) (21/400 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e1 : (((44040192 : ℤ) : ℝ) / (D : ℝ)) = (21/400 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
