-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u141557760_144179200_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:10:02.280637+00:00
-- url     : https://prove2.me/submissions/b8a0d4f7-9e43-4add-aab5-1bd7a1e4f958

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [27/160, 11/64]`, `ρ ∈ [137/1280, 73/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 141557760 142213120 89784320 91258880 ⟨⟨56487745752, 56487745758⟩, ⟨54488214381, 58504727207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 141557760 142213120 91258880 92733440 ⟨⟨57357516390, 57357516396⟩, ⟨55354940679, 59377531582⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 142213120 142868480 89784320 91258880 ⟨⟨56227575248, 56227575249⟩, ⟨54235020161, 58237468286⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 142213120 142868480 91258880 92733440 ⟨⟨57093732096, 57093732100⟩, ⟨55098142439, 59106649440⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 141557760 142213120 92733440 94208000 ⟨⟨58225833730, 58225833739⟩, ⟨56220224520, 60248871759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 141557760 142213120 94208000 95682560 ⟨⟨59092704681, 59092704689⟩, ⟨57084072740, 61118754710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 142213120 142868480 92733440 94208000 ⟨⟨57958452788, 57958452792⟩, ⟨55959839234, 59974383703⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 142213120 142868480 94208000 95682560 ⟨⟨58821744112, 58821744115⟩, ⟨56820117260, 60840677928⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 142868480 143523840 89784320 91258880 ⟨⟨55968989803, 55968989809⟩, ⟨53983354632, 57971852036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 142868480 143523840 91258880 92733440 ⟨⟨56831550345, 56831550351⟩, ⟨54842890357, 58837427458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 143523840 144179200 89784320 91258880 ⟨⟨55711971764, 55711971771⟩, ⟨53733200824, 57707860084⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 143523840 144179200 91258880 92733440 ⟨⟨56570953324, 56570953332⟩, ⟨54589167310, 58569847107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 142868480 143523840 92733440 94208000 ⟨⟨57692691657, 57692691663⟩, ⟨55701017361, 59701573080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 142868480 143523840 94208000 95682560 ⟨⟨58552420410, 58552420417⟩, ⟨56557742247, 60564295639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 143523840 144179200 92733440 94208000 ⟨⟨57428532373, 57428532379⟩, ⟨55443741628, 59430421211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 143523840 144179200 94208000 95682560 ⟨⟨58284715467, 58284715473⟩, ⟨56296930276, 60289589016⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 141557760 144179200 89784320 95682560 t = true :=
  ⟨_, (join_su (m := 142868480) (by decide) (join_sr (m := 92733440) (by decide) (join_su (m := 142213120) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 91258880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 142213120) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 94208000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 92733440) (by decide) (join_su (m := 143523840) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 91258880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 143523840) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 94208000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (27/160 : ℝ) (11/64 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e1 : (((144179200 : ℤ) : ℝ) / (D : ℝ)) = (11/64 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
