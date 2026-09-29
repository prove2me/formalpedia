-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u131072000_133693440_r107479040_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:07:43.610869+00:00
-- url     : https://prove2.me/submissions/4b95bcec-572a-4d66-a2ac-55ec6b010ae0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [5/32, 51/320]`, `ρ ∈ [41/320, 91/640]` by 19 cells of the computing
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
theorem cell0 : cellOK 131072000 131727360 107479040 110428160 ⟨⟨72383648670, 72383648677⟩, ⟨69655495106, 75142740600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 131727360 132382720 107479040 108953600 ⟨⟨71594842210, 71594842217⟩, ⟨69445971391, 73762803980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 131727360 132382720 108953600 110428160 ⟨⟨72500749506, 72500749514⟩, ⟨70348844536, 74671728128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 131072000 131727360 110428160 113377280 ⟨⟨74199506600, 74199506607⟩, ⟨71464436837, 76965435932⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 131727360 132382720 110428160 113377280 ⟨⟨73856548434, 73856548441⟩, ⟨71132645080, 76611089213⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 132382720 133038080 107479040 108953600 ⟨⟨71263166804, 71263166809⟩, ⟨69122314435, 73422982465⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 132382720 133038080 108953600 110428160 ⟨⟨72165417015, 72165417020⟩, ⟨70021537971, 74328242504⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 133038080 133693440 107479040 108953600 ⟨⟨70933599863, 70933599870⟩, ⟨68800697868, 73085338945⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 133038080 133693440 108953600 110428160 ⟨⟨71832210017, 71832210026⟩, ⟨69696288866, 73986951857⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 132382720 133038080 110428160 113377280 ⟨⟨73515765797, 73515765802⟩, ⟨70802936462, 76259012940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 133038080 133693440 110428160 113377280 ⟨⟨73177133764, 73177133771⟩, ⟨70475287251, 75909180968⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 131072000 131727360 113377280 116326400 ⟨⟨76008800291, 76008800300⟩, ⟨73266881111, 78781500064⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 131727360 132382720 113377280 116326400 ⟨⟨75658607827, 75658607836⟩, ⟨72927870952, 78419904863⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 131072000 131727360 116326400 119275520 ⟨⟨77811596133, 77811596142⟩, ⟨75062893314, 80591000393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 131727360 132382720 116326400 119275520 ⟨⟨77454244135, 77454244144⟩, ⟨74716738572, 80222232414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 132382720 133038080 113377280 116326400 ⟨⟨75310623836, 75310623841⟩, ⟨72590977026, 78060612869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 133038080 133693440 113377280 116326400 ⟨⟨74964823132, 74964823139⟩, ⟨72256175332, 77703597683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 132382720 133038080 116326400 119275520 ⟨⟨77099132648, 77099132653⟩, ⟨74372732267, 79855799486⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 133038080 133693440 116326400 119275520 ⟨⟨76746236238, 76746236247⟩, ⟨74030850142, 79491674964⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 131072000 133693440 107479040 119275520 t = true :=
  ⟨_, (join_sr (m := 113377280) (by decide) (join_su (m := 132382720) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 131727360) (by decide) (leaf_ok cell0) (join_sr (m := 108953600) (by decide) (leaf_ok cell1) (leaf_ok cell2))) (join_su (m := 131727360) (by decide) (leaf_ok cell3) (leaf_ok cell4))) (join_sr (m := 110428160) (by decide) (join_su (m := 133038080) (by decide) (join_sr (m := 108953600) (by decide) (leaf_ok cell5) (leaf_ok cell6)) (join_sr (m := 108953600) (by decide) (leaf_ok cell7) (leaf_ok cell8))) (join_su (m := 133038080) (by decide) (leaf_ok cell9) (leaf_ok cell10)))) (join_su (m := 132382720) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 131727360) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 131727360) (by decide) (leaf_ok cell13) (leaf_ok cell14))) (join_sr (m := 116326400) (by decide) (join_su (m := 133038080) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_su (m := 133038080) (by decide) (leaf_ok cell17) (leaf_ok cell18)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (5/32 : ℝ) (51/320 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e1 : (((133693440 : ℤ) : ℝ) / (D : ℝ)) = (51/320 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
