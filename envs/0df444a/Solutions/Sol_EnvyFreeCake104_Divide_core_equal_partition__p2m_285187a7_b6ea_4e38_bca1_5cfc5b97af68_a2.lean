-- Prove2me | solution 1 for EnvyFreeCake104.Divide.core_equal_partition__p2m_285187a7_b6ea_4e38_bca1_5cfc5b97af68_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T06:58:35.881056+00:00
-- url     : https://prove2.me/submissions/efb3cd1e-f1b5-46d4-87cf-a8c117a4c7f0

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
import Theorems.Thm_EnvyFreeCake104_Divide_equalCuts_partition__p2m_7c833f14_cb58_4a57_947b_39a2d0559683_a1
import Theorems.Thm_EnvyFreeCake104_Divide_assign_partition__p2m_7c833f14_cb58_4a57_947b_39a2d0559683_a1
import Theorems.Thm_EnvyFreeCake104_Divide_exec_bind_transfer__p2m_7c833f14_cb58_4a57_947b_39a2d0559683_a1

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 2 ≤ N.card) (c : ι) (hc : c ∈ N) (C : Piece) (hC : C.WF)
    (s : Rec ι) (hs : s.Valid V N) (hCs : s.Aligned C) (o : ChoiceOracle ι) :
    ∃ (P : ι → Piece) (s₁ : Rec ι) (o₁ : ChoiceOracle ι),
      s₁.Valid V N ∧
      (∀ i ∈ N, (P i).WF) ∧
      (∀ i ∈ N, s₁.Aligned (P i)) ∧
      (∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet) ∧
      (⋃ i ∈ N, (P i).toSet) = C.toSet ∧
      (∀ i ∈ N, (V c).value (P i).toSet = (V c).value C.toSet / (N.card : ℝ)) ∧
      ∀ (Y : ι → Piece) (U : Piece) (s₂ : Rec ι) (tr₂ : List (Event ι)),
        exec V o₁ (permute N P) s₁ = some ((Y, U), s₂, tr₂) →
        ∃ tr : List (Event ι),
          exec V o (core N c C) s = some ((Y, U), s₂, tr) ∧
          queryCount tr ≤ (N.card - 1) * (N.card + 1) + queryCount tr₂ := by
  classical
  have hperm : (sortLR C).Perm C := List.mergeSort_perm C _
  have hsortWF : (sortLR C).WF := by
    refine ⟨fun I hI ↦ hC.1 I (hperm.mem_iff.mp hI), ?_⟩
    exact (List.Perm.pairwise_iff (fun h ↦ h.symm) hperm).2 hC.2
  have hsortAligned : s.Aligned (sortLR C) := by
    intro I hI
    exact hCs I (hperm.mem_iff.mp hI)
  have hsortSet : (sortLR C).toSet = C.toSet := by
    ext x
    change (∃ I ∈ sortLR C, x ∈ I.toSet) ↔ (∃ I ∈ C, x ∈ I.toSet)
    simp only [hperm.mem_iff]
  have hnat : N.card - 1 + 1 = N.card := by omega
  have hrec :=
    EnvyFreeCake104.Divide.recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
      V N s hs c hc (sortLR C) hsortWF hsortAligned
  have hw : s.pieceVal c (sortLR C) / (N.card : ℝ) =
      (V c).value (sortLR C).toSet / ((N.card - 1 + 1 : ℕ) : ℝ) := by
    rw [hnat, hrec]
  obtain ⟨ps, s₁, tr₁, hrun, hs₁, hlen, hwf, halign, hdis, hcover, hval, hcost⟩ :=
    EnvyFreeCake104.Divide.equalCuts_partition__p2m_7c833f14_cb58_4a57_947b_39a2d0559683_a1
      V N c hc (N.card - 1) (sortLR C) hsortWF s hs hsortAligned o
  rw [← hw] at hrun
  have hlen' : ps.length = N.card := hlen.trans hnat
  have hval' : ∀ P ∈ ps,
      (V c).value P.toSet = (V c).value C.toSet / (N.card : ℝ) := by
    simpa only [hnat, hsortSet] using hval
  obtain ⟨hPwf, hPalign, hPdis, hPcover, hPval⟩ :=
    EnvyFreeCake104.Divide.assign_partition__p2m_7c833f14_cb58_4a57_947b_39a2d0559683_a1
      N ps hlen' s₁ (V c) ((V c).value C.toSet / (N.card : ℝ)) C.toSet
      hwf halign hdis (hcover.trans hsortSet) hval'
  obtain ⟨o₁, hlift⟩ :=
    EnvyFreeCake104.Divide.exec_bind_transfer__p2m_7c833f14_cb58_4a57_947b_39a2d0559683_a1
      V o (equalCuts N c (s.pieceVal c (sortLR C) / (N.card : ℝ))
        (N.card - 1) (sortLR C))
      (fun pieces ↦ permute N (assign N.toList pieces)) s ps s₁ tr₁ hrun
  refine ⟨assign N.toList ps, s₁, o₁, hs₁, hPwf, hPalign, hPdis, hPcover, hPval, ?_⟩
  intro Y U s₂ tr₂ hcont
  obtain ⟨tr, htr, hcount⟩ := hlift (Y, U) s₂ tr₂ hcont
  refine ⟨tr, ?_, ?_⟩
  · exact htr
  · rw [hcount]
    exact Nat.add_le_add_right hcost _
