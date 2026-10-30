-- Prove2me | solution 1 for CorrClusterExp.IBR.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:54:51.789209+00:00
-- url     : https://prove2.me/submissions/e125c4ff-096b-47ef-b28e-3f6552267a4f

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting
import Theorems.Thm_CorrClusterExp_IBR_lemma_4_3
import Theorems.Thm_CorrClusterExp_IBR_lemma_4_2

open CorrClusterExp.IBR Matrix Finset

lemma t45_bdd {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    BddAbove ((fun y => y ⬝ᵥ (S *ᵥ y)) '' box w) := by
  have hbox : box w = Set.pi Set.univ (fun i => Set.Icc 0 (w i)) := by
    ext y; simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc]; exact Iff.rfl
  have hc : IsCompact (box w) := by
    rw [hbox]; exact isCompact_univ_pi (fun i => isCompact_Icc)
  apply hc.bddAbove_image
  apply Continuous.continuousOn
  exact Continuous.dotProduct continuous_id (Continuous.matrix_mulVec continuous_const continuous_id)

lemma t45_wc_nonneg {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) : 0 ≤ worstCase S w := by
  unfold worstCase
  apply le_csSup (t45_bdd S w)
  refine ⟨0, fun i => ⟨le_refl _, hw0 i⟩, ?_⟩
  simp

lemma t45_VDP_le_Vk (q : ℝ) (k : ℕ) {n : ℕ} (w : Fin n → ℝ) : VDP q w ≤ Vk q k w := by
  unfold Vk
  have : Nonempty {c : Composition n // KGrouped k c} := by
    refine ⟨⟨Composition.ones n, ?_⟩⟩
    intro h hh
    exact ⟨h * k, by rw [Composition.ones_sizeUpTo]; omega⟩
  apply le_ciInf
  intro c
  unfold VDP
  exact ciInf_le (Finite.bddBelow_range _) c.1

theorem solution (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (n : ℕ) (hn : 0 < n)
    (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w) (hw1 : 0 < w ⟨0, hn⟩) :
    VDP q w / VOPT q w ≤ VDP q w / VLB w ∧
      VDP q w / VLB w ≤ ⨅ k : ℕ+, Vk q k w / VLB w ∧
      ⨅ k : ℕ+, Vk q k w / VLB w ≤ ⨅ k : ℕ+, fq q k * (4 / k + ((k : ℝ) - 1) / k) := by
  have hL := lemma_4_2 q hq0 hq n hn w hw0 hw
  have ha2 : 0 < w ⟨0, hn⟩ ^ 2 := by positivity
  have hLpos : 0 < VLB w := lt_of_lt_of_le ha2 (le_trans (le_max_left _ _) hL.1)
  have hVDP0 : 0 ≤ VDP q w := by
    unfold VDP
    exact Real.iInf_nonneg (fun c => t45_wc_nonneg _ w hw0)
  have hVk0 : ∀ k : ℕ, 0 ≤ Vk q k w := fun k => by
    unfold Vk; exact Real.iInf_nonneg (fun c => t45_wc_nonneg _ w hw0)
  refine ⟨div_le_div_of_nonneg_left hVDP0 hLpos hL.2.1, ?_, ?_⟩
  · apply le_ciInf
    intro k
    exact div_le_div_of_nonneg_right (t45_VDP_le_Vk q k w) hLpos.le
  · apply ciInf_mono
    · exact ⟨0, by rintro _ ⟨k, rfl⟩; exact div_nonneg (hVk0 k) hLpos.le⟩
    · intro k
      have hk : 1 ≤ (k : ℕ) := k.pos
      have h43 := lemma_4_3 q hq0 hq k hk n hn w hw0 hw hw1
      exact le_trans h43.2.1 h43.2.2
