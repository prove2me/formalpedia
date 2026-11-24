-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.exists_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:47:25.448901+00:00
-- url     : https://prove2.me/submissions/a7f0655c-73cb-4b83-b23a-238b266bc071

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_Branch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace Branch
private theorem le_iff_lt_colHeight_of_antitone {n : ℕ} {κ : Fin n → ℤ} (h : Antitone κ) (c : ℤ) (i : Fin n) :
    c ≤ κ i ↔ i.val < colHeight κ c := by
  unfold colHeight
  constructor
  · intro hc
    have hsub : Finset.Iic i ⊆ univ.filter fun m => c ≤ κ m := by
      intro m hm
      rw [Finset.mem_Iic] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact le_trans hc (h hm)
    have h1 := Finset.card_le_card hsub
    rw [Fin.card_Iic] at h1
    omega
  · intro hi
    by_contra hc
    have hsub : (univ.filter fun m => c ≤ κ m) ⊆ Finset.Iio i := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      rw [Finset.mem_Iio]
      by_contra hmi
      push_neg at hmi
      exact hc (le_trans hm (h hmi))
    have h1 := Finset.card_le_card hsub
    rw [Fin.card_Iio] at h1
    omega
private theorem card_filter_val_lt_eq {n k : ℕ} (hk : k ≤ n) : (univ.filter fun m : Fin n => m.val < k).card = k := by
  have e : (univ.filter fun m : Fin n => m.val < k).map Fin.valEmbedding = Finset.range k := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact hm
    · intro hj
      exact ⟨⟨j, by omega⟩, hj, rfl⟩
  have h1 := congrArg Finset.card e
  rw [Finset.card_map, Finset.card_range] at h1
  exact h1
end Branch
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch
theorem _root_.solution {n : ℕ} {μ : Fin (n + 1) → ℤ} (hμ : Antitone μ) (h : ℤ → ℕ)
    (hanti : ∀ c, h (c + 1) ≤ h c) (h1 : ∀ c, h c ≤ colHeight μ c) (h2 : ∀ c, colHeight μ c ≤ h c + 1)
    (h3 : ∀ c, h c ≤ n) : ∃ κ ∈ gtBox μ, ∀ c, h c = colHeight κ c := by
  have hA : Antitone h := antitone_int_of_succ_le hanti
  have hlo : ∀ i : Fin n, i.val < h (μ i.succ) := by
    intro i
    have h4 := (le_iff_lt_colHeight_of_antitone hμ (μ i.succ) i.succ).1 le_rfl
    have h5 := h2 (μ i.succ)
    rw [Fin.val_succ] at h4
    omega
  have hhi : ∀ (i : Fin n) (c : ℤ), i.val < h c → c ≤ μ i.castSucc := by
    intro i c hic
    by_contra hc
    have h4 : ¬ (i.castSucc).val < colHeight μ c := fun h' => hc ((le_iff_lt_colHeight_of_antitone hμ c i.castSucc).2 h')
    rw [Fin.coe_castSucc] at h4
    have h5 := h1 c
    omega
  have hne : ∀ i : Fin n, ((Finset.Icc (μ i.succ) (μ i.castSucc)).filter fun c => i.val < h c).Nonempty :=
    fun i => ⟨μ i.succ, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨le_rfl, hhi i _ (hlo i)⟩, hlo i⟩⟩
  let κ : Fin n → ℤ := fun i => ((Finset.Icc (μ i.succ) (μ i.castSucc)).filter fun c => i.val < h c).max' (hne i)
  have hκmem : ∀ i, κ i ∈ (Finset.Icc (μ i.succ) (μ i.castSucc)).filter fun c => i.val < h c :=
    fun i => Finset.max'_mem _ _
  have hkey : ∀ (i : Fin n) (c : ℤ), c ≤ κ i ↔ i.val < h c := by
    intro i c
    constructor
    · intro hc
      have hm := (Finset.mem_filter.1 (hκmem i)).2
      exact lt_of_lt_of_le hm (hA hc)
    · intro hic
      by_cases hc : μ i.succ ≤ c
      · exact Finset.le_max' _ c (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hc, hhi i c hic⟩, hic⟩)
      · push_neg at hc
        exact le_trans hc.le (Finset.mem_Icc.1 (Finset.mem_filter.1 (hκmem i)).1).1
  refine ⟨κ, ?_, ?_⟩
  · rw [mem_gtBox]
    intro i
    exact Finset.mem_Icc.1 (Finset.mem_filter.1 (hκmem i)).1
  · intro c
    unfold colHeight
    have hfe : (univ.filter fun m => c ≤ κ m) = univ.filter fun m : Fin n => m.val < h c := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hkey m c
    rw [hfe]
    exact (card_filter_val_lt_eq (h3 c)).symm
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch
