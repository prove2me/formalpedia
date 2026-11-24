-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_ph_type
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:50:26.181035+00:00
-- url     : https://prove2.me/submissions/06571a4a-6f2c-47b6-9dfc-f5aa04869748

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationTypeIntersection
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_typeSum_mono
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_phQ_single
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_A_can
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_phQ_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_phQ_top
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_low_minus
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_domLE_antisymm
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_domLE_refl
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_domLE_trans
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_supp_in
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_gen
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_vec_can_high
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hA : LemmaA) {M : GLMod n} (CF : ColFam M) : ∀ (N : ℕ) (j : CF.J),
    (by classical exact (univ.filter fun j' => DomLE (CF.mu j') (CF.mu j)).card) ≤ N →
    ∀ w, qd_phQ CF j w ∈ typeSum M (qd_low (CF.mu j)) := by
  classical
  intro N
  induction N with
  | zero =>
    intro j hj
    exfalso
    have : j ∈ univ.filter fun j' => DomLE (CF.mu j') (CF.mu j) := by simp [qb_domLE_refl]
    have := Finset.card_pos.2 ⟨j, this⟩
    omega
  | succ N ih =>
    intro j hj w
    obtain ⟨w', hw', he⟩ := qd_gen (CF.mu j) w
    have hsplit : qd_phQ CF j w = qd_phQ CF j w' + qd_phQ CF j (w - w') := by
      rw [← map_add, add_sub_cancel]
    rw [hsplit]
    apply Submodule.add_mem
    · have : Submodule.span ℚ (Set.range (qd_gcan (CF.mu j))) ≤
          (typeSum M (qd_low (CF.mu j))).comap (qd_phQ CF j) := by
        rw [Submodule.span_le]
        rintro _ ⟨g, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, ← qd_A_can]
        exact Submodule.subset_span ⟨CF.mu j, ⟨CF.dom j, qb_domLE_refl _⟩, _, qd_vec_can_high CF ℚ j, g, rfl⟩
      exact this hw'
    · have hv : qd_Lam (CF.mu j) (w - w') = 0 := by rw [map_sub, he, sub_self]
      obtain ⟨a, ha⟩ : ∃ a : qb_Idx CF → ℚ, ∑ y, a y • qb_vecF CF ℚ y = qd_phQ CF j (w - w') := by
        have : qd_phQ CF j (w - w') ∈ Submodule.span ℚ (Set.range (qb_vecF CF ℚ)) := by
          rw [(qb_basisR hA CF ℚ).2]; trivial
        exact (Submodule.mem_span_range_iff_exists_fun ℚ).1 this
      have hs := qb_supp_in hA CF ℚ a _ (qd_low_minus (CF.mu j)) (by
        intro nu hnu hnot
        rw [ha]
        by_cases h : nu = CF.mu j
        · rw [h]; exact qd_ev_phQ_top CF j _ hv
        · exact qd_ev_phQ_zero CF j nu (fun hd => hnot ⟨⟨hnu, hd⟩, h⟩) _)
      rw [← ha]
      refine Submodule.sum_mem _ fun y _ => ?_
      by_cases hy : a y = 0
      · rw [hy, zero_smul]; exact zero_mem _
      · apply Submodule.smul_mem
        have hy' := hs y hy
        have hcard : (univ.filter fun j' => DomLE (CF.mu j') (CF.mu y.1)).card ≤ N := by
          have hlt : (univ.filter fun j' => DomLE (CF.mu j') (CF.mu y.1)) ⊂
              (univ.filter fun j' => DomLE (CF.mu j') (CF.mu j)) := by
            refine (Finset.ssubset_iff_of_subset ?_).2 ⟨j, by simp [qb_domLE_refl], ?_⟩
            · intro j' hj'
              simp only [mem_filter, mem_univ, true_and] at hj' ⊢
              exact qb_domLE_trans hj' hy'.1.2
            · simp only [mem_filter, mem_univ, true_and]
              intro hd
              exact hy'.2 (qb_domLE_antisymm hy'.1.2 hd)
          have := Finset.card_lt_card hlt
          omega
        have h1 := ih y.1 hcard (Pi.single y.2.1 1)
        rw [qd_phQ_single] at h1
        exact qd_typeSum_mono M (show qd_low (CF.mu y.1) ⊆ qd_low (CF.mu j) from
          fun la hla => ⟨hla.1, qb_domLE_trans hla.2 hy'.1.2⟩) h1
end Formalism.InvariantFactorPaths.ColumnFamilies
