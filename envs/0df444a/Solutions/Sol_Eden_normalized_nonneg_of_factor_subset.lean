-- Prove2me | solution 1 for Eden.normalized_nonneg_of_factor_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:07:28.526315+00:00
-- url     : https://prove2.me/submissions/3ca5de1b-2e1f-48a6-a646-853484c50f22

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
import Theorems.Thm_Eden_multiset_descending
import Theorems.Thm_Eden_nonneg_of_card_nonneg
import Theorems.Thm_Eden_normalizedLogSingularValues_antitone
import Theorems.Thm_Eden_normalizedLogSingularValues_eq_descending


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) (s : Finset (Fin 5))
    (hs : ∀ j ∈ s, 0 ≤ Real.log (derivativeFactors c t p j))
    (i : Fin 5) (hi : i.val < s.card) : 0 ≤ normalizedLogSingularValues c t p i := by
  classical
  have hm : Finset.univ.val.map (normalizedLogSingularValues c t p) =
      Finset.univ.val.map (fun j => Real.log (derivativeFactors c t p j) / t) := by
    rw [normalizedLogSingularValues_eq_descending c ht p]
    exact multiset_descending _
  apply nonneg_of_card_nonneg (normalizedLogSingularValues_antitone c ht p) hm i
  apply hi.trans_le
  apply Finset.card_le_card
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, div_nonneg (hs j hj) ht.le⟩
end Eden
