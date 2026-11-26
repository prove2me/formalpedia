-- Prove2me | solution 1 for Eden.finiteTimeDimension_ge_of_nonneg_factor_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:15:29.882479+00:00
-- url     : https://prove2.me/submissions/4e85f316-b5c2-41c5-bde8-76cadc15178e

import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_NeutralDimensionBounds
import Theorems.Thm_Eden_nonneg_of_card_nonneg
import Theorems.Thm_Eden_finiteTimeDimension_eq_kaplanYorke
import Theorems.Thm_Eden_kaplanYorkeIndex_le_dimension
import Theorems.Thm_Eden_le_kaplanYorkeIndex
import Theorems.Thm_Eden_multiset_descending
import Theorems.Thm_Eden_normalizedLogSingularValues_antitone
import Theorems.Thm_Eden_normalizedLogSingularValues_eq_descending


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) {k : ℕ} (hk : k ≤ 5)
    (hcount : k ≤ (Finset.univ.filter
      (fun i : Fin 5 => 0 ≤ Real.log (derivativeFactors c t p i) / t)).card) :
    (k : ℝ) ≤ finiteTimeDimension c t p := by
  classical
  have hm : Finset.univ.val.map (normalizedLogSingularValues c t p) =
      Finset.univ.val.map (fun i => Real.log (derivativeFactors c t p i) / t) := by
    rw [normalizedLogSingularValues_eq_descending c ht p]
    exact multiset_descending _
  have hsum : 0 ≤ spectrumPartialSum (normalizedLogSingularValues c t p) k := by
    apply Finset.sum_nonneg
    intro i hi
    have hi₅ : i < 5 := lt_of_lt_of_le (Finset.mem_range.mp hi) hk
    rw [spectrumEntry, dif_pos hi₅]
    exact nonneg_of_card_nonneg (normalizedLogSingularValues_antitone c ht p)
      hm ⟨i, hi₅⟩ (lt_of_lt_of_le (Finset.mem_range.mp hi) hcount)
  rw [finiteTimeDimension_eq_kaplanYorke c ht p]
  exact (show (k : ℝ) ≤ kaplanYorkeIndex (normalizedLogSingularValues c t p) by
    exact_mod_cast le_kaplanYorkeIndex hk hsum).trans (kaplanYorkeIndex_le_dimension _)
end Eden
