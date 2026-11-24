-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.separated_cutoff_sum_of_disjoint_polydiscs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:17.918831+00:00
-- url     : https://prove2.me/submissions/469ebc7f-bbd9-409f-bc16-5c6b7f09387c

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_separated_sum_le_prod_integrals
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_E3cut_nonneg_of_nonneg_of_nonneg
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_cutoff_comparison_nearby

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hd : SeparatedPolydiscsDisjoint) (hi : CutoffIntegralFormula) : SeparatedCutoffSum := by
  intro ι _ ro K abelian₂ S hro hK hLam hS
  have hLpos : ∀ v, 0 < 3 / 2 * max ro (abelian₂ v) := fun v => by
    have : 0 < max ro (abelian₂ v) := lt_of_lt_of_le hro (le_max_left _ _)
    positivity
  have h := separated_sum_le_prod_integrals hd ro S hro hS (fun v z => TruncationCutoff K (abelian₂ v) ‖z‖)
    (fun v x => TruncationCutoff K (3 / 2 * max ro (abelian₂ v)) ‖x‖)
    (fun v z => E3cut_nonneg_of_nonneg_of_nonneg _ _ _ (hLpos v).le (norm_nonneg z))
    (fun v z => E3cut_nonneg_of_nonneg_of_nonneg _ _ _ (hLam v).le (norm_nonneg z))
    (fun v => (hi K _ hK (hLpos v)).1)
    (fun v D x hx => cutoff_comparison_nearby K ro (abelian₂ v) (by linarith) hro (hLam v) D x hx)
  have hV : 0 < (π * (ro / 2) ^ 2) ^ Fintype.card ι := by positivity
  rw [← le_div_iff₀ hV] at h
  refine le_trans h ?_
  rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_div_distrib]
  apply Finset.prod_le_prod
  · intro v _
    rw [(hi K _ hK (hLpos v)).2]
    have : 0 < K - 2 := by linarith
    have := hLpos v
    positivity
  · intro v _
    rw [(hi K _ hK (hLpos v)).2]
    have hK2 : 0 < K - 2 := by linarith
    have hpw : (9 / 4 : ℝ) ≤ (3 / 2 : ℝ) ^ K := by
      have : ((3 / 2 : ℝ)) ^ (2 : ℝ) ≤ (3 / 2 : ℝ) ^ K :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hK.le
      have h2 : ((3 / 2 : ℝ)) ^ (2 : ℝ) = 9 / 4 := by
        rw [Real.rpow_two]; norm_num
      linarith
    have e1 : π * (3 / 2 * max ro (abelian₂ v)) ^ 2 * (K / (K - 2)) / (π * (ro / 2) ^ 2) =
        4 * (9 / 4) * (K / (K - 2)) * (max ro (abelian₂ v)) ^ 2 / ro ^ 2 := by
      field_simp; ring
    rw [e1]
    have hk : 0 ≤ K / (K - 2) := by apply div_nonneg <;> linarith
    gcongr
end Formalism.HermitianLatticeCounting.P
