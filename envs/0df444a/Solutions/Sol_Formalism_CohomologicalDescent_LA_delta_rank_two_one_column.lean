-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.delta_rank_two_one_column
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:18:18.958012+00:00
-- url     : https://prove2.me/submissions/c74d7778-fbe3-47de-96eb-f80abd283316

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_weyl_r2n1
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_binForm_apply
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_binForm_single
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_diagBinom_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution : WeylRankTwoOneColumnImage := by
  unfold WeylRankTwoOneColumnImage
  intro R _ hn ν
  rw [la_weyl_r2n1]
  apply le_antisymm
  · rw [la_binLat, Submodule.span_le]
    rintro f ⟨p, q, hpq, rfl⟩
    have hsingle : Formalism.CohomologicalDescent.diagBinom R (ν 0) (Pi.single (⟨q, by omega⟩ : Fin (ν 0 + 1)) 1) =
        Pi.single ⟨q, by omega⟩ ((ν 0).choose q : R) := by
      funext j
      rw [la_diagBinom_apply]
      by_cases hj : j = ⟨q, by omega⟩
      · subst hj
        simp
      · simp [Pi.single_apply, hj]
    refine Submodule.mem_map.mpr ⟨Formalism.CohomologicalDescent.diagBinom R (ν 0) (Pi.single ⟨q, by omega⟩ 1),
      LinearMap.mem_range_self _ _, ?_⟩
    rw [hsingle, la_binForm_single, MvPolynomial.smul_eq_C_mul, map_natCast]
    simp only [Fin.val_mk, ← hpq, Nat.add_sub_cancel]
  · rw [Submodule.map_le_iff_le_comap]
    rintro _ ⟨c, rfl⟩
    rw [Submodule.mem_comap, la_binForm_apply, la_binLat]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have hi := i.isLt
    have hg : ((ν 0).choose i.val : R) • la_xy R (0 : Fin 1) (ν 0 - i.val) i.val ∈
        Submodule.span R {f | ∃ p q, p + q = ν 0 ∧
          f = ((p + q).choose q : MvPolynomial (Fin 2 × Fin 1) R) * la_xy R 0 p q} := by
      rw [MvPolynomial.smul_eq_C_mul, map_natCast]
      exact Submodule.subset_span ⟨ν 0 - i.val, i.val, by omega,
        by rw [show ν 0 - i.val + i.val = ν 0 by omega]⟩
    rw [la_diagBinom_apply, mul_comm ((ν 0).choose i.val : R), mul_smul]
    exact Submodule.smul_mem _ _ hg
end Formalism.CohomologicalDescent.LA
