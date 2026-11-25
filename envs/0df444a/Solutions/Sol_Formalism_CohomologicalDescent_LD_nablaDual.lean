-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.nablaDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:54:24.32586+00:00
-- url     : https://prove2.me/submissions/50d899ed-d075-4a40-966d-aba9a4b7d878

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dualWtSpec
import Theorems.Thm_Formalism_CohomologicalDescent_LD_gen_det_eq_det
import Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_bideterminant
import Theorems.Thm_Formalism_CohomologicalDescent_LD_shape_complement_sum
import Theorems.Thm_Formalism_CohomologicalDescent_LD_shape_total_degree
import Theorems.Thm_Formalism_CohomologicalDescent_LD_det_pow_mul_mem_dual_weyl
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dual_weyl_shift_eq_det_pow_mul
import Theorems.Thm_Formalism_CohomologicalDescent_LD_genericDet_pow_ne_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeyl_of_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_standardMonomialSpan
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : NablaDual := by
  intro r M ν hν hM x hx
  rw [gen_det_eq_det]
  have hνs : Antitone (dualWt M ν) := (dualWtSpec r M ν).2.2 hν
  rw [standardMonomialSpan r r ν hν] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    obtain ⟨g, hg, hg'⟩ := cofactor_bideterminant sz hsz I
    rw [shape_total_degree sz hsz, hshape] at hg'
    have hK : ∀ t : Fin r, (∑ k, initW r (r - sz k)) t + ν (Fin.rev t) = K := by
      intro t
      rw [← hshape]
      exact shape_complement_sum sz t
    rcases le_total K M with hKM | hKM
    · refine ⟨genericDet ℤ r ^ (M - K) * g, dualWeyl_of_eq (det_pow_mul_mem_dual_weyl _ (M - K) hg) ?_, ?_⟩
      · funext t
        have := hK t
        unfold dualWt
        omega
      · rw [mul_left_comm, ← hg', ← mul_assoc, ← pow_add, Nat.sub_add_cancel hKM]
    · have hg2 : g ∈ dualWeyl ℤ r r (fun a => dualWt M ν a + (K - M)) := by
        refine dualWeyl_of_eq hg ?_
        funext t
        have := hK t
        have := hM (Fin.rev t)
        unfold dualWt
        omega
      obtain ⟨g', hg3, rfl⟩ := dual_weyl_shift_eq_det_pow_mul _ hνs (K - M) hg2
      refine ⟨g', hg3, mul_left_cancel₀ (genericDet_pow_ne_zero r (K - M)) ?_⟩
      rw [mul_left_comm, ← hg', ← mul_assoc, ← pow_add, Nat.sub_add_cancel hKM]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨g, hg, hg'⟩ := hx
    obtain ⟨g2, hg2, hg2'⟩ := hy
    exact ⟨g + g2, Submodule.add_mem _ hg hg2, by rw [mul_add, map_add, mul_add, hg', hg2']⟩
  | smul c x _ hx =>
    obtain ⟨g, hg, hg'⟩ := hx
    exact ⟨c • g, Submodule.smul_mem _ c hg, by rw [mul_smul_comm, map_smul, mul_smul_comm, hg']⟩
end Formalism.CohomologicalDescent.LD
