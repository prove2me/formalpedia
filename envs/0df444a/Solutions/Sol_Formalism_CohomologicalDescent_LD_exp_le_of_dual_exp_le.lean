-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.exp_le_of_dual_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:37:55.6858+00:00
-- url     : https://prove2.me/submissions/e7302f4d-451d-46c7-a550-4b8386c7eb01

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dualWtSpec
import Theorems.Thm_Formalism_CohomologicalDescent_LD_genericDet_pow_ne_zero
import Theorems.Thm_Formalism_CohomologicalDescent_LD_weighted_homog_is_homogeneous
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dual_weight_total
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dominance_of_nabla_weight
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (hN : NablaDual) (hW : WeylDual) (hT : DualWeight) (hC : CofCof) (l r M : ℕ) (ν μ : Fin r → ℕ)
    (e : ℕ) (hl : l.Prime) (hν : Antitone ν) (hνM : ∀ a, ν a ≤ M) (hμM : ∀ a, μ a ≤ M)
    (h : ExpLe l r (dualWt M ν) (dualWt M μ) e) : ExpLe l r ν μ e := by
  intro x hx
  by_cases h0 : x = 0
  · refine ⟨1, (Nat.prime_iff_prime_int.mp hl).not_dvd_one, ?_⟩
    rw [h0, smul_zero]
    exact Submodule.zero_mem _
  obtain ⟨-, htot⟩ := dominance_of_nabla_weight r ν μ hν x hx h0
  obtain ⟨g, hg, hrel⟩ := hN r M ν hν hνM x hx.1
  have hgw := hT r M μ x g hμM hx.2 (by rw [htot]; exact hrel)
  obtain ⟨m, hm, hmem⟩ := h g ⟨hg, hgw⟩
  refine ⟨m, hm, ?_⟩
  obtain ⟨y, hy, hrel'⟩ := hW r M (dualWt M ν) ((dualWtSpec r M ν).2.2 hν) (dualWtSpec r M ν).2.1 _ hmem
  rw [(dualWtSpec r M ν).1 hνM] at hy
  have H2 := congrArg (cofMap r) hrel
  rw [map_mul, map_mul, map_pow, map_pow, (hC r).1] at H2
  have H3 := (hC r).2 (∑ a, ν a) x (htot ▸ weighted_homog_is_homogeneous μ x hx.2)
  rw [map_smul, smul_eq_C_mul] at hrel'
  have hNs := dual_weight_total M ν hνM
  have hE : genDet r ^ (∑ a, dualWt M ν a) * (genDet r ^ (r - 1)) ^ (∑ a, ν a) * genDet r ^ (∑ a, ν a) =
      genDet r ^ M * (genDet r ^ (r - 1)) ^ M * genDet r ^ ((r - 1) * ∑ a, ν a) := by
    rcases r with _ | n
    · have h1 : genDet 0 = 1 := by simp [genDet]
      simp [h1]
    · rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      simp only [Nat.add_sub_cancel]
      rw [add_mul, one_mul] at hNs
      linarith
  have hfin : (genDet r ^ (∑ a, dualWt M ν a) * (genDet r ^ (r - 1)) ^ (∑ a, ν a) * genDet r ^ (∑ a, ν a)) * y =
      (genDet r ^ (∑ a, dualWt M ν a) * (genDet r ^ (r - 1)) ^ (∑ a, ν a) * genDet r ^ (∑ a, ν a)) *
        ((m * (l : ℤ) ^ e) • x) := by
    conv_rhs => rw [hE]
    rw [smul_eq_C_mul]
    linear_combination ((genDet r ^ (r - 1)) ^ (∑ a, ν a) * genDet r ^ (∑ a, ν a)) * hrel' +
      (genDet r ^ (∑ a, ν a) * genDet r ^ M * C (m * (l : ℤ) ^ e)) * H2 +
      (genDet r ^ M * C (m * (l : ℤ) ^ e) * (genDet r ^ (r - 1)) ^ M) * H3
  have hne : genDet r ^ (∑ a, dualWt M ν a) * (genDet r ^ (r - 1)) ^ (∑ a, ν a) * genDet r ^ (∑ a, ν a) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (genericDet_pow_ne_zero r _) (pow_ne_zero _ (genericDet_pow_ne_zero r _))) (genericDet_pow_ne_zero r _)
  rw [← mul_left_cancel₀ hne hfin]
  exact hy
end Formalism.CohomologicalDescent.LD
