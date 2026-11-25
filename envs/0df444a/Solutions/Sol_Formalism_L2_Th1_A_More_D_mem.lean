-- Prove2me | solution 1 for Formalism.L2.Th1.A.More.D_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:22:34.243812+00:00
-- url     : https://prove2.me/submissions/c3c7a946-201a-4cee-a460-bb99e00e9034

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementM
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open More
open Formalism.L2.Th1.A.More
variable {K : Type u} [Field K] (W : WeierstrassCurve K) (S : Subring K)
namespace Formalism.L2.Th1.A.More
theorem _root_.solution (hw : ∀ n, coeff n (fw W) ∈ S) (f : K⟦X⟧) (hf : ∀ n, coeff n f ∈ S) (n : ℕ) :
    coeff n (D W f) ∈ S := by
  have e1 : D W f = fw W * derivative K f := by
    simp only [D, Derivation.smul_apply, smul_eq_mul]
  rw [e1, PowerSeries.coeff_mul]
  refine Subring.sum_mem S fun p _ => Subring.mul_mem S (hw _) ?_
  rw [PowerSeries.coeff_derivative]
  exact Subring.mul_mem S (hf _) (Subring.add_mem S (natCast_mem S _) (Subring.one_mem S))
end Formalism.L2.Th1.A.More
