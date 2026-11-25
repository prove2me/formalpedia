-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.harmonic_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:10:56.965501+00:00
-- url     : https://prove2.me/submissions/c3b27079-c4bb-45e7-b51f-ed6e8548b63d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FinTwoNeOneSub
import Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_RF_pderiv_comm__6c5c66fe37bd
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_ConjugatePairPlaceSetting_no_conj_letter
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_lap_one_apply
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution : NormOneHarmonic := by
  intro C _ V d _ T r cc a Orb _ tau J _ X F Z ga n L pl H isX
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker]
  intro τ _ a1 a2
  rw [lap_one_apply]
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
  by_cases hb : b = b'
  · subst hb
    by_cases h : (⟨τ, a1, b⟩ : Letter T r n) ∈ (MvPolynomial.rename (phiL r tau n) (blkProd X F n L pl)).vars
    · have h' : (⟨cc τ, a2, b⟩ : Letter T r n) ∉ (MvPolynomial.rename (phiL r tau n) (blkProd X F n L pl)).vars :=
        fun h2 => H.no_conj_letter τ a1 a2 b h h2
      rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars h', map_zero, smul_zero]
    · rw [pderiv_comm', MvPolynomial.pderiv_eq_zero_of_notMem_vars h, map_zero, smul_zero]
  · rw [Matrix.one_apply_ne hb, zero_smul]
end Formalism.L2.FormalSeriesBounds.RF
