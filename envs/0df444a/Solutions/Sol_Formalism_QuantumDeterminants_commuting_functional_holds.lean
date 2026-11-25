-- Prove2me | solution 1 for Formalism.QuantumDeterminants.commuting_functional_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:29:30.955393+00:00
-- url     : https://prove2.me/submissions/e0be7095-f82f-4b93-8611-10f43c5da8a3

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_reg_of_mem
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_opL_on
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_opL_off
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_Dop_opL
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_Dop_comm
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_dco_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Filter
noncomputable section
open Formalism Formalism.QuantumDeterminants
open WirtingerDerivatives
namespace Formalism.QuantumDeterminants
theorem _root_.solution : CommFun := by
  intro m E _ _ l k i j f hf hc
  have hr := reg_of_mem hf
  have hc' : k ≠ l ∨ (holoIdx j ↔ ¬ holoIdx i) := by
    rcases hc with h | h
    · exact Or.inl (Ne.symm h)
    · right
      constructor
      · intro hj hi
        exact (h.mp hi) hj
      · intro hi
        by_contra hj
        exact hi (h.mpr hj)
  funext x
  by_cases hx : x ∈ OmX m
  · rw [opL_on l i _ hx, opL_on k j _ hx, Dop_opL hr hx, Dop_opL hr hx, dco_zero hx l k i j hc,
      dco_zero hx k l j i hc', zero_smul, zero_add, zero_smul, zero_add, Dop_comm hr hx,
      smul_smul, smul_smul, mul_comm]
  · rw [opL_off l i _ hx (opL_off k j f hx (hf.2 x hx)),
      opL_off k j _ hx (opL_off l i f hx (hf.2 x hx))]
end Formalism.QuantumDeterminants
