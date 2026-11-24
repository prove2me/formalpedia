-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.twistedLatticeIndex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:00.169152+00:00
-- url     : https://prove2.me/submissions/fcbc50f9-abfa-4361-b140-3d546c629963

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_tw_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_relIndex_nsmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_rk_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_rk_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_rk_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_gA_eq_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_inf_eq_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x3
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S6.IndexCore := by
  intro E _ _ _ A g s hA0 hA hg hU
  have h2 : idx E (zsub E (A * FractionalIdeal.spanSingleton _ (g : E)))
      (twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s) = g ^ deg E := by
    unfold idx
    rw [tw_eq E A g s hA hg hU, Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_right,
      ← AddSubgroup.inf_relIndex_right, inf_eq_map E A g s hg, relIndex_nsmul, rk_eq E A s hA0 hA]
  refine ⟨?_, h2⟩
  have h3 : idx E (zsub E (A * FractionalIdeal.spanSingleton _ (g : E))) (zsub E A)
      = g ^ deg E * g ^ deg E := by
    unfold idx
    rw [gA_eq_map, relIndex_nsmul, ← rk_add E A s hA, rk_succ, rk_eq E A s hA0 hA, pow_add]
  have hle1 : (zsub E (A * FractionalIdeal.spanSingleton _ (g : E))).toAddSubgroup ≤
      (twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s).toAddSubgroup := by
    rw [tw_eq E A g s hA hg hU]
    exact Submodule.toAddSubgroup_mono le_sup_right
  have hle2 : (twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s).toAddSubgroup ≤
      (zsub E A).toAddSubgroup := Submodule.toAddSubgroup_mono inf_le_left
  have h4 := AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2
  unfold idx at h2 h3 ⊢
  rw [h2, h3] at h4
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hg _) h4
end Formalism.FourierDecayAlt.P
