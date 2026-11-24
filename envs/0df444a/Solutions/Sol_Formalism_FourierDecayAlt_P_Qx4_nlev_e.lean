-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.nlev_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:31:19.804207+00:00
-- url     : https://prove2.me/submissions/973b8b7d-785e-4efd-9b9a-72bf3552e075

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_herm_es_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_eI_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_e_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_ent
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Matrix Finset
open scoped ContDiff ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
local notation "⟪" u ", " v "⟫" => herm (Hpk k r) u v
variable {l : Fin r}
local notation "𝐞" => bvec (eI k r l)
local notation "𝐬" => bvec (esI k r l)
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution {n : Mx k r} (hn : n ∈ Nlev k r l.castSucc) : n *ᵥ 𝐞 = 𝐞 := by
  ext i
  by_cases hi : l.val ≤ i.val
  · rw [← B2x6.ent, hn.1.2.1 l i hi]; simp only [bvec, Pi.single_apply]
  · have hl := l.isLt
    have e : eI k r ⟨i.val, by omega⟩ = i := Fin.ext rfl
    have ha : (⟨i.val, by omega⟩ : Fin r).val < (l.castSucc).val := by simp only [Fin.val_castSucc]; omega
    have hne : l ≠ ⟨i.val, by omega⟩ := fun h => hi (by rw [h])
    rw [← e, ← herm_es_right (n *ᵥ bvec (eI k r l))]
    conv_lhs => rw [← (hn.2.2 _ ha).2]
    rw [uh_herm hn.2.1, h_e_es, if_neg hne]
    symm
    apply Pi.single_eq_of_ne
    intro h; exact hne (eI_inj.1 h).symm
end Formalism.FourierDecayAlt.P.Qx4
