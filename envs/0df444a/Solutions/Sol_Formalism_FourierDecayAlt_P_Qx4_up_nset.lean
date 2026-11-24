-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.up_nset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:19:03.793803+00:00
-- url     : https://prove2.me/submissions/41804e0a-332c-4604-9510-945867628243

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_herm_e_right
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
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_nset_iff
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
theorem _root_.solution {u : Mx k r} (hu : u ∈ UP k r l) : u ∈ Nset k r := by
  rw [WeylGroupFacts.nset_iff]
  refine ⟨hu.1.1, fun i j hj hi => ?_⟩
  rw [B2x6.ent u i j]
  have hl := l.isLt
  by_cases hjl : j.val < l.val
  · have e : eI k r ⟨j.val, by omega⟩ = j := Fin.ext rfl
    have := (hu.1.2 ⟨j.val, by omega⟩ (by simpa using hjl)).1
    rw [e] at this
    rw [this]; simp only [bvec, Pi.single_apply]
  · by_cases hjl' : j.val = l.val
    · have e : eI k r l = j := Fin.ext hjl'.symm
      rw [← e, hu.2.1]; simp only [bvec, Pi.single_apply]
    · have h0 : ⟪bvec j, 𝐞⟫ = 0 := by
        rw [herm_e_right]
        apply Pi.single_eq_of_ne
        intro h; have := congrArg Fin.val h; simp only [esI] at this; omega
      obtain ⟨t, ht⟩ := hu.2.2 _ h0
      rw [ht]
      have : (bvec (eI k r l) : Fin (2 * r + k + 1) → ℂ) i = 0 := by
        apply Pi.single_eq_of_ne
        intro h; have := congrArg Fin.val h; simp only [eI] at this; omega
      rw [Pi.add_apply, Pi.smul_apply, this, smul_zero, add_zero]; simp only [bvec, Pi.single_apply]
end Formalism.FourierDecayAlt.P.Qx4
