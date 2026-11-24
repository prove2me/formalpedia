-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.omega_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:02.669465+00:00
-- url     : https://prove2.me/submissions/1abaa7c4-4bf0-4a26-b449-084761acb78c

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_hzz
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_om_eq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_herm_Pm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_herm_e
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_fvec_lt
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_x_top
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gk_herm_add_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gk_herm_smul_left
import Theorems.Thm_Formalism_QuantumDeterminants_fvec_apply_ge
import Theorems.Thm_Formalism_QuantumDeterminants_fvec_apply_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate TensorProduct
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : OrthogonalComplementDecomposition := by
  intro k r z z' hz hz' hT' g hg
  set X := formalDeterminantVectorOnGroup k r z z' g with hX
  have hTc : ((Tz k r z' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT'
  have hW : inWb k r (N3om k r z z' g) := by
    intro i hi
    simp only [N3om]
    rw [if_neg (by omega)]
  refine ⟨hW, ?_, ?_⟩
  · intro b
    by_cases hb : b.val < r
    · rw [s1c2_fvec_lt k r z' b hb, s1c2_herm_e]
      exact hW _ (Or.inr (by simp only [esI]; omega))
    · have hbl : fvec k r z' b = z' := by simp [fvec, hb]
      rw [hbl, s1c2_om_eq k r z z' hz', gk_herm_add_left, gk_herm_smul_left, s1c2_herm_Pm k r z' _ hz', s1c2_hzz]
      field_simp
      ring
  · refine ⟨fun b => if hb : b.val < r then X (eI k r ⟨b.val, hb⟩)
      else -(herm (Hpk k r) X z' / (Tz k r z' : ℂ)), ?_⟩
    funext i
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i.val < r
    · rw [hW i (Or.inl hi), add_zero, Finset.sum_eq_single ⟨i.val, by omega⟩]
      · rw [fvec_apply_lt z' hz' _ i hi, if_pos rfl, mul_one, dif_pos hi]; rfl
      · intro c _ hc
        rw [fvec_apply_lt z' hz' _ i hi, if_neg (fun h => hc (Fin.ext h)), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · push Not at hi
      rw [Finset.sum_eq_single (Fin.last r)]
      · rw [fvec_apply_ge z' _ i hi, if_pos (by simp), dif_neg (by simp)]
        by_cases hk : i.val ≤ r + k
        · simp only [N3om]
          rw [if_pos ⟨hi, hk⟩]; ring
        · rw [hW i (Or.inr (by omega)), hz' i (Or.inr (by omega)), mul_zero, add_zero]
          exact s1c2_x_top k r z z' g i (by omega)
      · intro c _ hc
        rw [fvec_apply_ge z' _ i hi, if_neg (fun h => hc (Fin.ext (by simp; omega))), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.HermitianLatticeCounting.P
