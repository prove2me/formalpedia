-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_x_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:26.367109+00:00
-- url     : https://prove2.me/submissions/f679a9e0-b68f-4072-8308-dfcacf50254d

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_orthogonality_relation
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_hL_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_N3xM_eq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_herm_e
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_fvec_lt

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
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i : Fin (2 * r + k + 1)) (hi : r + k < i.val) :
    formalDeterminantVectorOnGroup k r z z' g i = 0 := by
  have hb : 2 * r + k - i.val < r := by omega
  have h := orthogonality_relation _ (hermitianSesquilinearForm (Hpk k r)) r (fun a => g⁻¹ *ᵥ fvec k r z a) (fvec k r z')
    ⟨2 * r + k - i.val, by omega⟩
  rw [if_neg (by intro h'; have := congrArg Fin.val h'; simp at this; omega), s1c2_hL_apply, ← s1c2_N3xM_eq,
    s1c2_fvec_lt k r z' _ hb, s1c2_herm_e] at h
  have e : esI k r ⟨2 * r + k - i.val, hb⟩ = i := by
    apply Fin.ext; simp only [esI]; omega
  rwa [e] at h
end Formalism.HermitianLatticeCounting.P
