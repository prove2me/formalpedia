-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_gram_f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:57.861546+00:00
-- url     : https://prove2.me/submissions/f43aea4f-07d7-4382-9624-99378b849dd1

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_hzz
import Theorems.Thm_Formalism_QuantumDeterminants_ggBlockA


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
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (a b : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z a) (fvec k r z b) =
      if a = Fin.last r ∧ b = Fin.last r then -((Tz k r z : ℝ) : ℂ) else 0 := by
  rw [ggBlockA k r z hz b a, Matrix.smul_apply, smul_eq_mul, s1c2_hzz]
  by_cases h : a = Fin.last r ∧ b = Fin.last r
  · obtain ⟨rfl, rfl⟩ := h; simp [ggLastU]
  · rw [if_neg h]
    have : ggLastU r b a = 0 := by
      unfold ggLastU
      rw [if_neg (fun h' => h ⟨h'.2, h'.1⟩)]
    rw [this, mul_zero]
end Formalism.HermitianLatticeCounting.P
