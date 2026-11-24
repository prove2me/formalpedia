-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_herm_mid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:20.507801+00:00
-- url     : https://prove2.me/submissions/a0ab48b1-20f6-4351-8251-73ecd15a2c92

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_Hh
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_swap
import Theorems.Thm_Formalism_QuantumDeterminants_ggHpk_mulVec_Wb


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
theorem _root_.solution (k r : ℕ) (z' d : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z')
    (hd : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → d i = 0) : herm (Hpk k r) d z' = 0 := by
  rw [ggHerm_swap _ (s1c2_Hh k r)]
  have : herm (Hpk k r) z' d = 0 := by
    simp only [herm, dotProduct, ggHpk_mulVec_Wb k r z' hz', Pi.star_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h : r ≤ i.val ∧ i.val ≤ r + k
    · rw [hd i h.1 h.2, star_zero, zero_mul]
    · rw [hz' i (by omega), mul_zero, mul_zero]
  rw [this, star_zero]
end Formalism.HermitianLatticeCounting.P
