-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.dual_vector_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:54:16.039584+00:00
-- url     : https://prove2.me/submissions/e45aaf64-f33e-4ed9-9599-27b132a58949

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_N3xM_S
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_om_eq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_UW_sub_S
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_block
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_inv
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_unitary


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
open Formalism.QuantumDeterminants.WeylGroupFacts
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : DualVectorEquivariant := by
  intro k r z z' hz hz' g hg h hh h' hh'
  have hx := s1c2_N3xM_S k r z z' hz hz' g h h' (s1c2_UW_sub_S k r z h hh) (s1c2_UW_sub_S k r z' h' hh')
  set X := formalDeterminantVectorOnGroup k r z z' g with hX
  have hη : h'⁻¹ ∈ UWset k r z' := uw_inv hh'
  have hb : block k r h'⁻¹ := uw_block hη
  have hP : reflectFlagCoordinates k r (h'⁻¹ *ᵥ X) = h'⁻¹ *ᵥ reflectFlagCoordinates k r X := by
    funext i
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · simp only [reflectFlagCoordinates, if_pos hi, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hj
      · rfl
      · rw [hb.1 i j (by omega), if_neg (by intro e; rw [e] at hi; exact hj hi), zero_mul, mul_zero]
    · simp only [reflectFlagCoordinates, if_neg hi, Matrix.mulVec, dotProduct]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hb.2 i j (by omega)]
      split_ifs with e hj
      · rw [e] at hi; exact absurd hj hi
      · rw [mul_zero]
      · rw [zero_mul]
      · rw [zero_mul]
  have hinner : herm (Hpk k r) (h'⁻¹ *ᵥ X) z' = herm (Hpk k r) X z' := by
    conv_lhs => rw [← hη.2.2]
    exact ggHerm_unitary _ _ hη.1 X z'
  rw [s1c2_om_eq k r z z' hz', s1c2_om_eq k r z z' hz', hx, hP, hinner, Matrix.mulVec_add, Matrix.mulVec_smul,
    hη.2.2]
end Formalism.HermitianLatticeCounting.P
