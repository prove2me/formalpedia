-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.dual_vector_unipotent_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:54:16.875307+00:00
-- url     : https://prove2.me/submissions/83790f33-ffb6-483b-98f3-581b24694041

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_N3xM_S
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_om_eq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_herm_Pm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_x_top
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_N_sub_S
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_nset_iff


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
theorem _root_.solution : DualVectorUnipotentInvariant := by
  intro k r z z' hz hz' g hg n hn n' hn'
  have hx := s1c2_N3xM_S k r z z' hz hz' g n n' (s1c2_N_sub_S k r z hz n hn) (s1c2_N_sub_S k r z' hz' n' hn')
  set X := formalDeterminantVectorOnGroup k r z z' g with hX
  have hcol : col k r n'⁻¹ := ((nset_iff _).1 (mem_n_inv hn')).2
  have htop : ∀ i : Fin (2 * r + k + 1), r + k < i.val → X i = 0 := fun i hi => s1c2_x_top k r z z' g i hi
  have hmid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (n'⁻¹ *ᵥ X) i = X i := by
    intro i hi
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · by_cases hk : i.val ≤ r + k
      · rw [hcol i i hk (Or.inr hi), if_pos rfl, one_mul]
      · rw [htop i (by omega), mul_zero]
    · intro j _ hj
      by_cases hk : j.val ≤ r + k
      · rw [hcol i j hk (Or.inr hi), if_neg (Ne.symm hj), zero_mul]
      · rw [htop j (by omega), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hP : reflectFlagCoordinates k r (n'⁻¹ *ᵥ X) = reflectFlagCoordinates k r X := by
    funext i
    simp only [reflectFlagCoordinates]
    split_ifs with h
    · exact hmid i h.1
    · rfl
  rw [s1c2_om_eq k r z z' hz', s1c2_om_eq k r z z' hz', hx, hP, ← s1c2_herm_Pm k r z' (n'⁻¹ *ᵥ X) hz', hP,
    s1c2_herm_Pm k r z' X hz']
end Formalism.HermitianLatticeCounting.P
