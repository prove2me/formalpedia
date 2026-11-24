-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_N3xM_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:39:51.266576+00:00
-- url     : https://prove2.me/submissions/b461de8b-9fd1-4188-9480-7375aa065cce

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_transform_upper_unitriangular_change
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_N3xM_eq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_S_cols
import Theorems.Thm_Formalism_QuantumDeterminants_Sset_UH
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_symmetric_group_holds


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
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (g s s' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hs : s ∈ Sset k r z) (hs' : s' ∈ Sset k r z') :
    formalDeterminantVectorOnGroup k r z z' (s * g * s') = s'⁻¹ *ᵥ formalDeterminantVectorOnGroup k r z z' g := by
  obtain ⟨A, hA, hAf⟩ := s1c2_S_cols k r z hz _ ((symmetric_group_holds k r z hz).2.2 s hs)
  obtain ⟨A', hA', hAf'⟩ := s1c2_S_cols k r z' hz' _ hs'
  have hsU : s' ∈ UH (Hpk k r) := Sset_UH hs'
  rw [s1c2_N3xM_eq, s1c2_N3xM_eq,
    ← transform_upper_unitriangular_change (Hpk k r) s' hsU (isUnit_of_uh hsU) _ _ A A' hA hA' hAf']
  congr 1
  funext a
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAf,
    Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul]
end Formalism.HermitianLatticeCounting.P
