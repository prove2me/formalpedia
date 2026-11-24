-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_S_cols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:32:35.803381+00:00
-- url     : https://prove2.me/submissions/c84ae135-a8b0-4078-8d5d-876430574ce4

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gj_cols
import Theorems.Thm_Formalism_QuantumDeterminants_S_F


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
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hs : s ∈ Sset k r z) :
    ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, IsUpperUnitriangular U ∧ ∀ b, s *ᵥ fvec k r z b = ∑ e, U e b • fvec k r z e := by
  obtain ⟨U, h1, h2, h3⟩ := S_F hz hs
  exact ⟨U, ⟨h2, h1⟩, (gj_cols _ _ _).1 h3⟩
end Formalism.HermitianLatticeCounting.P
