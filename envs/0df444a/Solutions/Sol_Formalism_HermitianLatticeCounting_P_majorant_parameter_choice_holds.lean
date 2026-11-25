-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.majorant_parameter_choice_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:05:11.523797+00:00
-- url     : https://prove2.me/submissions/3f331ba2-83a7-4b7e-900d-a64ec110201c

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_majorant_orthogonal_component
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_majorant_phase_estimate_holds


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
theorem _root_.solution : SkewVectorChoice := by
  have hPhase : MajorantPhaseChoice := majorant_phase_estimate_holds
  intro V _ _ θ hθ r y a hl
  obtain ⟨e', he1, _, he3, _⟩ := majorant_orthogonal_component V (r + 1) y a.castSucc
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ := majorant_orthogonal_component V (r + 1) y a.succ
  have hu0 : u ≠ 0 := by
    intro h; apply hl; rw [← hu3, h, norm_zero]
  obtain ⟨p1, p2, p3⟩ := hPhase V θ hθ u (y a.succ) (y '' {b | b ≤ a.castSucc}) hu0
    (by
      rintro w ⟨b, hb, rfl⟩
      exact hu2 b (lt_of_le_of_lt (show b ≤ a.castSucc from hb) (Fin.castSucc_lt_succ)))
    hu4
  refine ⟨e', _, he1, he3, p1, fun b hb => p2 _ ⟨b, hb, rfl⟩, ?_⟩
  rw [p3, hu3]
end Formalism.HermitianLatticeCounting.P
