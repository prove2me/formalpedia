-- Prove2me | solution 1 for Formalism.L2.Th1.H.phase_root_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:28:20.897827+00:00
-- url     : https://prove2.me/submissions/a82d1603-b98c-4a34-a29c-c775b29c81d9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_QuadraticSemicharactersOfProductThetaMem
import Theorems.Thm_Formalism_L2_Th1_H_phase_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace Formalism.L2.Th1.H
theorem _root_.solution (H : Sesq V) (Λ : AddSubgroup V) (hΛ : IsSelfDual H Λ) (N : ℕ) {s x : V}
    (hs : (N : ℂ) • s ∈ Λ) (hx : x ∈ Λ) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)) ^ (2 * N) = 1 := by
  exact phase_root H Λ hΛ.ge N hs hx
end Formalism.L2.Th1.H
