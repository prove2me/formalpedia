-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.Lead.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:32.672074+00:00
-- url     : https://prove2.me/submissions/92b408ac-3a50-4dd6-b495-fe05ceb22886

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
variable {R : Type*} [Ring R] [Algebra ℂ R]
variable {n m : ℕ} {c d : R} {f g : ℂ → R}
namespace Formalism.FourierDecayAlt.P.Mx5
namespace Lead
theorem _root_.solution {ι : Type} (s : Finset ι) (F : ι → ℂ → R) (h : ∀ i ∈ s, Lead n 0 (F i)) :
    Lead n 0 fun Y => ∑ i ∈ s, F i Y := by
  classical
  choose! a ha using h
  refine ⟨fun j => ∑ i ∈ s, a i j, fun Y => ?_⟩
  show ∑ i ∈ s, F i Y = Y ^ n • (0 : R) + ∑ j ∈ range n, Y ^ j • ∑ i ∈ s, a i j
  rw [Finset.sum_congr rfl (fun i hi => ha i hi Y)]
  simp only [smul_zero, zero_add, Finset.smul_sum]
  rw [Finset.sum_comm]
end Lead
end Formalism.FourierDecayAlt.P.Mx5
