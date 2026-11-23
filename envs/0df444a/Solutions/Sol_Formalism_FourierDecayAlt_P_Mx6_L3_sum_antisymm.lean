-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.L3.sum_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:24.62826+00:00
-- url     : https://prove2.me/submissions/e24d1801-f6c6-4483-887c-a96ed474df09

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.L3
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6.L3
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M] (I : Finset ℕ) (F : ℕ → ℕ → M)
    (h : ∀ i ∈ I, ∀ j ∈ I, F i j + F j i = 0) : ∑ i ∈ I, ∑ j ∈ I, F i j = 0 := by
  have h1 : ∑ i ∈ I, ∑ j ∈ I, F i j + ∑ i ∈ I, ∑ j ∈ I, F i j = 0 := by
    nth_rewrite 2 [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun j hj => h i hi j hj
  have h2 : (2 : ℂ) • ∑ i ∈ I, ∑ j ∈ I, F i j = 0 := by rw [two_smul]; exact h1
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
end Formalism.FourierDecayAlt.P.Mx6.L3
