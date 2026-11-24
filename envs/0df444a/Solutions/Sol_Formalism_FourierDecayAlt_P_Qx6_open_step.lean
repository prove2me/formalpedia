-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.open_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:40:16.00938+00:00
-- url     : https://prove2.me/submissions/07d06f05-e60a-40f9-94f5-674cfa60ac19

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_cd_mL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (l : Fin r) {Dc : (Fin r → ℂ) → Set (Mx k r)} (h : IsOpen (UU Dc)) :
    IsOpen (UU (stepD l Dc)) := by
  have hO : IsOpen {x : XX k r | x.1 ∈ OmX r} := by
    have e : OmX r = ⋂ j : Fin r, {x : Fin r → ℂ | x j ≠ 0} := by
      ext x
      simp [OmX]
    rw [e]
    exact (isOpen_iInter_of_finite fun j => isOpen_ne_fun (continuous_apply j) continuous_const).preimage continuous_fst
  have e2 : UU (stepD l Dc) = {x : XX k r | x.1 ∈ OmX r} ∩ mL k r l ⁻¹' UU Dc := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact And.intro h1 (And.intro h1 h2)
    · rintro ⟨h1, -, h2⟩
      exact And.intro h1 h2
  rw [e2]
  exact (cd_mL (k := k) l).continuousOn.isOpen_inter_preimage hO h
end Formalism.FourierDecayAlt.P.Qx6
