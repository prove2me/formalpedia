-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.psiKR_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:54.83565+00:00
-- url     : https://prove2.me/submissions/cbd622d2-5b32-4ec9-a060-dc5ee5983131

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (R : Subring K) (ψ : AddChar K ℂ) (hD : LocalDatum K R ψ) (x : KR R) :
    conj (psiKR R ψ x) = psiKR R ψ (-x) := by
  unfold psiKR
  rw [hD.unitary]
  have e1 : (Submodule.Quotient.mk (Quotient.out (-x)) : KR R) = -x := Quotient.out_eq _
  have e2 : (Submodule.Quotient.mk (Quotient.out x) : KR R) = x := Quotient.out_eq _
  have hx : (Submodule.Quotient.mk (Quotient.out (-x)) : KR R) = Submodule.Quotient.mk (-Quotient.out x) := by
    rw [Submodule.Quotient.mk_neg, e1, e2]
  rw [Submodule.Quotient.eq, LinearMap.mem_range] at hx
  obtain ⟨r, hr⟩ := hx
  have hr' : (r : K) = Quotient.out (-x) - -Quotient.out x := hr
  have hr1 : ψ (r : K) = 1 := by
    have := (hD.selfDual (r : K)).2 r.2 1 R.one_mem
    simpa using this
  have h3 : Quotient.out (-x) = -Quotient.out x + (r : K) := by rw [hr']; ring
  rw [h3, AddChar.map_add_eq_mul, hr1, mul_one]
end Formalism.FourierDecayAlt.P.A5x8
