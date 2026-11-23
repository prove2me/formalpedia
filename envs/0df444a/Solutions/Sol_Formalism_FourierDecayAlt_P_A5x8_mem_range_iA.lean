-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.mem_range_iA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:49:51.645748+00:00
-- url     : https://prove2.me/submissions/8c7f9415-8cc3-473b-9a3f-2968a41d3d10

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_dot_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_mk_outV
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_mk_eq_zero
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
variable {K : Type} [CommRing K] (R : Subring K) {m : ℕ}
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (Z : Matrix (Fin m) (Fin m) K) (x : Fin m → KR R)
    (hx : ∀ j, (outV R x ᵥ* Z) j ∈ R) : x ∈ Set.range (iA R Z) := by
  let f : (Fin m → R) →ₗ[R] KR R := (Submodule.mkQ _).comp (iso_dot R (outV R x))
  have hker : latZ R Z ≤ LinearMap.ker f := by
    intro v hv
    obtain ⟨u, hu⟩ := hv
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hu
    have hmem : (outV R x ᵥ* Z) ⬝ᵥ coeLin R u ∈ R := R.sum_mem fun j _ => R.mul_mem (hx j) (u j).2
    rw [LinearMap.mem_ker, LinearMap.comp_apply, iso_dot_apply, ← hu, Matrix.dotProduct_mulVec,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    exact ⟨⟨_, hmem⟩, rfl⟩
  refine ⟨(latZ R Z).liftQ f hker, ?_⟩
  funext j
  have hc : coeLin R (Pi.single j (1 : R)) = Pi.single j (1 : K) := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp [coeLin]
    · simp [coeLin, Pi.single_apply, hk]
  show (latZ R Z).liftQ f hker (Submodule.Quotient.mk (Pi.single j 1)) = x j
  rw [Submodule.liftQ_apply]
  simp only [f, LinearMap.comp_apply, iso_dot_apply, Submodule.mkQ_apply]
  rw [hc, dotProduct_single, mul_one, mk_outV]
end Formalism.FourierDecayAlt.P.A5x8
