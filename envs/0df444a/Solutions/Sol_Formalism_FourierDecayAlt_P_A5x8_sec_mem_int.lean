-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.sec_mem_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:06.101867+00:00
-- url     : https://prove2.me/submissions/89e7f574-1480-4eff-983e-a54b9bde9d70

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
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution {n : ℕ} {H : Subgroup (GL (Fin n) K)} (g : H) (hd : (sec_m g).det = 1) :
    g ∈ intSub R H ↔ IsInt R (sec_m g) := by
  constructor
  · intro hg
    exact hg.1
  · intro h
    refine ⟨h, ?_⟩
    let B : Matrix (Fin n) (Fin n) R := fun a b => ⟨sec_m g a b, h a b⟩
    have hB : R.subtype.mapMatrix B = sec_m g := by
      ext a b
      rfl
    have hinv : (((g : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (sec_m g).adjugate := by
      rw [Matrix.coe_units_inv, Matrix.inv_def]
      simp [sec_m] at hd ⊢
      simp [hd]
    intro a b
    rw [hinv, ← hB, ← RingHom.map_adjugate]
    exact (B.adjugate a b).2
end Formalism.FourierDecayAlt.P.A5x8
