-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x7.card_iso_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:00.650734+00:00
-- url     : https://prove2.me/submissions/deeddc11-906f-4e6c-a9c8-389abdc79087

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_lamLin_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_coker_subsingleton
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
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x7
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x7
theorem _root_.solution {n n' : ℕ} {Z : Matrix (Fin n) (Fin n) K} {Z' : Matrix (Fin n') (Fin n') K}
    (hZ : IsInt R Z⁻¹) (h1 : Z * Z⁻¹ = 1) (hZ' : IsInt R Z'⁻¹) (h1' : Z' * Z'⁻¹ = 1) :
    Nat.card (isoZZ R Z Z') = 1 := by
  haveI := coker_subsingleton R hZ h1
  haveI := coker_subsingleton R hZ' h1'
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext (LinearEquiv.ext fun x => Subsingleton.elim _ _)⟩, ⟨⟨LinearEquiv.ofSubsingleton _ _, ?_⟩⟩⟩
  simp only [isoZZ, Set.mem_setOf_eq]
  exact ⟨Subsingleton.elim _ _, fun v v' _ => by rw [lamLin_zero R hZ, lamLin_zero R hZ']⟩
end Formalism.FourierDecayAlt.P.A5x7
