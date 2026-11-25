-- Prove2me | solution 1 for CompanionTheory.D.gk.Poul.isInvInvariant_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:11:56.785803+00:00
-- url     : https://prove2.me/submissions/8c781a7f-f2ee-4c0b-8a12-69d36f6aa63e

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Unimod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeries__Poulsen_b54a5a55a6942064
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_PoulsenSmoothVectorsDense
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsSmForm_continuous
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_exists_iota_eq
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_PIW_HCFdeg_stUnimod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.Poul
open PI PI.UpqRep CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.admitted CompanionTheory.LimBd
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace CompanionTheory.D.gk.Poul
theorem _root_.solution {ε : Fin (2 * r + k + 1) → Bool} {P : Mat (2 * r + k + 1)} (hP : IsCayley k r ε P)
    (hG : IsMatGroup (UH (Hpk k r))) : (haar : Measure (MG (UH (Hpk k r)) hG)).IsInvInvariant := by
  let f : UJ ε →* MG (UH (Hpk k r)) hG :=
    { toFun := fun g => MG.mk hG _ (SchurHpk.iota_mem hP g)
      map_one' := MG.ext (SchurHpk.iota_one hP)
      map_mul' := fun a b => MG.ext (SchurHpk.iota_mul hP a b) }
  have hf : Continuous f := MG.continuous_iff.2 (SchurHpk.iota_closedEmb hP).continuous
  have hs : Function.Surjective f := fun x => by
    obtain ⟨g, hg⟩ := SchurHpk.exists_iota_eq hP x.mem
    exact ⟨g, MG.ext hg⟩
  have hce : IsClosedEmbedding f :=
    IsClosedEmbedding.of_comp MG.isClosedEmbedding_mat.isEmbedding (SchurHpk.iota_closedEmb hP)
  have hH : IsHaarMeasure (Measure.map f (muG ε)) := isHaarMeasure_map (muG ε) f hf hs hce.tendsto_cocompact
  have hI := (PIW.HCFdeg.stUnimod _ ε).2
  have hinv : (Measure.map f (muG ε)).inv = Measure.map f (muG ε) := by
    rw [Measure.inv_def, Measure.map_map measurable_inv hf.measurable]
    have : (Inv.inv ∘ f : UJ ε → _) = f ∘ Inv.inv := funext fun g => (map_inv f g).symm
    rw [this, ← Measure.map_map hf.measurable measurable_inv, Measure.map_inv_eq_self]
  refine ⟨?_⟩
  rw [isMulLeftInvariant_eq_smul haar (Measure.map f (muG ε)), Measure.inv_def, Measure.map_smul, ← Measure.inv_def,
    hinv]
end CompanionTheory.D.gk.Poul
