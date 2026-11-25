-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW.NCovAd_inf_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:12:38.450377+00:00
-- url     : https://prove2.me/submissions/051b49d2-7654-440f-9d09-d2d58bd62a9a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IntAdCpctOpen
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_CompactCovering_NCovAd
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Metric
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RescaleCore Formalism.L2.SG.Pf.RescaleCore.NCov
open Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW
theorem _root_.solution : ∃ R : ℝ, ∀ x : Ainf F, ∃ β : 𝓞 F,
    ∀ v : InfinitePlace F, ‖(x - algebraMap F (Ainf F) (β : F)) v‖ ≤ R := by
  classical
  set b := NumberField.mixedEmbedding.latticeBasis F with hb
  have hB : ∃ R : ℝ, ∀ y ∈ ZSpan.fundamentalDomain b, ‖y‖ ≤ R := by
    first
    | exact (ZSpan.fundamentalDomain_isBounded b).exists_norm_le
    | exact isBounded_iff_forall_norm_le.mp (ZSpan.fundamentalDomain_isBounded b)
  obtain ⟨R, hR⟩ := hB
  refine ⟨R, fun x => ?_⟩
  obtain ⟨⟨w, hw⟩, hwD, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x)
  have hc' : ∃ c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ, ∑ i, c i • b i = w := by
    first
    | exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hw
    | exact Submodule.mem_span_range_iff_exists_fun.mp hw
  obtain ⟨c, hc⟩ := hc'
  let γ : 𝓞 F := ∑ i, c i • NumberField.RingOfIntegers.basis F i
  have hγ : NumberField.mixedEmbedding F (algebraMap (𝓞 F) F γ) = w := by
    rw [← hc]
    simp only [γ, map_sum, map_zsmul, hb, NumberField.mixedEmbedding.latticeBasis_apply,
      NumberField.integralBasis_apply]
  refine ⟨-γ, fun v => ?_⟩
  have hneg : ((-γ : 𝓞 F) : F) = -(algebraMap (𝓞 F) F γ) := by
    first
    | rfl
    | simp
    | (push_cast; rfl)
  set z := x - algebraMap F (Ainf F) ((-γ : 𝓞 F) : F) with hzdef
  have hz : NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z ∈ ZSpan.fundamentalDomain b := by
    have e : NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z = w + NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x := by
      rw [hzdef, hneg, map_neg, sub_neg_eq_add, map_add, ← hγ,
        NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, add_comm]
    rw [e]
    first
    | exact hwD
    | (rw [Submodule.vadd_def, vadd_eq_add] at hwD; exact hwD)
    | (simpa [Submodule.vadd_def] using hwD)
  have hn := hR _ hz
  by_cases hv : v.IsReal
  · calc ‖z v‖ = ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z).1 ⟨v, hv⟩‖ := by
          rw [NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
          exact ((NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero
            (map_zero _) _).symm
      _ ≤ ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z).1‖ := norm_le_pi_norm _ _
      _ ≤ ‖NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z‖ := norm_fst_le _
      _ ≤ R := hn
  · have hv' : v.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv
    calc ‖z v‖ = ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z).2 ⟨v, hv'⟩‖ := by
          rw [NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
          exact ((NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
            (map_zero _) _).symm
      _ ≤ ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z).2‖ := norm_le_pi_norm _ _
      _ ≤ ‖NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z‖ := norm_snd_le _
      _ ≤ R := hn
end Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW
