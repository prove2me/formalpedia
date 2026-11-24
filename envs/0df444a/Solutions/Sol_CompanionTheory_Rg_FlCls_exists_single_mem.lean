-- Prove2me | solution 1 for CompanionTheory.Rg.FlCls.exists_single_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:18:28.589952+00:00
-- url     : https://prove2.me/submissions/463d221c-0249-42eb-b2af-8b11f845b68a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_NefEffectiveCones_ExistsNsmulMulVecMemHat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAdeleRingTensorEquivInfiniteProdFinite
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UJClassFin
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_ArchimedeanDenseStabilizers_DenseRangeOfNotIsReal
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_CompanionTheory_HatBound_exists_nsmul_mem_lattice
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
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
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix ComplexOrder MatrixOrder
open CompanionTheory CompanionTheory.Rg CompanionTheory.Rg.FlCls
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
namespace CompanionTheory.Rg.FlCls
theorem _root_.solution (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e →
      Pi.single i ((c : F) • e) ∈ (L : Set (Fin n → E)) := by
  classical
  choose f hf hf' using fun i : Fin n => GlobalTheory.CompanionTheory.HatBound.exists_nsmul_mem_lattice L hL (Pi.single i 1)
  have hpos : 0 < ∏ i, f i := Finset.prod_pos fun i _ => hf _
  set m := ∏ i, f i with hm
  refine ⟨m, Nat.cast_ne_zero.2 hpos.ne', fun i e he => ?_⟩
  obtain ⟨k, hk⟩ : f i ∣ m := Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  have h1 := L.smul_mem (⟨e, he⟩ : 𝓞 E) (nsmul_mem (hf' i) k)
  have e2 : (Pi.single i (((m : 𝓞 F) : F) • e) : Fin n → E) =
      (⟨e, he⟩ : 𝓞 E) • k • f i • (Pi.single i (1 : E) : Fin n → E) := by
    funext j
    change _ = e * (k • f i • (Pi.single i (1 : E) : Fin n → E) j)
    by_cases h : j = i
    · subst h
      simp [hk, Algebra.smul_def]; ring
    · simp [h]
  rw [e2]
  exact h1
end CompanionTheory.Rg.FlCls
