-- Prove2me | solution 1 for CompanionTheory.Rg.FlCls.exists_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:01:29.998482+00:00
-- url     : https://prove2.me/submissions/2cdcece9-b7be-41b3-b219-a1944f1d28c3

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
import Theorems.Thm_GlobalTheory_CompanionTheory_HatBound_exists_nat_mul_integer
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
theorem _root_.solution (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ (L : Set (Fin n → E)), ∀ i, IsIntegral ℤ ((c : F) • x i) := by
  classical
  obtain ⟨s, hs⟩ := hL
  choose f hf r hr using GlobalTheory.CompanionTheory.HatBound.exists_nat_mul_integer E
  have hpos : 0 < ∏ x ∈ s, ∏ i, f (x i) := Finset.prod_pos fun x _ => Finset.prod_pos fun i _ => hf _
  set m := ∏ x ∈ s, ∏ i, f (x i) with hm
  refine ⟨m, Nat.cast_ne_zero.2 hpos.ne', fun x hx i => ?_⟩
  have e : ((m : 𝓞 F) : F) • x i = (m : E) * x i := by
    rw [Algebra.smul_def]; simp
  rw [e]
  clear e
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ : f (x i) ∣ m := (Finset.dvd_prod_of_mem (fun i => f (x i)) (Finset.mem_univ i)).trans
      (Finset.dvd_prod_of_mem (fun x : Fin n → E => ∏ i, f (x i)) hx)
    have : (m : E) * x i = ((k * r (x i) : 𝓞 E) : E) := by
      have h7 : ((k * r (x i) : 𝓞 E) : E) = (k : E) * (f (x i) * x i) := by
        rw [← hr (x i)]; simp
      rw [h7, hk]; push_cast; ring
    rw [this]
    exact (k * r (x i) : 𝓞 E).isIntegral_coe
  | zero => simpa using isIntegral_zero
  | add x y _ _ hx hy => rw [Pi.add_apply, mul_add]; exact hx.add hy
  | smul a x _ hx =>
    have : (m : E) * (a • x) i = (a : E) * ((m : E) * x i) := by
      rw [Pi.smul_apply, Algebra.smul_def]; ring
    rw [this]
    exact a.isIntegral_coe.mul hx
end CompanionTheory.Rg.FlCls
