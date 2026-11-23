-- Prove2me | solution 1 for Formalism.UG.P.csSpan_approx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:12.04321+00:00
-- url     : https://prove2.me/submissions/0cd36d8a-33a7-4e8c-a122-47ac4311b9d1

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Theorems.Thm_Formalism_UG_P_adelstabL_incl_int
import Theorems.Thm_Formalism_UG_P_adelstab_incl_C
import Theorems.Thm_Formalism_UG_P_levelafC_mem
import Theorems.Thm_Formalism_UG_P_levelaf_tmul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.UG.P
theorem _root_.solution (hA : Formalism.UG.CS.IntAdApprox) (D : 𝓞 F) (hD : D ≠ 0) {s : 𝒜} (hs : s ∈ 𝒮) :
    ∃ x : E, IsIntegral ℤ x ∧ ∃ w ∈ 𝒮, s = ι x + levelafC E D * w := by
  refine Subring.closure_induction
    (p := fun s _ => ∃ x : E, IsIntegral ℤ x ∧ ∃ w ∈ 𝒮, s = ι x + levelafC E D * w)
    ?_ ?_ ?_ ?_ ?_ ?_ hs
  · rintro x (⟨⟨e, ⟨e', rfl⟩⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · refine ⟨algebraMap (𝓞 E) E e', RingOfIntegers.isIntegral_coe e', 0, zero_mem _, ?_⟩
      simp [inclE]
    · obtain ⟨r, y', hy', hyr⟩ := hA F D hD y hy
      refine ⟨algebraMap (𝓞 F) E r, ?_, (1 : E) ⊗ₜ[F] y', ?_, ?_⟩
      · rw [IsScalarTower.algebraMap_apply (𝓞 F) F E]
        exact (RingOfIntegers.isIntegral_coe r).algebraMap
      · have := levelaf_tmul_mem (F := F) (E := E) 1 hy'
        rwa [map_one] at this
      · rw [adelstab_incl_C]
        simp only [levelafC, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rw [← TensorProduct.tmul_add, ← hyr]
  · exact ⟨0, isIntegral_zero, 0, zero_mem _, by simp⟩
  · exact ⟨1, isIntegral_one, 0, zero_mem _, by simp⟩
  · rintro a b _ _ ⟨x, hx, w, hw, rfl⟩ ⟨y, hy, w', hw', rfl⟩
    exact ⟨x + y, hx.add hy, w + w', add_mem hw hw', by rw [map_add]; ring⟩
  · rintro a _ ⟨x, hx, w, hw, rfl⟩
    exact ⟨-x, hx.neg, -w, neg_mem hw, by rw [map_neg]; ring⟩
  · rintro a b _ _ ⟨x, hx, w, hw, rfl⟩ ⟨y, hy, w', hw', rfl⟩
    refine ⟨x * y, hx.mul hy, w * ι y + ι x * w' + levelafC E D * w * w', ?_, ?_⟩
    · exact add_mem (add_mem (mul_mem hw (adelstabL_incl_int _ hy))
        (mul_mem (adelstabL_incl_int _ hx) hw')) (mul_mem (mul_mem (levelafC_mem D) hw) hw')
    · rw [map_mul]; ring
end Formalism.UG.P
