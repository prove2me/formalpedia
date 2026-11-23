-- Prove2me | solution 1 for Formalism.UG.P.csScale_latS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:35:33.336004+00:00
-- url     : https://prove2.me/submissions/04acb669-75ba-4cb5-80cd-03cc381136fe

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsScale
import Theorems.Thm_Formalism_UG_P_csScale_hform_add_left
import Theorems.Thm_Formalism_UG_P_csScale_hform_add_right
import Theorems.Thm_Formalism_UG_P_csScale_hform_zero_left
import Theorems.Thm_Formalism_UG_P_csScale_hform_zero_right
import Theorems.Thm_Formalism_UG_P_csScale_hform_smul_left
import Theorems.Thm_Formalism_UG_P_csScale_hform_smul_right
import Theorems.Thm_Formalism_UG_P_csScale_sigR_mem
import Theorems.Thm_Formalism_UG_P_csScale_hform_incl

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
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.UG.P
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) (m : ℤ)
    (hm : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((m : E) * hform (σ : E →+* E) J x y))
    {u w : n → 𝒜} (hu : u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ)
    (hw : w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) :
    ιA (m : E) * hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ιA) u w ∈ 𝒮 := by
  unfold latS at hu hw
  induction hu using Submodule.span_induction generalizing w with
  | mem u hu' =>
    obtain ⟨x, hx, rfl⟩ := hu'
    induction hw using Submodule.span_induction with
    | mem w hw' =>
      obtain ⟨y, hy, rfl⟩ := hw'
      show ιA (m : E) * hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ιA)
        (fun i => ιA (x i)) (fun i => ιA (y i)) ∈ 𝒮
      rw [csScale_hform_incl, ← map_mul]
      exact CS.incl_int ⟨_, hm x hx y hy⟩
    | zero => rw [csScale_hform_zero_right, mul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [csScale_hform_add_right, mul_add]; exact add_mem ha hb
    | smul c a _ ha =>
      rw [Subring.smul_def, csScale_hform_smul_right, mul_left_comm]
      exact mul_mem c.2 ha
  | zero => rw [csScale_hform_zero_left, mul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [csScale_hform_add_left, mul_add]; exact add_mem (ha hw) (hb hw)
  | smul c a _ ha =>
    rw [Subring.smul_def, csScale_hform_smul_left, mul_left_comm]
    exact mul_mem (csScale_sigR_mem σ c.2) (ha hw)
end Formalism.UG.P
