-- Prove2me | solution 1 for Formalism.UG.P.csDual_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:02.437816+00:00
-- url     : https://prove2.me/submissions/b8d98f68-c00a-4b0b-ae3b-77270b40326b

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Theorems.Thm_Formalism_UG_P_csDual_hform_add_left
import Theorems.Thm_Formalism_UG_P_csDual_hform_zero_left
import Theorems.Thm_Formalism_UG_P_csDual_hform_smul_left
import Theorems.Thm_Formalism_UG_P_csDual_sig_mem
import Theorems.Thm_Formalism_UG_P_csDual_hform_incl

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
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E) (M : Submodule (𝓞 E) (n → E)) (x : n → E)
    (hx : ∀ y ∈ M, hform (σ : E →+* E) J y x ∈ (algebraMap (𝓞 E) E).range)
    (u : n → 𝒜) (hu : u ∈ Submodule.span 𝒮 ((fun y : n → E => fun i => ι (y i)) '' (M : Set (n → E)))) :
    hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ι) u (fun i => ι (x i)) ∈ 𝒮 := by
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    rw [csDual_hform_incl]
    obtain ⟨w, hw⟩ := hx y hy
    rw [← hw]
    exact Subring.subset_closure (Or.inl ⟨⟨_, w, rfl⟩, rfl⟩)
  | zero => rw [csDual_hform_zero_left]; exact zero_mem _
  | add u v _ _ hu hv => rw [csDual_hform_add_left]; exact add_mem hu hv
  | smul a u _ hu =>
    rw [Subring.smul_def, csDual_hform_smul_left]
    exact mul_mem (csDual_sig_mem σ a.2) hu
end Formalism.UG.P
