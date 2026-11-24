-- Prove2me | solution 1 for Formalism.UG.P.csEquiv_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:38:15.892863+00:00
-- url     : https://prove2.me/submissions/3d10a1a8-609b-4fd2-808d-5ad4fed4bfd3

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsEquiv
import Theorems.Thm_Formalism_UG_P_csEquiv_mem
import Theorems.Thm_P2M_Formalism_UG_P_glEquiv_apply__d9aedd7a5d31


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
open Formalism.UG Formalism.UG.CS
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (Λ : Submodule (𝓞 E) (n → E)) (γ : GL n E)
    (g k : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hk : k ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ)) :
    globLat (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g * k) Λ =
      Formalism.HermitianLatticesTheory.gmap (glEquiv γ) (globLat g Λ) := by
  ext x
  rw [csEquiv_mem Λ γ g k hk x]
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [glEquiv_apply', Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  · rintro ⟨y, hy, rfl⟩
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [glEquiv_apply', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
    exact hy
end Formalism.UG.P
