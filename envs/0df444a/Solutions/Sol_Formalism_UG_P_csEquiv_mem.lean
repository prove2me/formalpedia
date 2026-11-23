-- Prove2me | solution 1 for Formalism.UG.P.csEquiv_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:57.352155+00:00
-- url     : https://prove2.me/submissions/16a7baf1-5efe-44dc-a90b-ae783639ad15

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsEquiv
import Theorems.Thm_Formalism_UG_P_csEquiv_bc_mulVec

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
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ)) (x : n → E) :
    x ∈ globLat (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g * k) Λ ↔
      ((γ⁻¹ : GL n E) : Matrix n n E) *ᵥ x ∈ globLat g Λ := by
  have hki := (stabGL _).inv_mem hk
  show (((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g * k)⁻¹ :
      GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔
    ((g⁻¹ : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((((γ⁻¹ : GL n E) : Matrix n n E) *ᵥ x) i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← map_inv, csEquiv_bc_mulVec]
  exact (hki _).symm
end Formalism.UG.P
