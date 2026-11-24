-- Prove2me | solution 1 for Formalism.UG.P.adelstab_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:38:08.301723+00:00
-- url     : https://prove2.me/submissions/47814fee-91b5-4854-bb78-5871b1881468

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab
import Theorems.Thm_Formalism_UG_P_adelstab_mem_iff

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
theorem _root_.solution (G : GL n 𝒜) (L : Submodule 𝒮 (n → 𝒜)) (γ₀ : GL n E)
    (hM : G⁻¹ * bc ι γ₀ * G ∈ stabGL L) : γ₀ ∈ stabGL (adelstabLam F E G L) := by
  intro x
  rw [adelstab_mem_iff, adelstab_mem_iff]
  have key : (fun i => ι (((γ₀ : Matrix n n E) *ᵥ x) i)) =
      ((bc ι γ₀ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ι (x i)) := by
    ext i; rw [RingHom.map_mulVec]; rfl
  rw [key, hM (((G⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ι (x i))), mulVec_mulVec, mulVec_mulVec]
  simp only [Units.val_mul, Matrix.mul_assoc]
  rw [← Units.val_mul G G⁻¹, mul_inv_cancel, Units.val_one, Matrix.mul_one]
end Formalism.UG.P
