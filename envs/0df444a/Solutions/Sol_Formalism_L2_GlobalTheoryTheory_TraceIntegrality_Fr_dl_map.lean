-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.dl_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:52:45.607847+00:00
-- url     : https://prove2.me/submissions/48ecfaf1-4496-425b-bf59-00442f7698f4

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL4_PFrCore
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_mem_dl
import Theorems.Thm_Formalism_UG_P_hform_mulVec


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
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.TraceIntegrality Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E) (G : GL n E) (hG : G ∈ UJ (σ : E →+* E) J)
    {Λ Λ' : Submodule (𝓞 E) (n → E)} (h : ∀ x, x ∈ Λ ↔ (G : Matrix n n E) *ᵥ x ∈ Λ') :
    ∀ x ∈ dl σ J Λ, (G : Matrix n n E) *ᵥ x ∈ dl σ J Λ' := by
  intro x hx
  rw [mem_dl] at hx ⊢
  intro x' hx'
  have hG' : cT (σ : E →+* E) (G : Matrix n n E) * J * (G : Matrix n n E) = J := hG
  have h1 : ((G⁻¹ : GL n E) : Matrix n n E) *ᵥ x' ∈ Λ := by
    refine (h _).2 ?_
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    exact hx'
  have h2 := hx _ h1
  have h3 : x' = (G : Matrix n n E) *ᵥ (((G⁻¹ : GL n E) : Matrix n n E) *ᵥ x') := by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  rw [h3, hform_mulVec, hG']
  exact h2
end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
