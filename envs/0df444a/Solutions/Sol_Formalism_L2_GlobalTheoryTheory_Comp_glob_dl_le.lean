-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.glob_dl_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:32:13.897503+00:00
-- url     : https://prove2.me/submissions/11a1c195-d623-4a6f-b47b-86e973c01ab8

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_mem_dl
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_hform_hat
import Theorems.Thm_Formalism_UG_P_csDual_hform_incl
import Theorems.Thm_Formalism_UG_P_csGlob_int
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
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Comp
open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.Comp
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) (g : GL n 𝒜)
    (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) : globLat g (dl σ J Λ) ≤ dl σ J (globLat g Λ) := by
  intro x hx
  rw [mem_dl]
  intro y hy
  have h1 := hform_hat σ J Λ _ _ hy hx
  have hg' : g⁻¹ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := inv_mem hg
  have h2 : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) * J.map ιA *
      ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) = J.map ιA := hg'
  rw [hform_mulVec, h2, csDual_hform_incl] at h1
  have h3 := csGlob_int (F := F) _ h1
  exact ⟨⟨_, h3⟩, rfl⟩
end Formalism.L2.GlobalTheoryTheory.Comp
