-- Prove2me | solution 1 for Formalism.UG.P.csGlob_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:15:22.575681+00:00
-- url     : https://prove2.me/submissions/cb909764-6db7-491b-9bb1-ca2cb743ca27

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlobApprox
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Theorems.Thm_Formalism_UG_P_csGlob_eq
import Theorems.Thm_Formalism_UG_P_adelstabL_lower
import Theorems.Thm_Formalism_UG_P_adelstabL_upper
import Theorems.Thm_Formalism_UG_P_adelstab_entries
import Theorems.Thm_Formalism_UG_P_adelstab_finite
import Theorems.Thm_Formalism_UG_P_adelstab_span
import Theorems.Thm_Formalism_UG_P_levelaf_exists_denom


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
theorem _root_.solution (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (g : GL n 𝒜) :
    Submodule.IsLattice E (Formalism.UG.CS.globLat g Λ) := by
  obtain ⟨c₁, hc₁, h₁⟩ := adelstabL_lower (F := F) Λ hspan
  obtain ⟨c₂, hc₂, h₂⟩ := adelstabL_upper (F := F) Λ hfin
  obtain ⟨d, hd, c, hc, hcg, hcgi⟩ := levelaf_exists_denom (E := E) g
  have hG := adelstab_entries g d c hc hcg
  have hGi := adelstab_entries g⁻¹ d c hc hcgi
  have hf := adelstab_finite g _ c₂ d hc₂ hd h₂ hG
  have hs := adelstab_span g _ c₁ d hc₁ hd h₁ hGi
  rw [csGlob_eq]
  exact ⟨Module.Finite.iff_fg.mp hf, hs⟩
end Formalism.UG.P
