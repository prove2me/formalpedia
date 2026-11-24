-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.glob_dl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:08:00.459801+00:00
-- url     : https://prove2.me/submissions/b3e437dd-6823-4bc6-a864-a0371ea08921

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_glob_mono
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_isLat_glob
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_glob_inv_glob
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_glob_glob_inv
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_glob_dl_le

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
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E)
    (hJ : ∀ M : Submodule (𝓞 E) (n → E), IsLat M → IsLat (dl σ J M))
    {Λ : Submodule (𝓞 E) (n → E)} (hΛ : IsLat Λ) (g : GL n 𝒜)
    (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) : globLat g (dl σ J Λ) = dl σ J (globLat g Λ) := by
  apply le_antisymm (glob_dl_le σ J Λ g hg)
  have h1 := glob_dl_le σ J (globLat g Λ) g⁻¹ (inv_mem hg)
  rw [glob_glob_inv hΛ] at h1
  have h2 := glob_mono g h1
  rwa [glob_inv_glob (hJ _ (isLat_glob hΛ g))] at h2
end Formalism.L2.GlobalTheoryTheory.Comp
