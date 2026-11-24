-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.glob_companion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:31:19.127656+00:00
-- url     : https://prove2.me/submissions/f9f4a777-ec7c-4e32-a8d2-ea6c6a906892

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_MemHatMapGlob
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_ExistsUnitaryOneDetEq
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_glob_dl
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_glob_smul
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_glob_sup
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_isLat_smul


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
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.Comp
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E)
    (hJ : ∀ M : Submodule (𝓞 E) (n → E), IsLat M → IsLat (dl σ J M))
    {Λ : Submodule (𝓞 E) (n → E)} (hΛ : IsLat Λ) {a : 𝓞 E} (ha : a ≠ 0) (g : GL n 𝒜)
    (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    globLat g (Λ ⊔ Ideal.span {a} • dl σ J Λ) = globLat g Λ ⊔ Ideal.span {a} • dl σ J (globLat g Λ) := by
  rw [glob_sup hΛ (isLat_smul (hJ _ hΛ) ha), glob_smul (hJ _ hΛ) ha, glob_dl σ J hJ hΛ g hg]
end Formalism.L2.GlobalTheoryTheory.Comp
