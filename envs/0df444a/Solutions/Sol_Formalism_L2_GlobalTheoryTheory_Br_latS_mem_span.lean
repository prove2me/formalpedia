-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Br.latS_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:18:40.982706+00:00
-- url     : https://prove2.me/submissions/825e66fd-c41d-4f66-9e1c-8e158ec53a53

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_BlockActions_LatSOfMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_BlockActions_FiniteAdeleRingNontrivial
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Br_latS_functional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Br
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.Br
theorem _root_.solution (Λ : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (hx : (fun i => ι (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) :
    x ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
  by_contra hxV
  obtain ⟨f, hfx, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxV inferInstance
  refine hfx (latS_functional (F := F) Λ f (fun y hy => ?_) x hx)
  have h2 : f y ∈ (Submodule.span E (Λ : Set (Fin n → E))).map f :=
    Submodule.mem_map_of_mem (Submodule.subset_span hy)
  rw [hf] at h2
  exact (Submodule.mem_bot E).1 h2
end Formalism.L2.GlobalTheoryTheory.Br
