-- Prove2me | solution 1 for Formalism.L2.Geo.Def.PC.stab_of_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:32:15.697559+00:00
-- url     : https://prove2.me/submissions/cfdc00cc-2b18-40b5-9e1c-3d33e469dd71

import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassD
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassE
import Theorems.Thm_Formalism_L2_Geo_Def_PC_lg
import Theorems.Thm_Formalism_L2_Geo_Def_PC_mem_stab_of
import Theorems.Thm_Formalism_L2_Geo_Def_PC_pr_mulVec
import Theorems.Thm_Formalism_L2_Geo_Def_PC_pr_lat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.PC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.L2.Geo.Def.PC
theorem _root_.solution (Λ : Submodule (𝓞 E) (n → E)) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (x : GL n 𝒜) (hx : ∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) x ∈ stabGL (latV v Λ)) :
    x ∈ stabGL (latA (F := F) Λ) := by
  have fwd : ∀ g : GL n 𝒜, (∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) g ∈ stabGL (latV v Λ)) →
      ∀ y ∈ latA (F := F) Λ, (g : Matrix n n 𝒜) *ᵥ y ∈ latA (F := F) Λ := by
    intro g hg y hy
    refine lg (F := F) Λ hspan _ fun v => ?_
    rw [pr_mulVec]
    have hgv : ∀ z : n → E ⊗[F] v.adicCompletion F, z ∈ latV v Λ ↔
        ((bc (prV (E := E) v) g : GL n (E ⊗[F] v.adicCompletion F)) :
          Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈ latV v Λ := hg v
    exact (hgv _).1 (pr_lat (F := F) v Λ y hy)
  refine mem_stab_of (latA (F := F) Λ) x (fwd x hx) (fwd x⁻¹ fun v => ?_)
  rw [map_inv]
  exact inv_mem (hx v)
end Formalism.L2.Geo.Def.PC
