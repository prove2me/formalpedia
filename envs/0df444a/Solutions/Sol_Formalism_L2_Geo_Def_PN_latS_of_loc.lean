-- Prove2me | solution 1 for Formalism.L2.Geo.Def.PN.latS_of_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:28:26.83779+00:00
-- url     : https://prove2.me/submissions/4dd5e83b-7414-4bd7-ad45-072e6ed077e8

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PNeatB
import Theorems.Thm_Formalism_L2_Geo_Def_PN_latS_mul_mem
import Theorems.Thm_Formalism_L2_Geo_Def_PN_latS_of_prod
import Theorems.Thm_Formalism_L2_Geo_Def_PN_prod_eps_eq
import Theorems.Thm_Formalism_UG_P_adelstabL_lower
import Theorems.Thm_Formalism_UG_P_levelafC_mem
import Theorems.Thm_Formalism_UG_P_levelafC_mul
import Theorems.Thm_Formalism_UG_P_levelaf_denom
import Theorems.Thm_Formalism_UG_P_levelaf_finite_places


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
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.PN
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.L2.Geo.Def.PN
theorem _root_.solution (Λ : Submodule (𝓞 E) (n → E)) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (w : n → 𝒜) (hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      (fun i => prV (E := E) v (w i)) ∈ latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ) :
    w ∈ latS (F := F) 𝔸 𝒮 Λ := by
  classical
  choose d0 hd0 hd0m using fun i => levelaf_denom (F := F) (E := E) (w i)
  obtain ⟨c, hc, hcm⟩ := adelstabL_lower (F := F) Λ hspan
  have h1 : ∀ i, levelafC E (∏ j, d0 j) * w i ∈ 𝒮 := by
    intro i
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm (d0 i), levelafC_mul, mul_assoc]
    exact mul_mem (levelafC_mem _) (hd0m i)
  have h2 := hcm _ h1
  have hd : c * ∏ j, d0 j ≠ 0 := mul_ne_zero hc (Finset.prod_ne_zero_iff.2 fun j _ => hd0 j)
  obtain ⟨a, ha, hae⟩ := prod_eps_eq (E := E) _ hd
  refine latS_of_prod Λ (levelaf_finite_places _ hd).toFinset w (fun v _ => hloc v) ?_
  rw [hae]
  have ha' : (1 : E) ⊗ₜ[F] a ∈ 𝒮 := Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  have := latS_mul_mem _ Λ ha' h2
  convert this using 2
  rw [levelafC_mul]; ring
end Formalism.L2.Geo.Def.PN
