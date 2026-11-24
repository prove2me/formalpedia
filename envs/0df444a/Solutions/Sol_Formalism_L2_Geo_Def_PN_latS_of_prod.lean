-- Prove2me | solution 1 for Formalism.L2.Geo.Def.PN.latS_of_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:26:41.113637+00:00
-- url     : https://prove2.me/submissions/6e9a98d3-2650-4c38-8d89-aa264c578046

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PNeatB
import Theorems.Thm_Formalism_L2_Geo_Def_PN_IE_latS
import Theorems.Thm_Formalism_UG_P_afsplit_decomp
import Theorems.Thm_Formalism_UG_P_afsplit_prV_eps_ne


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
theorem _root_.solution (Λ : Submodule (𝓞 E) (n → E)) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ∀ w : n → 𝒜, (∀ v ∈ T, (fun i => prV (E := E) v (w i)) ∈ latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ) →
    (fun i => (∏ v ∈ T, (1 - afsplitEps E v)) * w i) ∈ latS (F := F) 𝔸 𝒮 Λ →
    w ∈ latS (F := F) 𝔸 𝒮 Λ := by
  classical
  induction T using Finset.induction_on with
  | empty => intro w _ h; simpa using h
  | insert v T hv ih =>
    intro w hloc h
    have h1 : (fun i => (1 - afsplitEps E v) * w i) ∈ latS (F := F) 𝔸 𝒮 Λ := by
      apply ih
      · intro u hu
        have huv : u ≠ v := fun e => hv (e ▸ hu)
        have : (fun i => prV (E := E) u ((1 - afsplitEps E v) * w i)) =
            (fun i => prV (E := E) u (w i)) := by
          ext i
          rw [map_mul, map_sub, map_one, afsplit_prV_eps_ne v u huv, sub_zero, one_mul]
        rw [this]
        exact hloc u (Finset.mem_insert_of_mem hu)
      · have : (fun i => (∏ v ∈ T, (1 - afsplitEps E v)) * ((1 - afsplitEps E v) * w i)) =
            (fun i => (∏ v ∈ insert v T, (1 - afsplitEps E v)) * w i) := by
          ext i
          rw [Finset.prod_insert hv]; ring
        rw [this]; exact h
    have h2 := IE_latS Λ v (hloc v (Finset.mem_insert_self v T))
    have : w = (fun i => afsplitIE v (prV (E := E) v (w i))) + (fun i => (1 - afsplitEps E v) * w i) := by
      ext i
      rw [Pi.add_apply, afsplit_decomp]; ring
    rw [this]; exact add_mem h2 h1
end Formalism.L2.Geo.Def.PN
