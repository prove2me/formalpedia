-- Prove2me | solution 1 for Formalism.L2.Geo.Def.PN.prV_latS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:10:56.967326+00:00
-- url     : https://prove2.me/submissions/5235faff-68fb-493c-a871-d375e4d4b4b6

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PNeatB
import Theorems.Thm_Formalism_L2_Geo_Def_PN_latS_mul_mem
import Theorems.Thm_Formalism_UG_P_afsplit_prV_int


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
theorem _root_.solution (Λ : Submodule (𝓞 E) (n → E)) (v : HeightOneSpectrum (𝓞 F)) {u : n → 𝒜}
    (hu : u ∈ latS (F := F) 𝔸 𝒮 Λ) :
    (fun i => prV (E := E) v (u i)) ∈ latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    have : (fun i => prV (E := E) v ((0 : n → 𝒜) i)) = 0 := by ext i; simp
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : (fun i => prV (E := E) v ((a + b) i)) =
        (fun i => prV (E := E) v (a i)) + (fun i => prV (E := E) v (b i)) := by
      ext i; simp
    rw [this]; exact add_mem ha hb
  | smul s a _ ha =>
    have : (fun i => prV (E := E) v ((s • a) i)) =
        (fun i => prV (E := E) v (s : 𝒜) * prV (E := E) v (a i)) := by
      ext i; rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
    rw [this]; exact latS_mul_mem _ Λ (afsplit_prV_int v _ s.2) ha
end Formalism.L2.Geo.Def.PN
