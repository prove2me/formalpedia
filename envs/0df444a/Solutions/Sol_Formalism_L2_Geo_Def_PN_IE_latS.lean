-- Prove2me | solution 1 for Formalism.L2.Geo.Def.PN.IE_latS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:09:36.386256+00:00
-- url     : https://prove2.me/submissions/7c4868f5-405f-4c08-a693-d2abe3b039cb

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PNeatB
import Theorems.Thm_Formalism_L2_Geo_Def_PN_latS_mul_mem
import Theorems.Thm_Formalism_UG_P_afsplit_IE_int
import Theorems.Thm_Formalism_UG_P_afsplit_decomp
import Theorems.Thm_Formalism_UG_P_afsplit_eps_int
import Theorems.Thm_Formalism_UG_P_afsplit_prV_inclE


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
theorem _root_.solution (Λ : Submodule (𝓞 E) (n → E)) (v : HeightOneSpectrum (𝓞 F))
    {h : n → E ⊗[F] v.adicCompletion F}
    (hh : h ∈ latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ) :
    (fun i => afsplitIE v (h i)) ∈ latS (F := F) 𝔸 𝒮 Λ := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨x, hx, rfl⟩ := hh
    have : (fun i => afsplitIE v (inclE (F := F) (v.adicCompletion F) (x i))) =
        (fun i => afsplitEps E v * inclE (F := F) 𝔸 (x i)) := by
      ext i
      rw [← afsplit_decomp, afsplit_prV_inclE]
    rw [this]
    exact latS_mul_mem _ Λ (afsplit_eps_int v) (Submodule.subset_span ⟨x, hx, rfl⟩)
  | zero =>
    have : (fun i => afsplitIE v ((0 : n → E ⊗[F] v.adicCompletion F) i)) = 0 := by ext i; simp
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : (fun i => afsplitIE v ((a + b) i)) =
        (fun i => afsplitIE v (a i)) + (fun i => afsplitIE v (b i)) := by
      ext i; simp
    rw [this]; exact add_mem ha hb
  | smul s a _ ha =>
    have : (fun i => afsplitIE v ((s • a) i)) =
        (fun i => afsplitIE v (s : E ⊗[F] v.adicCompletion F) * afsplitIE v (a i)) := by
      ext i; rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
    rw [this]; exact latS_mul_mem _ Λ (afsplit_IE_int v _ s.2) ha
end Formalism.L2.Geo.Def.PN
