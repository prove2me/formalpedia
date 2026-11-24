-- Prove2me | solution 1 for Formalism.L2.Geo.Def.PC.pr_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:54:12.878477+00:00
-- url     : https://prove2.me/submissions/62ec3ea4-c34c-4d2e-b20d-e0ee3ff02730

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassD
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
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.PC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.L2.Geo.Def.PC
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E)) (y : n → 𝒜)
    (hy : y ∈ latA (F := F) Λ) : (fun i => prV (E := E) v (y i)) ∈ latV v Λ := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    have : (fun i => prV (E := E) v ((0 : n → 𝒜) i)) = 0 := by ext i; simp
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : (fun i => prV (E := E) v ((a + b) i)) =
        (fun i => prV (E := E) v (a i)) + (fun i => prV (E := E) v (b i)) := by ext i; simp
    rw [this]; exact add_mem ha hb
  | smul s a _ ha =>
    have : (fun i => prV (E := E) v ((s • a) i)) =
        (⟨prV (E := E) v (s : 𝒜), afsplit_prV_int v _ s.2⟩ : SV E v) • (fun i => prV (E := E) v (a i)) := by
      ext i
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
    rw [this]; exact Submodule.smul_mem _ _ ha
end Formalism.L2.Geo.Def.PC
