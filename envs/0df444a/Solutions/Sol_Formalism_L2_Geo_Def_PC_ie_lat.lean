-- Prove2me | solution 1 for Formalism.L2.Geo.Def.PC.ie_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:55:22.267045+00:00
-- url     : https://prove2.me/submissions/903b11a1-efde-4e66-aac1-b928798be6fa

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassD
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
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.PC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.L2.Geo.Def.PC
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E))
    (u : n → E ⊗[F] v.adicCompletion F) (hu : u ∈ latV v Λ) :
    (fun i => afsplitIE v (u i)) ∈ latA (F := F) Λ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    have : (fun i => afsplitIE v (inclE (F := F) (v.adicCompletion F) (x i))) =
        (⟨afsplitEps E v, afsplit_eps_int v⟩ : 𝒮) • (fun i => inclE (F := F) 𝔸 (x i)) := by
      ext i
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      rw [← afsplit_decomp, afsplit_prV_inclE]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
  | zero =>
    have : (fun i => afsplitIE v ((0 : n → E ⊗[F] v.adicCompletion F) i)) = 0 := by ext i; simp
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : (fun i => afsplitIE v ((a + b) i)) =
        (fun i => afsplitIE v (a i)) + (fun i => afsplitIE v (b i)) := by ext i; simp
    rw [this]; exact add_mem ha hb
  | smul s a _ ha =>
    have : (fun i => afsplitIE v ((s • a) i)) =
        (⟨afsplitIE v (s : E ⊗[F] v.adicCompletion F), afsplit_IE_int v _ s.2⟩ : 𝒮) •
          (fun i => afsplitIE v (a i)) := by
      ext i
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
    rw [this]; exact Submodule.smul_mem _ _ ha
end Formalism.L2.Geo.Def.PC
