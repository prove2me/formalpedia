-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.isLat_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:24.026156+00:00
-- url     : https://prove2.me/submissions/83a97ae5-d3db-459a-acf8-2f92052f525c

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat

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
theorem _root_.solution {A : Submodule (𝓞 E) (n → E)} (hA : IsLat A) {a : 𝓞 E} (ha : a ≠ 0) :
    IsLat (Ideal.span {a} • A) := by
  refine ⟨Module.Finite.iff_fg.2 (Submodule.FG.smul (Submodule.fg_span_singleton a) (Module.Finite.iff_fg.1 hA.1)), ?_⟩
  rw [eq_top_iff, ← hA.2, Submodule.span_le]
  intro x hx
  have h1 : a • x ∈ Ideal.span {a} • A := Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hx
  have h2 : (a : E) ≠ 0 := fun h => ha (RingOfIntegers.ext h)
  have h3 : x = (a : E)⁻¹ • (a • x) := by
    rw [← algebraMap_smul E a x, smul_smul]
    show x = ((a : E)⁻¹ * (a : E)) • x
    rw [inv_mul_cancel₀ h2, one_smul]
  rw [h3]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
end Formalism.L2.GlobalTheoryTheory.Comp
