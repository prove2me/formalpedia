-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.smul_glob_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:12:18.084051+00:00
-- url     : https://prove2.me/submissions/ada74a0d-a864-45a0-8e7c-def28e7d7045

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_smul_hat

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
theorem _root_.solution (A : Submodule (𝓞 E) (n → E)) (a : 𝓞 E) (g : GL n 𝒜) :
    Ideal.span {a} • globLat g A ≤ globLat g (Ideal.span {a} • A) := by
  rw [Submodule.smul_le]
  intro r hr x hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hr
  rw [mul_comm, mul_smul]
  refine Submodule.smul_mem _ c ?_
  show ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA ((a • x) i)) ∈ hat F (Ideal.span {a} • A)
  have h1 : (fun i => ιA ((a • x) i)) = ιA (a : E) • (fun i => ιA (x i)) := by
    funext i
    show ιA ((a : E) * x i) = ιA (a : E) * ιA (x i)
    rw [map_mul]
  rw [h1, mulVec_smul]
  exact smul_hat A a _ hx
end Formalism.L2.GlobalTheoryTheory.Comp
