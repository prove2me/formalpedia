-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.smul_hat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:02:49.585864+00:00
-- url     : https://prove2.me/submissions/00f26089-e952-4e8d-bbcd-7e10684ba190

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
theorem _root_.solution (A : Submodule (𝓞 E) (n → E)) (a : 𝓞 E) (u : n → 𝒜) (hu : u ∈ hat F A) :
    ιA (a : E) • u ∈ hat F (Ideal.span {a} • A) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, rfl⟩ := hu
    refine Submodule.subset_span ⟨a • y, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hy, ?_⟩
    funext i
    show ιA ((a : E) * y i) = ιA (a : E) * ιA (y i)
    rw [map_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [smul_add]; exact add_mem hu hv
  | smul s u _ hu =>
    rw [smul_comm]
    exact Submodule.smul_mem _ s hu
end Formalism.L2.GlobalTheoryTheory.Comp
