-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.mem_dl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:01.382902+00:00
-- url     : https://prove2.me/submissions/206dfccd-e6d8-4ad2-822f-5673a93fe7cb

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_hform_add_right
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_hform_smul_right
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_hform_zero_right

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
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) (y : n → E) :
    y ∈ dl σ J Λ ↔ ∀ x ∈ Λ, hform (σ : E →+* E) J x y ∈ (algebraMap (𝓞 E) E).range := by
  constructor
  · intro hy x hx
    induction hy using Submodule.span_induction with
    | mem y hy => exact hy x hx
    | zero => rw [hform_zero_right]; exact zero_mem _
    | add y z _ _ hy hz => rw [hform_add_right]; exact add_mem hy hz
    | smul a y _ hy =>
      rw [← algebraMap_smul E a y, hform_smul_right]
      exact mul_mem ⟨a, rfl⟩ hy
  · intro h
    exact Submodule.subset_span h
end Formalism.L2.GlobalTheoryTheory.Comp
