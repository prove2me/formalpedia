-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.hform_hat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:02:21.493155+00:00
-- url     : https://prove2.me/submissions/d5c454e9-565e-4ca2-9c40-15fb6e974f64

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_hform_add_right
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_hform_smul_right
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_hform_zero_right
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_mem_dl
import Theorems.Thm_Formalism_UG_P_csDual_span


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
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) (u w : n → 𝒜)
    (hu : u ∈ hat F Λ) (hw : w ∈ hat F (dl σ J Λ)) :
    hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ιA) u w ∈ 𝒮 := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, rfl⟩ := hw
    exact csDual_span σ J Λ x ((mem_dl σ J Λ x).1 hx) u hu
  | zero => rw [hform_zero_right]; exact zero_mem _
  | add v w _ _ hv hw => rw [hform_add_right]; exact add_mem hv hw
  | smul s w _ hw =>
    rw [Subring.smul_def, hform_smul_right]
    exact mul_mem s.2 hw
end Formalism.L2.GlobalTheoryTheory.Comp
