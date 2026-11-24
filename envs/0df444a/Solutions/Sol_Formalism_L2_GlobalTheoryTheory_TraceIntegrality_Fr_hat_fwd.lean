-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.hat_fwd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:10:38.11588+00:00
-- url     : https://prove2.me/submissions/9b7107a9-ab44-48c4-9f50-aa4e0ae42c7c

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL4_PFrCore
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_vi_mem_hat
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_gmv

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
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.TraceIntegrality Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
theorem _root_.solution (G : Matrix n n E) {Λ Λ' : Submodule (𝓞 E) (n → E)} (h : ∀ x ∈ Λ, G *ᵥ x ∈ Λ')
    (u : n → 𝒜) (hu : u ∈ hat F Λ) : (G.map ιA) *ᵥ u ∈ hat F Λ' := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    show G.map ιA *ᵥ vi F x ∈ _
    rw [gmv]
    exact vi_mem_hat (h x hx)
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [mulVec_add]; exact add_mem hu hw
  | smul s u _ hu =>
    rw [Subring.smul_def, mulVec_smul]
    exact Submodule.smul_mem _ s hu
end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
