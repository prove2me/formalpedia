-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.mem_hat_glob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:05:24.426142+00:00
-- url     : https://prove2.me/submissions/8e9f2f61-52fb-4e7d-ac3e-a030ea2d177c

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Theorems.Thm_Formalism_UG_P_csGlob_intAdApprox
import Theorems.Thm_Formalism_UG_P_span_recovery_of_integral_adelic_approx


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
theorem _root_.solution {Λ : Submodule (𝓞 E) (n → E)} (h : IsLat Λ) (g : GL n 𝒜) (u : n → 𝒜) :
    u ∈ hat F (globLat g Λ) ↔ ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F Λ :=
  span_recovery_of_integral_adelic_approx csGlob_intAdApprox F E n Λ h.1 h.2 g u
end Formalism.L2.GlobalTheoryTheory.Comp
