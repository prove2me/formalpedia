-- Prove2me | solution 1 for Formalism.UG.P.csGlob_tmul_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:11:55.806198+00:00
-- url     : https://prove2.me/submissions/7db43852-e1c5-409f-b5fb-8911ac6bdeb0

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlobApprox
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob

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
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.UG.P
theorem _root_.solution (x : E) (ρ : 𝓞 F) :
    x ⊗ₜ[F] algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) ρ = ι (algebraMap (𝓞 F) E ρ * x) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F),
    IsScalarTower.algebraMap_apply (𝓞 F) F E,
    Algebra.algebraMap_eq_smul_one (A := FiniteAdeleRing (𝓞 F) F), ← TensorProduct.smul_tmul,
    ← Algebra.smul_def]
  rfl
end Formalism.UG.P
