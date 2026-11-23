-- Prove2me | solution 1 for Formalism.UG.P.csDual_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:17.358056+00:00
-- url     : https://prove2.me/submissions/218bbacd-21f6-4cc9-aaa0-640b36634713

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual

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
theorem _root_.solution (M : Matrix n n E) (v : n → 𝒜) (a b : 𝒜) (k : n) :
    a * b * ((M.map ι) *ᵥ v) k = ∑ i, (b * ι (M k i)) * (a * v i) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
end Formalism.UG.P
