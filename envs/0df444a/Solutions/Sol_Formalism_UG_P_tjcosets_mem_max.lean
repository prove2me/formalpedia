-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_mem_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:40:56.244303+00:00
-- url     : https://prove2.me/submissions/491c63c8-6529-49f5-9d57-2716b8d94590

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped WithZero
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution (x : Ov F v) :
    IsLocalRing.residue (Ov F v) x = 0 ↔ Valued.v (x : v.adicCompletion F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  refine (ValuationSubring.valuation_lt_one_iff (v.adicCompletionIntegers F) x).trans ?_
  have e := (Valuation.isEquiv_valuation_valuationSubring
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).lt_iff_lt (x := (x : v.adicCompletion F)) (y := 1)
  rw [map_one, map_one] at e
  exact e.symm
end Formalism.UG.P
