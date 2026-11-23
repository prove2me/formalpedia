-- Prove2me | solution 1 for Formalism.UG.P.satake_Tj_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:08.0336+00:00
-- url     : https://prove2.me/submissions/b2455534-faae-4df2-93f4-9fc731e723f2

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
import Theorems.Thm_Formalism_UG_P_satake_Tj_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (k : Type) [CommRing k] [Nontrivial k] (ϖ : v.adicCompletion F) (j : ℕ)
    (g : GL (Fin n) (v.adicCompletion F)) :
    Tj k n (Ov F v) ϖ j g ≠ 0 ↔ g ∈ satakeTset v ϖ j := by
  rw [satake_Tj_eq]
  by_cases h : g ∈ satakeTset v ϖ j
  · rw [Set.indicator_of_mem h]; simp [h]
  · rw [Set.indicator_of_notMem h]; simp [h]
end Formalism.UG.P
