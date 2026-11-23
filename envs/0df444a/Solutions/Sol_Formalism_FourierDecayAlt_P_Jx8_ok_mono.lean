-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.ok_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:29.467017+00:00
-- url     : https://prove2.me/submissions/7713496c-672b-4dea-9f9d-c444b6a12f45

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution {E α : Type} [Field E] {S : LocSys E α} {F G : Finset α} (h : F ⊆ G) (hS : S.Ok G) :
    S.Ok F := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  exact ⟨fun t t' ht ht' x hx y hy => h1 t t' ht ht' x (h hx) y (h hy), fun t ht => psd_mono h (h2 t ht),
    fun t t' htt x hx y hy => h3 t t' htt x (h hx) y (h hy), fun t => psd_mono h (h4 t),
    fun t ht => psd_mono h (h5 t ht), fun R hR => psd_mono h (h6 R hR)⟩
end Formalism.FourierDecayAlt.P.Jx8
