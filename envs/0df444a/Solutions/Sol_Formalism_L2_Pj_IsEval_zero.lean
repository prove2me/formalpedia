-- Prove2me | solution 1 for Formalism.L2.Pj.IsEval.zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:46.76995+00:00
-- url     : https://prove2.me/submissions/f4309eb2-0eb6-4ee2-bd66-66a6a3e2b071

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open scoped WithZero
open Formalism Formalism.L2 Formalism.L2.Pj
attribute [instance] CDVR.cr CDVR.dom CDVR.dvr CDVR.cpl CDVR.ch0
variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K]
variable {la : HeightOneSpectrum R} {V : Type} {K' : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Field K'] [Algebra V K'] [IsFractionRing V K']
namespace Formalism.L2.Pj
namespace IsEval
theorem _root_.solution {W : Type} {Cusp : W → Type} [∀ w, AddCommGroup (Cusp w)] [∀ w, Module K (Cusp w)]
    {wadd : W → W → W} {mulC : ∀ w w', Cusp w → Cusp w' → Cusp (wadd w w')} {F : Type} [Field F]
    {ι : K →+* F} {ev : ∀ w, Cusp w → F} (h : IsEval wadd mulC ι ev) (w : W) : ev w 0 = 0 := by
  have := h.smul w 0 0
  rwa [zero_smul, map_zero, zero_mul] at this
end IsEval
end Formalism.L2.Pj
