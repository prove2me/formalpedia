-- Prove2me | solution 1 for Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore.C_mem_polyS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:44.126409+00:00
-- url     : https://prove2.me/submissions/ff5d7fe9-c095-423f-9674-a50c66449914

import Definitions.Def_Formalism_TruncatedSeriesCounting_LemmaDetPoly
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_LemmaDetPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical Polynomial
noncomputable section
open Formalism Formalism.TruncatedSeriesCounting Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
variable {R : Type*} [CommRing R] {G : Type*} [Monoid G] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
theorem _root_.solution {S : Subring R} {c : R} (hc : c ∈ S) : C c ∈ polyS S := by
  intro k
  show (C c).coeff k ∈ S
  rw [Polynomial.coeff_C]
  split_ifs
  · exact hc
  · exact S.zero_mem
end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
