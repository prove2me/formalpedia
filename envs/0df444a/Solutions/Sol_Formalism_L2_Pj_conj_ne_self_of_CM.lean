-- Prove2me | solution 1 for Formalism.L2.Pj.conj_ne_self_of_CM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:16:20.920528+00:00
-- url     : https://prove2.me/submissions/9d31679f-6463-4a97-becd-c3bd4f57120c

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ConjNeSelfOfCM

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
open Formalism Formalism.L2 Formalism.L2.Pj
open MvPowerSeries NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} [StarRing (𝓞 E)]
omit [StarRing (𝓞 E)]
namespace Formalism.L2.Pj
theorem _root_.solution (τ : E →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := by
  haveI := NumberField.IsCMField.isTotallyComplex E
  intro hτ
  have hc := NumberField.IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk τ)
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex, NumberField.InfinitePlace.isReal_mk_iff] at hc
  exact hc hτ
end Formalism.L2.Pj
