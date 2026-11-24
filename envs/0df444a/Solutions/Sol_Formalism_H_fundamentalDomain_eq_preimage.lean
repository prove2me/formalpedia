-- Prove2me | solution 1 for Formalism.H.fundamentalDomain_eq_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:05.65619+00:00
-- url     : https://prove2.me/submissions/3169db23-a468-489d-a198-5b04cbdfb447

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_FundamentalDomainEqPreimage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]
namespace Formalism.H
theorem _root_.solution (e : Module.Basis ι ℝ V) :
    ZSpan.fundamentalDomain e = e.equivFunL ⁻¹' boxIco ι := by
  ext x
  simp [ZSpan.mem_fundamentalDomain, boxIco, Set.mem_pi]
end Formalism.H
