-- Prove2me | solution 1 for Formalism.DivisionValues.StepBAux.hcompl_le_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:44.136924+00:00
-- url     : https://prove2.me/submissions/bd3e7087-44fd-427b-9748-3ad5debfd168

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.StepBAux
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.StepBAux
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) :
    Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal ≤ (conjPl w).asIdeal.primeCompl := by
  unfold Formalism.HermitianLatticesTheory.hcompl
  rw [Submonoid.closure_le]
  intro s hs
  show s ∉ (conjPl w).asIdeal
  intro hsc
  obtain ⟨u, hu, hus⟩ := (Ideal.mem_map_of_equiv (cO K) s).mp hsc
  apply hs.2 u _ hu
  rw [← hus]
  show (u : K) = star (star (u : K))
  rw [star_star]
end Formalism.DivisionValues.StepBAux
