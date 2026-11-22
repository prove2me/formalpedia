-- Prove2me | solution 1 for Formalism.DivisionValues.shift_above_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:51:19.256031+00:00
-- url     : https://prove2.me/submissions/e1e512b2-492c-4ef6-aa2e-317c79d32462

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TwistedLatticeNaturality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues
theorem _root_.solution (p : ℕ) (hp : p.Prime) (w : HeightOneSpectrum (𝓞 K)) :
    Above p w ↔ 0 < vw w (p : K) := by
  have hp0 : (p : 𝓞 K) ≠ 0 := by
    first
    | exact Nat.cast_ne_zero.mpr hp.ne_zero
    | intro h
      have h' : ((p : 𝓞 K) : K) = 0 := by rw [h]; simp
      have h'' : (p : K) = 0 := by simpa using h'
      exact hp.ne_zero (by exact_mod_cast h'')
  have hI : Ideal.span {(p : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hp0
  have hv : vw w (p : K) =
      ((Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {(p : 𝓞 K)})).factors : ℤ) := by
    rw [← FractionalIdeal.count_coe K w hI, FractionalIdeal.coeIdeal_span_singleton]
    simp [vw]
  show (p : 𝓞 K) ∈ w.asIdeal ↔ _
  rw [hv, ← Ideal.dvd_span_singleton, ← Associates.count_ne_zero_iff_dvd hI w.irreducible]
  omega
end Formalism.DivisionValues
