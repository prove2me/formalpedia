-- Prove2me | solution 1 for Formalism.DivisionValues.shift_smulLat_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:21.949814+00:00
-- url     : https://prove2.me/submissions/2c18e2c9-5c1d-40d5-8d3e-7e4b348d1fce

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
variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution (a : K) (ha : a ≠ 0) (N : Submodule (𝓞 K) (Fin d → K))
    (hN : Submodule.IsLattice K N) : Submodule.IsLattice K (smulLat a N) := by
  refine ⟨hN.fg.map _, ?_⟩
  have hset : ((smulLat a N : Submodule (𝓞 K) (Fin d → K)) : Set (Fin d → K)) =
      (LinearMap.lsmul K (Fin d → K) a) '' (N : Set (Fin d → K)) := by
    simp [smulLat]
  rw [hset, ← Submodule.map_span, hN.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  intro v
  exact ⟨a⁻¹ • v, by simp [smul_smul, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]⟩
end Formalism.DivisionValues
