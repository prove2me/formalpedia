-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.DescP.coe_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:40:59.648975+00:00
-- url     : https://prove2.me/submissions/7c116195-f89b-45f1-8ed4-91df71edcf08

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescJet

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
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.DescP
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {n d : ℕ}
namespace Formalism.L2.FormalSeriesBounds.DescP
theorem _root_.solution (p : MvPolynomial (Fin n × Fin d) k) :
    (p : PS k n d) = ∑ μ ∈ p.support, MvPolynomial.coeff μ p • monomial μ (1 : k) := by
  ext ν
  rw [MvPolynomial.coeff_coe, map_sum]
  simp only [map_smul, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · simpa using h
end Formalism.L2.FormalSeriesBounds.DescP
