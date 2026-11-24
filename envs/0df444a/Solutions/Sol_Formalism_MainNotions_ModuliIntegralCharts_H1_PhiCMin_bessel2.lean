-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.bessel2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:47:54.416149+00:00
-- url     : https://prove2.me/submissions/a8b16371-59cb-4ee5-87fc-602dd38f63c7

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinE

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
open Matrix
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
theorem _root_.solution {d : ℕ} (v p q : Fin d → ℝ) (hv : v ⬝ᵥ v = 1) (hp : p ⬝ᵥ p = 1)
    (hpq : p ⬝ᵥ q = 0) (hq : 0 < q ⬝ᵥ q) :
    (v ⬝ᵥ p) ^ 2 * (q ⬝ᵥ q) + (v ⬝ᵥ q) ^ 2 ≤ q ⬝ᵥ q := by
  have hr : 0 ≤ ((q ⬝ᵥ q) • v - ((q ⬝ᵥ q) * (v ⬝ᵥ p)) • p - (v ⬝ᵥ q) • q) ⬝ᵥ
      ((q ⬝ᵥ q) • v - ((q ⬝ᵥ q) * (v ⬝ᵥ p)) • p - (v ⬝ᵥ q) • q) := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hqp : q ⬝ᵥ p = 0 := by rw [dotProduct_comm]; exact hpq
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm p v, dotProduct_comm q v, hv, hp, hpq, hqp] at hr
  nlinarith [hr, hq]
end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
