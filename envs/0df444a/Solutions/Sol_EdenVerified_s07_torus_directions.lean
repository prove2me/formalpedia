-- Prove2me | solution 1 for EdenVerified.s07_torus_directions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:58:11.303454+00:00
-- url     : https://prove2.me/submissions/f134c395-457a-48e2-b86f-112b3048117b

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_norm_fderiv_torus_directions
import Theorems.Thm_Eden_radialOrthonormalBasis_on_torus
import Theorems.Thm_Eden_tendsto_torus_direction_growth
import Theorems.Thm_Eden_torus_direction_rates_and_ordered_exponents


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) (p : PhaseSpace) (hp : p ∈ torus) :
    (fun i => radialOrthonormalBasis p i) =
      ![!₂[p 0, p 1, 0, 0, 0], !₂[-p 1, p 0, 0, 0, 0],
        !₂[0, 0, p 2, p 3, 0], !₂[0, 0, -p 3, p 2, 0], !₂[0, 0, 0, 0, 1]] ∧
    (∀ t : ℝ, 0 ≤ t → ∀ i : Fin 5,
      ‖fderiv ℝ (evolution c t) p (radialOrthonormalBasis p i)‖ =
        Real.exp ((![2, 0, 2, 0, -c] : Fin 5 → ℝ) i*t)) ∧
    (∀ i : Fin 5, Tendsto (fun t : ℝ => Real.log
      ‖fderiv ℝ (evolution c t) p (radialOrthonormalBasis p i)‖ / t) atTop
      (𝓝 ((![2, 0, 2, 0, -c] : Fin 5 → ℝ) i))) ∧
    lyapunovExponent c p = ![2, 2, 0, 0, -c] ∧ 0 < (2 : ℝ) ∧ -c < 0 :=
  ⟨radialOrthonormalBasis_on_torus hp,
    fun t ht i => norm_fderiv_torus_directions c ht hp i,
    tendsto_torus_direction_growth c hp, torus_direction_rates_and_ordered_exponents hc hp⟩
end EdenVerified
