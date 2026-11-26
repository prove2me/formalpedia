-- Prove2me | solution 1 for EdenVerified.D10_actual_exponents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:02:31.304764+00:00
-- url     : https://prove2.me/submissions/4a575567-9c98-4b9c-89de-3995e9d706cf

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_lyapunovExponent_antitone
import Theorems.Thm_Eden_tendsto_lyapunovExponent


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (p : PhaseSpace) :
    Antitone (lyapunovExponent c p) ∧
    (∀ i : Fin 5, Tendsto (fun t : ℝ => Real.log
      ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) / t)
      atTop (𝓝 (lyapunovExponent c p i))) ∧
    asymptoticDimension c p = kaplanYorkeDimension (lyapunovExponent c p) :=
  ⟨lyapunovExponent_antitone c p, tendsto_lyapunovExponent c p, rfl⟩
end EdenVerified
