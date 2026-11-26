-- Prove2me | solution 1 for EdenVerified.concave_interpolants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:00:51.963726+00:00
-- url     : https://prove2.me/submissions/d964d47a-111a-4d5d-bc8f-3feff0d9987d

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_concaveOn_log_singularValueFunction
import Theorems.Thm_Eden_concaveOn_lyapunovExponent_interpolation


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (p : PhaseSpace) :
    (∀ t : ℝ, 0 < t → ConcaveOn ℝ (Icc (0 : ℝ) 5) (fun d => Real.log
      (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t)) ∧
    ConcaveOn ℝ (Icc (0 : ℝ) 5) (spectrumInterpolation (lyapunovExponent c p)) :=
  ⟨fun _ ht => concaveOn_log_singularValueFunction c ht p,
    concaveOn_lyapunovExponent_interpolation c p⟩
end EdenVerified
