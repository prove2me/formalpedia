-- Prove2me | solution 1 for Eden.concaveOn_lyapunovExponent_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:21:26.525301+00:00
-- url     : https://prove2.me/submissions/641f7f02-1c08-454a-8a78-260021e286f3

import Definitions.Def_Eden_LogarithmicInterpolation
import Mathlib.Analysis.Convex.Function
import Definitions.Def_Eden_InterpolationConcavity
import Theorems.Thm_Eden_concaveOn_spectrumInterpolation
import Theorems.Thm_Eden_lyapunovExponent_antitone


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) :
    ConcaveOn ℝ (Icc (0 : ℝ) 5) (spectrumInterpolation (lyapunovExponent c p)) :=
  concaveOn_spectrumInterpolation (lyapunovExponent_antitone c p)
end Eden
