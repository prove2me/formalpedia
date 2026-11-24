-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RestrictedDualKernel.pos_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:09.089282+00:00
-- url     : https://prove2.me/submissions/faa0a9eb-8b8b-47e3-bf6b-213d2f28c8d7

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictedDualKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RestrictedDualKernel
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix ComplexOrder
variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
namespace Formalism.FourierDecayAlt.P.RestrictedDualKernel
theorem _root_.solution {c u : ℂ} (hc : 0 < c) (hu : 0 ≤ u.re ∧ u.im = 0) : 0 ≤ (c * u).re ∧ (c * u).im = 0 := by
  obtain ⟨h1, h2⟩ := Complex.pos_iff.mp hc
  have hci : c.im = 0 := by linarith
  rw [Complex.mul_re, Complex.mul_im, hci, hu.2]
  constructor
  · nlinarith [hu.1]
  · ring
end Formalism.FourierDecayAlt.P.RestrictedDualKernel
