-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B1.polar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:34:24.862792+00:00
-- url     : https://prove2.me/submissions/827c2875-58f5-451c-9ebf-a6ef88d5dbfe

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B1
theorem _root_.solution : Polarisation := by
  intro V _ _ W β γ hβ hγ hW x hx y hy
  obtain ⟨ba1, ba2, bs1, bs2⟩ := hβ
  obtain ⟨ga1, ga2, gs1, gs2⟩ := hγ
  have hxy := hW (x + y) (W.add_mem hx hy)
  have hxiy := hW (x + Complex.I • y) (W.add_mem hx (W.smul_mem _ hy))
  have hxx := hW x hx
  have hyy := hW y hy
  simp only [ba1, ba2, ga1, ga2] at hxy
  simp only [ba1, ba2, bs1, bs2, ga1, ga2, gs1, gs2, Complex.conj_I] at hxiy
  linear_combination (1 / 2 : ℂ) * (hxy - hxx - hyy) +
    (Complex.I / 2) * (hxiy - hxx + Complex.I ^ 2 * hyy) -
    ((β y x - γ y x - (β x y - γ x y)) / 2) * Complex.I_sq
end Formalism.FourierDecayAlt.P.B1
