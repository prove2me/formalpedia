-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.haar_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:27:46.613941+00:00
-- url     : https://prove2.me/submissions/8a104633-28c7-436d-9292-5b390877d5e1

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SettingConstruction
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.SettingConstruction
theorem _root_.solution {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) (c : ℝ≥0) (hc : 0 < c) :
    IsHaarOn U (c • μ) where
  conc := by
    rw [Measure.smul_apply, h.conc, smul_zero]
  left := fun a ha => by rw [Measure.map_smul, h.left a ha]
  right := fun a ha => by rw [Measure.map_smul, h.right a ha]
  finite_compact := fun K hK => by
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (h.finite_compact K hK)
  ne_zero := by
    intro h0
    apply h.ne_zero
    have h1 : (c • μ) Set.univ = 0 := by rw [h0]; rfl
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (by exact_mod_cast h2 : c = 0) hc.ne'
    · exact Measure.measure_univ_eq_zero.mp h2
end Formalism.FourierDecayAlt.P.SettingConstruction
