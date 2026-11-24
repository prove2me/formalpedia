-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits.conj_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:40:18.339804+00:00
-- url     : https://prove2.me/submissions/e9f9f376-1623-49b6-b087-dd5f19d160fb

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_UnitsEqOneOrNegOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits
theorem _root_.solution (d : ℕ) (hd : 0 < d) (x : K) (hx : x ^ 2 = -(d : K)) (φ : K →+* ℂ) :
    starRingEnd ℂ (φ x) ≠ φ x := by
  intro h
  rw [Complex.conj_eq_iff_re] at h
  have h2 : (φ x) ^ 2 = -(d : ℂ) := by simpa using congrArg φ hx
  rw [← h] at h2
  have h3 : ((φ x).re ^ 2 : ℝ) = -(d : ℝ) := by exact_mod_cast h2
  have : (0 : ℝ) < d := by exact_mod_cast hd
  nlinarith [sq_nonneg (φ x).re]
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits
