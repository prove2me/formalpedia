-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.dl_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:34:57.104027+00:00
-- url     : https://prove2.me/submissions/dcae7fdb-4284-43fa-bf50-fc61cc574a05

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ne_zero_of_mem_I
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private lemma gv_mul_lemma {a c : Mat k r} (ha : a ∈ GV k r) (hc : c ∈ GV k r) : a * c ∈ GV k r := by
  show (a * c)ᴴ * Hpk k r * (a * c) = Hpk k r
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hc' : cᴴ * Hpk k r * c = Hpk k r := hc
  rw [Matrix.conjTranspose_mul,
    show cᴴ * aᴴ * Hpk k r * (a * c) = cᴴ * (aᴴ * Hpk k r * a) * c by simp only [Matrix.mul_assoc],
    ha', hc']
section
variable {t : ℝ × ℝ} (h1 : t.1 ∈ Set.Icc (1 / 2 : ℝ) 2) (h2 : t.2 ∈ Set.Icc (1 / 2 : ℝ) 2)
include h1 h2
end
end Formalism.FourierDecayAlt.P.B4
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {t : ℝ × ℝ} (h1 : t.1 ∈ Set.Icc (1 / 2 : ℝ) 2) (h2 : t.2 ∈ Set.Icc (1 / 2 : ℝ) 2)
include h1 h2
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {g : Mat k r} (hg : g ∈ GV k r) : (aDil k r t.1)⁻¹ * g * aDil k r t.2 ∈ GV k r := by
  rw [aDil_inv k r t.1 (ne_zero_of_mem_I h1)]
  exact gv_mul_lemma (gv_mul_lemma (aDil_mem k r _ (inv_ne_zero (ne_zero_of_mem_I h1))) hg)
    (aDil_mem k r _ (ne_zero_of_mem_I h2))
end Formalism.FourierDecayAlt.P.B4
