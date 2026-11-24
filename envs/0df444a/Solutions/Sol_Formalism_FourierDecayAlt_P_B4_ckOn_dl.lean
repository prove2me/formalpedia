-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.ckOn_dl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:15:55.437622+00:00
-- url     : https://prove2.me/submissions/4bace613-d5e2-42cc-a257-32e4bc8251bc

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_mem
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
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {m : ℕ∞} (t : ℝ × ℝ) (h1 : t.1 ≠ 0) (h2 : t.2 ≠ 0) {f : Mat k r → E}
    (hf : CkOn m (GV k r) f) : CkOn m (GV k r) (dl t f) := by
  unfold CkOn at *
  have hin : ∀ g ∈ GV k r, (aDil k r t.1)⁻¹ * g * aDil k r t.2 ∈ GV k r := by
    intro g hg
    rw [aDil_inv k r t.1 h1]
    exact gv_mul_lemma (gv_mul_lemma (aDil_mem k r _ (inv_ne_zero h1)) hg) (aDil_mem k r _ h2)
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf _ (hin g₀ hg₀)
  let L : Mat k r →L[ℝ] Mat k r := (mulR (aDil k r t.2)).comp (mulL (aDil k r t.1)⁻¹)
  refine ⟨L ⁻¹' U, f' ∘ L, hU.preimage L.continuous, hgU, ?_, ?_⟩
  · exact hc.comp L.contDiff.contDiffOn (fun x hx => hx)
  · intro g hgU' hgG
    exact hff (L g) hgU' (hin g hgG)
end Formalism.FourierDecayAlt.P.B4
