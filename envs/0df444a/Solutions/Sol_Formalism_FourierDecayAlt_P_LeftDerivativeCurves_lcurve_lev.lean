-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftDerivativeCurves.lcurve_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:24:30.272022+00:00
-- url     : https://prove2.me/submissions/8ca78e4b-0b2f-4564-9dfb-275420f1b604

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_curve_lev


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LeftDerivativeCurves
open Qx2 (Good)
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.LeftDerivativeCurves
theorem _root_.solution {g X : Mx k r} (hg : g ∈ Glev k r i) (hX : inLieLev k r i X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) * g ∈ Glev k r i := by
  have h1 : (1 : Mx k r) ∈ Glev k r i :=
    ⟨by show (1 : Mx k r)ᴴ * Hpk k r * 1 = Hpk k r; simp, fun a _ => ⟨by simp, by simp⟩⟩
  have he := Qx2.curve_lev h1 hX t
  rw [Matrix.one_mul] at he
  obtain ⟨he1, he2⟩ := he
  obtain ⟨hg1, hg2⟩ := hg
  have he1' : (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r := he1
  have hg1' : gᴴ * Hpk k r * g = Hpk k r := hg1
  refine ⟨?_, fun a ha => ?_⟩
  · show (NormedSpace.exp ((t : ℂ) • X) * g)ᴴ * Hpk k r * (NormedSpace.exp ((t : ℂ) • X) * g) = Hpk k r
    rw [conjTranspose_mul]
    have e : gᴴ * (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * (NormedSpace.exp ((t : ℂ) • X) * g) =
        gᴴ * ((NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X)) * g := by
      simp only [Matrix.mul_assoc]
    rw [e, he1', hg1']
  · obtain ⟨h1, h2⟩ := hg2 a ha
    obtain ⟨h3, h4⟩ := he2 a ha
    exact ⟨by rw [← Matrix.mulVec_mulVec, h1, h3], by rw [← Matrix.mulVec_mulVec, h2, h4]⟩
end Formalism.FourierDecayAlt.P.LeftDerivativeCurves
