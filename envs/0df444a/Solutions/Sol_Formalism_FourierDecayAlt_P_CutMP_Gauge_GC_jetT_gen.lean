-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:33:18.973173+00:00
-- url     : https://prove2.me/submissions/df1cfdb8-9679-4c9b-b821-b8cf4936af1c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTJet
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_jetT_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_jetT_fderiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution {D G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : D → G} {U : Set D} (hU : IsOpen U) {g₀ : D} (hgU : g₀ ∈ U)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U) (L : D →L[ℝ] D) (N : ℕ)
    (hv : ∀ j ≤ N + 1, iteratedFDeriv ℝ j F g₀ = 0) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => fderiv ℝ F x (L x)) U ∧
      ∀ j ≤ N, iteratedFDeriv ℝ j (fun x => fderiv ℝ F x (L x)) g₀ = 0 := by
  have hmn : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]
  have hF' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ F y) U := hF.fderiv_of_isOpen hU hmn
  refine ⟨hF'.clm_apply L.contDiff.contDiffOn, ?_⟩
  intro j hj
  let Bl : (D →L[ℝ] G) →L[ℝ] D →L[ℝ] G := (ContinuousLinearMap.apply ℝ G : D →L[ℝ] (D →L[ℝ] G) →L[ℝ] G).flip
  have hfun : (fun x => fderiv ℝ F x (L x)) = fun x => Bl (fderiv ℝ F x) (L x) := rfl
  have hbd := Bl.norm_iteratedFDerivWithin_le_of_bilinear hF' L.contDiff.contDiffOn hU.uniqueDiffOn hgU
    (n := j) (jetT_le j)
  have hzero : ∀ i ∈ Finset.range (j + 1), iteratedFDerivWithin ℝ i (fun y => fderiv ℝ F y) U g₀ = 0 := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i hU hgU]
    exact jetT_fderiv (hv (i + 1) (by simp at hi; omega))
  rw [Finset.sum_eq_zero (fun i hi => by rw [hzero i hi, norm_zero, mul_zero, zero_mul]), mul_zero] at hbd
  have h0 := norm_le_zero_iff.1 hbd
  rw [iteratedFDerivWithin_of_isOpen j hU hgU] at h0
  rw [hfun]
  exact h0
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
