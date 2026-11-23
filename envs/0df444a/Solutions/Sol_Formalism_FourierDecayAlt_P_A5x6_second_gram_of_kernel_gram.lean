-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x6.second_gram_of_kernel_gram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:37.058346+00:00
-- url     : https://prove2.me/submissions/383ba569-44dd-460f-b5a1-8cadbd69cb9f

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_psd_comap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P
namespace A5x6
section KRfacts
variable {K : Type} [CommRing K] (R : Subring K)
end KRfacts
private lemma isPSD_real_rescale {X : Type} (F : Finset X) (k : X → X → ℂ) (c : X → ℝ)
    (h : IsPSD F k) : IsPSD F (fun x y => (c x : ℂ) * (c y : ℂ) * k x y) := by
  unfold IsPSD at h ⊢
  intro a
  have e : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * ((c x : ℂ) * (c y : ℂ) * k x y) =
      ∑ x ∈ F, ∑ y ∈ F, (a x * c x) * conj (a y * c y) * k x y := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    ring
  rw [e]
  exact h _
end A5x6
open A5x6
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x6
namespace Formalism.FourierDecayAlt.P.A5x6
theorem _root_.solution (hG : KpGram) (hM : ModMul) : BlockKernelPosSemidef := by
  classical
  unfold BlockKernelPosSemidef
  unfold KpGram at hG
  unfold ModMul at hM
  intro K _ _ _ R ψ hLD s hs m F hF
  have hK := psd_comap (Kp R ψ) (fun x : Point K × Kˣ => addBlock x.1 s x.2) F
    (hG K R ψ hLD _)
  have hc := isPSD_real_rescale F _ (fun x : Point K × Kˣ => modK R (x.2 : K) ^ (s * (s - 1) / 2)) hK
  have e : (fun x y : Point K × Kˣ => Ns R ψ s x.1 y.1 x.2 y.2) = fun x y =>
      ((modK R (x.2 : K) ^ (s * (s - 1) / 2) : ℝ) : ℂ) *
        ((modK R (y.2 : K) ^ (s * (s - 1) / 2) : ℝ) : ℂ) *
        Kp R ψ (addBlock x.1 s x.2) (addBlock y.1 s y.2) := by
    funext x y
    unfold Ns
    rw [(hM K R ψ hLD x.2 y.2).2, mul_pow, Complex.ofReal_mul]
  rw [e]
  exact hc
end Formalism.FourierDecayAlt.P.A5x6
