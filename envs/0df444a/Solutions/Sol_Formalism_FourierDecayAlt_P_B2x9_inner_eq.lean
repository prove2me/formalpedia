-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.inner_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:19:46.325796+00:00
-- url     : https://prove2.me/submissions/61322620-d8d6-40f2-803b-aa71b38bb837

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_mulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_sigmaFinite_of_haar
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_tau_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_Psi_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_oneStep_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_Ff_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_neg_HPar
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_swap
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mulM_cont


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution (HIv : HaarInv) (hG : ClosedG) (HI : HeisInv) (μG₁ : Measure (Mt k r')) (h₁ : IsHaarOn (GV k r') μG₁)
    (hP : IsClosedSubgroup (P1set k r')) (hμP : IsHaarOn (P1set k r') (muP μG₁)) (f : Mt k (1 + r') → ℝ≥0∞) (hf : Measurable f)
    (c : ℂ) :
    ∫⁻ p : (HPar k r' × HPar k r') × Mt k r', f (Psi k r' (c, p))
          ∂((volume : Measure (HPar k r' × HPar k r')).prod μG₁) = ∫⁻ x : HPar k r', Ff (muP μG₁) f (tau k r' (c, x)) := by
  haveI := sigmaFinite_of_haar h₁
  haveI : SigmaFinite (muP μG₁) := sigmaFinite_of_haar hμP
  have hPsi : ∀ (x x' : HPar k r') (g : Mt k r'), Psi k r' (c, ((x, x'), g)) =
      mulM (tau k r' (c, (-x.1, -x.2)), mulM (levM k r' g, heisF k r' x')) := by
    intro x x' g
    show oneStep k r' x c (Matrix.of g) x' = _
    rw [oneStep_eq HI]
    rfl
  have hmF : Measurable fun p : (HPar k r' × HPar k r') × Mt k r' => f (Psi k r' (c, p)) :=
    hf.comp (Psi_meas.comp (measurable_const.prodMk measurable_id))
  have hG' : Measurable fun x : HPar k r' => Ff (muP μG₁) f (tau k r' (c, x)) :=
    (Ff_meas _ hf).comp (tau_meas.comp (measurable_const.prodMk measurable_id))
  have hin : ∀ x : HPar k r', ∫⁻ y : HPar k r', ∫⁻ g, f (Psi k r' (c, ((x, y), g))) ∂μG₁ ∂volume =
      Ff (muP μG₁) f (tau k r' (c, (-x.1, -x.2))) := by
    intro x
    have hh : Measurable fun q => f (mulM (tau k r' (c, (-x.1, -x.2)), q)) :=
      hf.comp (mulM_cont.comp (continuous_const.prodMk continuous_id)).measurable
    have hm2 : Measurable fun p : HPar k r' × Mt k r' => f (Psi k r' (c, ((x, p.1), p.2))) :=
      hmF.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    calc ∫⁻ y : HPar k r', ∫⁻ g, f (Psi k r' (c, ((x, y), g))) ∂μG₁ ∂volume
        = ∫⁻ p : HPar k r' × Mt k r', f (Psi k r' (c, ((x, p.1), p.2)))
            ∂((volume : Measure (HPar k r')).prod μG₁) := (lintegral_prod _ hm2.aemeasurable).symm
      _ = ∫⁻ p : HPar k r' × Mt k r', f (mulM (tau k r' (c, (-x.1, -x.2)), mulM (levM k r' p.2, heisF k r' p.1)))
            ∂((volume : Measure (HPar k r')).prod μG₁) := by
          refine lintegral_congr (fun p => ?_)
          rw [hPsi]
      _ = Ff (muP μG₁) f (tau k r' (c, (-x.1, -x.2))) := (swap HIv hG HI μG₁ h₁ hP hμP _ hh).symm
  rw [lintegral_prod (fun p => f (Psi k r' (c, p))) hmF.aemeasurable,
    Measure.volume_eq_prod (α := HPar k r') (β := HPar k r'),
    lintegral_prod (fun xx : HPar k r' × HPar k r' => ∫⁻ g, f (Psi k r' (c, (xx, g))) ∂μG₁)
      hmF.lintegral_prod_right'.aemeasurable]
  simp only [hin]
  conv_rhs => rw [← neg_HPar]
  rw [lintegral_map (f := fun x => Ff (muP μG₁) f (tau k r' (c, x))) hG' measurable_neg]
  rfl
end Formalism.FourierDecayAlt.P.B2x9
