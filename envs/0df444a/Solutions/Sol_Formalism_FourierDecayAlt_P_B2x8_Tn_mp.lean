-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.Tn_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:24:55.021294+00:00
-- url     : https://prove2.me/submissions/af916e05-2544-4f54-9445-f26ed9f7060b

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hermitian_form_continuous

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (x₀ : HPar k r') :
    MeasurePreserving (Tn k r' x₀) (μx.prod (volume : Measure (HPar k r'))) (μx.prod (volume : Measure (HPar k r'))) := by
  have hm : Measurable fun p : ℂ × HPar k r' =>
      ((p.2.1 + p.1 • x₀.1, p.2.2 - (conj p.1 * herm (Hpk k r') p.2.1 x₀.1).im + ‖p.1‖ ^ 2 * x₀.2) : HPar k r') := by
    have h : Continuous fun p : ℂ × HPar k r' => herm (Hpk k r') p.2.1 x₀.1 :=
      (hermitian_form_continuous (Hpk k r')).comp ((continuous_fst.comp continuous_snd).prodMk continuous_const)
    have h2 : Continuous fun p : ℂ × HPar k r' => conj p.1 := Complex.continuous_conj.comp continuous_fst
    have h3 : Continuous fun p : ℂ × HPar k r' => (conj p.1 * herm (Hpk k r') p.2.1 x₀.1).im :=
      Complex.continuous_im.comp (h2.mul h)
    apply Continuous.measurable
    fun_prop
  refine (MeasurePreserving.id μx).skew_product
    (g := fun (c : ℂ) (q : HPar k r') => ((q.1 + c • x₀.1, q.2 - (conj c * herm (Hpk k r') q.1 x₀.1).im + ‖c‖ ^ 2 * x₀.2) : HPar k r')) hm ?_
  refine Filter.Eventually.of_forall fun c => ?_
  have hsk : MeasurePreserving
      (fun q : HPar k r' => ((q.1 + c • x₀.1, q.2 - (conj c * herm (Hpk k r') q.1 x₀.1).im + ‖c‖ ^ 2 * x₀.2) : HPar k r'))
      ((volume : Measure (Fin (2 * r' + k + 1) → ℂ)).prod (volume : Measure ℝ))
      ((volume : Measure (Fin (2 * r' + k + 1) → ℂ)).prod (volume : Measure ℝ)) := by
    refine (measurePreserving_add_right (volume : Measure (Fin (2 * r' + k + 1) → ℂ)) (c • x₀.1)).skew_product
      (g := fun (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) => s - (conj c * herm (Hpk k r') y x₀.1).im + ‖c‖ ^ 2 * x₀.2) ?_ ?_
    · exact (hm.comp (measurable_const.prodMk measurable_id : Measurable fun q : HPar k r' => (c, q))).snd
    · refine Filter.Eventually.of_forall fun y => ?_
      have := (measurePreserving_add_right (volume : Measure ℝ)
        (-(conj c * herm (Hpk k r') y x₀.1).im + ‖c‖ ^ 2 * x₀.2)).map_eq
      have he : (fun s : ℝ => s - (conj c * herm (Hpk k r') y x₀.1).im + ‖c‖ ^ 2 * x₀.2) =
          fun s : ℝ => s + (-(conj c * herm (Hpk k r') y x₀.1).im + ‖c‖ ^ 2 * x₀.2) := by
        funext s; ring
      rw [he]; exact this
  exact hsk.map_eq
end Formalism.FourierDecayAlt.P.B2x8
