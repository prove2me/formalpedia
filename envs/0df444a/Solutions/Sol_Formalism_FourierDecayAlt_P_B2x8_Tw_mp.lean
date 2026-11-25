-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.Tw_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:54.69537+00:00
-- url     : https://prove2.me/submissions/ecde8e61-1a2b-44b0-8e3b-43d178642e12

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hb_im
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x8__x_map_inv_5a29fa767cc4
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_quadratic_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_prod_swap_measure_preserving
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_ae_second_coordinate_ne_zero

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
theorem _root_.solution (c₀ : ℂ) (hc : c₀ ≠ 0) :
    MeasurePreserving (Tw k r' c₀) (μx.prod (volume : Measure (HPar k r'))) (μx.prod (volume : Measure (HPar k r'))) := by
  have hbase : MeasurePreserving (fun q : HPar k r' => ((q.1, -q.2) : HPar k r')) volume volume := by
    have := (MeasurePreserving.id (volume : Measure (Fin (2 * r' + k + 1) → ℂ))).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
    rw [← Measure.volume_eq_prod] at this
    exact this
  have hS : MeasurePreserving
      (fun p : HPar k r' × ℂ => (((p.1.1, -p.1.2) : HPar k r'), c₀ * hb k r' p.1.1 p.1.2 / conj p.2))
      ((volume : Measure (HPar k r')).prod μx) ((volume : Measure (HPar k r')).prod μx) := by
    refine hbase.skew_product (g := fun (q : HPar k r') (c : ℂ) => c₀ * hb k r' q.1 q.2 / conj c) ?_ ?_
    · have h1 : Measurable fun p : HPar k r' × ℂ => hb k r' p.1.1 p.1.2 :=
        (heisenberg_quadratic_continuous.comp continuous_fst).measurable
      have h2 : Measurable fun p : HPar k r' × ℂ => conj p.2 :=
        (Complex.continuous_conj.comp continuous_snd).measurable
      exact (h1.const_mul c₀).div h2
    · filter_upwards [ae_second_coordinate_ne_zero] with q hq
      refine μx_map_inv _ (mul_ne_zero hc ?_)
      intro h0
      apply hq
      rw [← hb_im (k := k) (r' := r') q.1 q.2, h0]; rfl
  have hT : Tw k r' c₀ = Prod.swap ∘ (fun p : HPar k r' × ℂ =>
      (((p.1.1, -p.1.2) : HPar k r'), c₀ * hb k r' p.1.1 p.1.2 / conj p.2)) ∘ Prod.swap := by
    funext p; rfl
  rw [hT]
  exact (prod_swap_measure_preserving (volume : Measure (HPar k r')) μx).comp (hS.comp (prod_swap_measure_preserving μx (volume : Measure (HPar k r'))))
end Formalism.FourierDecayAlt.P.B2x8
