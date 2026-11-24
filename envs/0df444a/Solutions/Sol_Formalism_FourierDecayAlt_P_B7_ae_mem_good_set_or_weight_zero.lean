-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_or_weight_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:13:44.826805+00:00
-- url     : https://prove2.me/submissions/9f430393-512d-49d8-bcd9-5095fe4b8f60

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
attribute [local instance] sfG sfW sfN sfW'
attribute [local instance] sfSS
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) :
    ∀ᵐ q : (Fin r → ℂ) × ℂ, q ∈ Q0 D ∨ bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 := by
  have hc : 0 < Tz k r D.z * Tz k r D.z' := mul_pos D.T_pos D.T'_pos
  have h0 : ∀ᵐ ζ : ℂ, Complex.normSq ζ ≠ Tz k r D.z * Tz k r D.z' := by
    have hs : (volume : Measure ℂ) (Metric.sphere 0 (Real.sqrt (Tz k r D.z * Tz k r D.z'))) = 0 :=
      Measure.addHaar_sphere_of_ne_zero _ _ (Real.sqrt_pos.2 hc).ne'
    refine ae_iff.2 (measure_mono_null ?_ hs)
    intro ζ hζ
    simp only [ne_eq, not_not, Set.mem_ofPred_eq] at hζ
    rw [mem_sphere_zero_iff_norm, ← hζ, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have h1 : ∀ᵐ q : (Fin r → ℂ) × ℂ, Complex.normSq q.2 ≠ Tz k r D.z * Tz k r D.z' :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Fin r → ℂ))) (ν := (volume : Measure ℂ))).ae h0
  filter_upwards [h1] with q hq
  by_cases hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0
  · exact Or.inr hw
  · left
    unfold bcWeight at hw
    split_ifs at hw with hle
    · refine ⟨fun a ha => hw ?_, lt_of_le_of_ne hle (Ne.symm hq)⟩
      have : (∏ a : Fin r, ‖q.1 a‖ ^ (2 * (Mdim k r a - 2))) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
        rw [ha, norm_zero]
        refine zero_pow ?_
        have := a.2
        unfold Mdim
        omega
      rw [this, zero_mul]
    · exact absurd rfl hw
end Formalism.FourierDecayAlt.P.B7
