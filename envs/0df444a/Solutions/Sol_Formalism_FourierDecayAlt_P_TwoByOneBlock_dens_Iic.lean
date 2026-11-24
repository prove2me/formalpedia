-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.dens_Iic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:49:22.856106+00:00
-- url     : https://prove2.me/submissions/91752944-a20a-4776-98fc-5df63e2d87cd

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open Set
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution (n : ℕ) (b : ℝ) : dens n (Iic b) = ENNReal.ofReal ((max b 0) ^ (n + 1) / (n + 1)) := by
  unfold dens
  rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have hI : Iic b ∩ Ioi (0 : ℝ) = Ioc 0 b := by ext t; simp [and_comm]
  rw [hI]
  rcases le_total b 0 with hb | hb
  · rw [Ioc_eq_empty (not_lt.2 hb), max_eq_right hb]; simp
  · rw [max_eq_left hb, ← ofReal_integral_eq_lintegral_ofReal]
    · rw [← intervalIntegral.integral_of_le hb, integral_pow]
      simp
    · exact (continuous_pow n).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht => pow_nonneg ht.1.le n)
end Formalism.FourierDecayAlt.P.TwoByOneBlock
