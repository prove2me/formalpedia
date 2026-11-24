-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.inner_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:14:14.167837+00:00
-- url     : https://prove2.me/submissions/f79c860e-1eed-4535-b9bf-df365340d32a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Sq_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_map_Sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Ff_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_refl_eq

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
theorem _root_.solution (n : ℕ) {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) (y : ℂ) :
    (∫⁻ x : Fin (n + 1) → ℂ, Ff T T' φ y (Complex.normSq y - Sq (n + 1) x)) =
      ((n + 1 : ℕ) * Vb (n + 1) : ℝ≥0∞) * ∫⁻ s : ℝ, Rf n T T' φ y s := by
  have hF : Measurable fun t : ℝ => Ff T T' φ y (Complex.normSq y - t) :=
    (Ff_meas T T' hφ).comp (measurable_const.prodMk (measurable_const.sub measurable_id))
  have hd : Measurable fun t : ℝ => ENNReal.ofReal (t ^ n) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const n)
  rw [← lintegral_map hF (Sq_cont _).measurable, map_Sq, lintegral_smul_measure, smul_eq_mul]
  congr 1
  unfold dens
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hF, ← lintegral_indicator measurableSet_Ioi]
  have hg : Measurable ((Ioi (0 : ℝ)).indicator
      fun t => ENNReal.ofReal (t ^ n) * Ff T T' φ y (Complex.normSq y - t)) :=
    (hd.mul hF).indicator measurableSet_Ioi
  have h2 := (Measure.measurePreserving_sub_left (volume : Measure ℝ) (Complex.normSq y)).lintegral_comp hg
  refine Eq.trans ?_ (Eq.trans h2.symm (lintegral_congr fun s => refl_eq n hT hT' φ y s))
  rfl
end Formalism.FourierDecayAlt.P.TwoByOneBlock
