-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.inCC_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:36:30.883833+00:00
-- url     : https://prove2.me/submissions/c9d7892b-1ac7-4b03-be81-1c5888286922

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Mathlib.Topology.Algebra.MvPolynomial
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m m' : ℕ} (hm : m' ≤ m)
    {F : B.Mat k r → E} (hF : B.InCC A m F) : B.InCC A m' F := by
  obtain ⟨c, hck, hb⟩ := hF
  exact ⟨c, B5.ckOn_mono (by exact_mod_cast hm) hck, fun u v hu hv hl g hg => hb u v hu hv (le_trans hl hm) g hg⟩
end Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
