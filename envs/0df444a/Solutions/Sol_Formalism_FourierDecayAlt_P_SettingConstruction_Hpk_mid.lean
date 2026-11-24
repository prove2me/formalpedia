-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.Hpk_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:26:13.286629+00:00
-- url     : https://prove2.me/submissions/5d26e865-57b6-4ca9-bfa8-06d8756f935b

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SettingConstruction
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r : ℕ)
namespace Formalism.FourierDecayAlt.P.SettingConstruction
theorem _root_.solution (a b : Fin (k + 1)) : Hpk k r (wI k r a) (wI k r b) = Hb k a b := by
  simp only [Hpk, Hb, wI, Matrix.diagonal_apply, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | (exfalso; omega) | (norm_num; done) | (norm_num; intro h; exfalso; omega) | (intro h; exfalso; omega)
end Formalism.FourierDecayAlt.P.SettingConstruction
