-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x1.par_subgroupSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:46:52.267474+00:00
-- url     : https://prove2.me/submissions/f9858cec-e87a-419a-bc18-f7201a3c851a

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_par_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x1
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} {r k : ℕ}
variable [CommRing A]
variable {P : Matrix (Fin k) (Fin k) A → Prop}
namespace Formalism.FourierDecayAlt.P.S3x1
theorem _root_.solution (hP : GP P) : IsSubgroupSet (Par (r := r) P) := by
  refine ⟨parG hP, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · exact ⟨Matrix.GeneralLinearGroup.mk'' x (par_det hP hx), hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact hg
end Formalism.FourierDecayAlt.P.S3x1
