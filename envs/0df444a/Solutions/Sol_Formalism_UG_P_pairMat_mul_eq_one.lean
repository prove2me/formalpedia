-- Prove2me | solution 1 for Formalism.UG.P.pairMat_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:26.21902+00:00
-- url     : https://prove2.me/submissions/604d32d5-7364-48be-8811-68681866178c

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SplitUnitaryGroupIso
import Theorems.Thm_Formalism_UG_P_split_mat_ext
import Theorems.Thm_Formalism_UG_P_split_map_fst_mul
import Theorems.Thm_Formalism_UG_P_split_map_snd_mul
import Theorems.Thm_Formalism_UG_P_pairMat_fst
import Theorems.Thm_Formalism_UG_P_pairMat_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution {X Y X' Y' : Matrix n n R} (h1 : X * X' = 1) (h2 : Y * Y' = 1) :
    pairMat X Y * pairMat X' Y' = 1 := by
  apply split_mat_ext
  · rw [split_map_fst_mul, pairMat_fst, pairMat_fst, h1]
    exact (Matrix.map_one _ rfl rfl).symm
  · rw [split_map_snd_mul, pairMat_snd, pairMat_snd, h2]
    exact (Matrix.map_one _ rfl rfl).symm
end Formalism.UG.P
