-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.fock_Ffull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:57:10.368312+00:00
-- url     : https://prove2.me/submissions/72789aa7-d7c6-4072-a66f-cba8653769ed

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_fock_rename
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_eq
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_inclusion_prodMap_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (ρ : Fin r) (n : Fin T.t → ℕ) (f f' : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    fock p (T.Ffull p (LL.setTies T n) i ρ (n i) f) (T.Ffull p (LL.setTies T n) i ρ (n i) f') =
      fock p (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f)
        (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f') := by
  rw [Ffull_eq, Ffull_eq]
  exact fock_rename _ (inclusion_prodMap_injective (hK_of_adm LL T hadm i)) _ _
end Formalism.CountingSumsFrames.TO
