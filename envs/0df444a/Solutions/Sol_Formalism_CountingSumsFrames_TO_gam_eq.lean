-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.gam_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:05:16.84968+00:00
-- url     : https://prove2.me/submissions/bfc3e18c-e7d1-4a10-9a1f-4f99440144cf

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_fock_rename
import Theorems.Thm_Formalism_CountingSumsFrames_TO_phi_Ffull
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
    tieGam p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (T.z i) (n i) f f' =
      (((((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)) + n i + r + T.z i - 1).choose
          (((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i))) : ℕ) : ℚ_[p]) *
        fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) f))
          (T.Ffull p (LL.setTies T n) i ρ (n i) f') /
        ((((n i - ((LL.setTies T n).takeD (T.pos i + 1)).total).factorial *
            ((LL.setTies T n).takeD (T.pos i + 1)).total.factorial : ℕ) : ℚ_[p]) *
          ∏ x, ((((LL.setTies T n).takeD (T.pos i + 1)).deg x).factorial : ℚ_[p])) := by
  rw [phi_Ffull LL T hadm i ρ n f, Ffull_eq, fock_rename _ (inclusion_prodMap_injective (hK_of_adm LL T hadm i))]
  rfl
end Formalism.CountingSumsFrames.TO
