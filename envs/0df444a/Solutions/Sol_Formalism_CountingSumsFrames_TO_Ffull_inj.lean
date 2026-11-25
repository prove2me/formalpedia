-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.Ffull_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:57:14.351825+00:00
-- url     : https://prove2.me/submissions/54574d62-a97f-4b28-9bdc-9a1ab35b140b

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_eq
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_freeze_zero
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_inclusion_prodMap_injective
import Theorems.Thm_Formalism_GM_extendBijOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.GM.TM MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] [NeZero r] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (ρ : Fin r)
  (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ) (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i)
include hadm hS
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)))
    (h0 : T.Ffull p (LL.setTies T n) i ρ (n i) f = 0) : f = 0 := by
  have hK := hK_of_adm LL T hadm i
  rw [Ffull_eq] at h0
  have h1 : freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f = 0 := by
    apply rename_injective _ (inclusion_prodMap_injective (r := r) hK)
    rw [h0, map_zero]
  exact (Formalism.GM.extendBijOn p (T.pos i + 1) r ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) hS).1 f hP 0
    (Submodule.zero_mem _) (by rw [h1, freeze_zero])
end Formalism.CountingSumsFrames.TO
