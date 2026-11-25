-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.Ffull_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:01:41.726804+00:00
-- url     : https://prove2.me/submissions/f7403c93-56c6-4acd-b555-45813b00e561

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_top
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_pol
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_ycond
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_top


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
theorem _root_.solution (w : Fin r → ℤ) (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) :
    T.Ffull p (LL.setTies T n) i ρ (n i) f ∈ Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr := by
  have hP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)) :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1).1
  refine Submodule.mem_inf.mpr ⟨Ffull_pol LL T hadm i ρ n f hP hS, (Submodule.mem_iInf _).mpr fun k => ?_⟩
  by_cases hk : T.J k < T.pos i + 1 + 1
  · rw [Mup, if_pos hk]
    exact Ffull_ycond LL T hadm i ρ n w f hf hS k (by omega)
  · rw [Mup, if_neg hk, Formalism.GM.DimensionMonotonicity.ycond_top]; exact Submodule.mem_top
end Formalism.CountingSumsFrames.TO
