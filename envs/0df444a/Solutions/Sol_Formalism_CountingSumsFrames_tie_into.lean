-- Prove2me | solution 1 for Formalism.CountingSumsFrames.tie_into
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:22:14.963258+00:00
-- url     : https://prove2.me/submissions/4611602a-0cef-4437-9b13-28be0208a2bd

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_hw
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
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
namespace Formalism.CountingSumsFrames
theorem _root_.solution [NeZero r] (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ)
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) (w : Fin r → ℤ)
    {f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]}
    (hf : f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) :
    T.Ffull p (LL.setTies T n) i ρ (n i) f ∈
      GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) (w - ((n i : ℕ) : ℤ) • Pi.single ρ 1) ⊓
      Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr := by
  have hP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)) :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1).1
  refine Submodule.mem_inf.mpr ⟨Ffull_hw LL T hadm i ρ hρ n w f hf hS, Submodule.mem_inf.mpr
    ⟨Ffull_pol LL T hadm i ρ n f hP hS, (Submodule.mem_iInf _).mpr fun k => ?_⟩⟩
  by_cases hk : T.J k < T.pos i + 1 + 1
  · rw [Mup, if_pos hk]
    exact Ffull_ycond LL T hadm i ρ n w f hf hS k (by omega)
  · rw [Mup, if_neg hk, ycond_top]; exact Submodule.mem_top
end Formalism.CountingSumsFrames
