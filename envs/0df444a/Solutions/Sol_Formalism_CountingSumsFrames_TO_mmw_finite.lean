-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.mmw_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:27.977029+00:00
-- url     : https://prove2.me/submissions/60b98707-be46-4449-a048-4f1fd6de80f2

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_finite


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
include hρ
omit hρ
omit hadm hS
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution :
    {w : Fin r → ℤ | MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥}.Finite := by
  classical
  refine ((pol_finite (r := r) ((LL.setTies T n).takeD (T.pos i + 1))).image
    (fun m => fun c => wt ((LL.setTies T n).takeD (T.pos i + 1)) (T.pos i + 1) c m)).subset ?_
  intro w hw
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw
  have hP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)) :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1).1
  have hW := (Submodule.mem_inf.mp hf).2
  obtain ⟨m, hm⟩ : ∃ m, m ∈ f.support := by
    by_contra hc; push Not at hc
    exact hf0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
  rw [Pol, mem_restrictSupport_iff] at hP
  rw [WtSpC, mem_restrictSupport_iff] at hW
  exact ⟨m, hP (Finset.mem_coe.mpr hm), funext fun c => hW (Finset.mem_coe.mpr hm) c (mem_univ c)⟩
end Formalism.CountingSumsFrames.TO
