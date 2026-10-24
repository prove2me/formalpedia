-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.tendsto_apply_of_tendsto_adjointComp_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:58:15.457981+00:00
-- url     : https://prove2.me/submissions/21e5861e-31ff-4f1d-88c4-fbad4343f876

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_VonNeumann
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2

noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace LinearPMap
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Semigroup
end FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Semigroup
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
namespace FunctionalInequalities.Analysis.Semigroup
end FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities.Analysis.Semigroup in
open Filter Topology in
/-- Graph convergence for `T†T` gives convergence of `T`: if `xₙ → y` and `T†T xₙ → T†T y`, then
`T xₙ → T y`, because `‖T (xₙ - y)‖² = ⟪T†T (xₙ - y), xₙ - y⟫`. -/
theorem solution {T : H₀ →ₗ.[ℝ] H₁}
    (hd : Dense (T.domain : Set H₀)) {x : ℕ → (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain}
    {y : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain} (h0 : Tendsto (fun n => (x n : H₀)) atTop (𝓝 (y : H₀)))
    (h1 : Tendsto (fun n => FunctionalInequalities.Analysis.Semigroup.adjointComp T (x n)) atTop (𝓝 (FunctionalInequalities.Analysis.Semigroup.adjointComp T y))) :
    Tendsto (fun n => T ⟨(x n : H₀), (x n).2.2⟩) atTop (𝓝 (T ⟨(y : H₀), y.2.2⟩)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have key (n : ℕ) : ‖T ⟨(x n : H₀), (x n).2.2⟩ - T ⟨(y : H₀), y.2.2⟩‖ ^ 2 ≤
      ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T (x n) - FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ * ‖(x n : H₀) - y‖ := by
    have hTe : T ⟨((x n - y : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain) : H₀), (x n - y).2.2⟩ =
        T ⟨(x n : H₀), (x n).2.2⟩ - T ⟨(y : H₀), y.2.2⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    have hAe : FunctionalInequalities.Analysis.Semigroup.adjointComp T (x n - y) = FunctionalInequalities.Analysis.Semigroup.adjointComp T (x n) - FunctionalInequalities.Analysis.Semigroup.adjointComp T y :=
      LinearPMap.map_sub _ _ _
    rw [← hTe, ← FunctionalInequalities.Analysis.Semigroup.inner_adjointComp_self hd, hAe, Submodule.coe_sub]
    exact real_inner_le_norm _ _
  have hlim : Tendsto (fun n => ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T (x n) - FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ * ‖(x n : H₀) - y‖)
      atTop (𝓝 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.1 h1).mul
      (tendsto_iff_norm_sub_tendsto_zero.1 h0)
  have hsq := squeeze_zero (fun n => by positivity) key hlim
  simpa [Real.sqrt_sq (norm_nonneg _)] using hsq.sqrt
