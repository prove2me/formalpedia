-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ycond_comap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:20.761208+00:00
-- url     : https://prove2.me/submissions/2520c42e-1c96-4b31-b42d-7feff43437aa

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_wt_le_of_mem
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_rename
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_weight_mapDomain
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_wt_le_of_mem
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_stable


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
namespace Formalism.CountingSumsFrames
theorem _root_.solution [NeZero r] {M' : ℕ} (LA : Letters M') (LB : Letters N) (ι : Fin M' → Fin N)
    (hι : ∀ a, ((ι a) : ℕ) = a) (hv : ∀ a, LB.vec (ι a) = LA.vec a)
    (hinj : Function.Injective (fun x : Fin M' × Fin r => (ι x.1, x.2))) (j : ℕ) (Mth : WithTop ℤ)
    (hwv : (wv LB j) ∘ (fun x : Fin M' × Fin r => (ι x.1, x.2)) = wv LA j)
    {F' : MvPolynomial (Fin M' × Fin r) ℚ_[p]}
    (hF : rename (fun x : Fin M' × Fin r => (ι x.1, x.2)) F' ∈ YCond p LB j Mth) : F' ∈ YCond p LA j Mth := by
  classical
  have hle : (YCond p LB j Mth).comap (rename (fun x : Fin M' × Fin r => (ι x.1, x.2))).toLinearMap ≤
      YCond p LA j Mth := by
    refine le_sSup ⟨?_, ?_⟩
    · intro G hG
      rw [mem_restrictSupport_iff]
      intro m hm
      show ((wt LA j 0 m : ℤ) : WithTop ℤ) ≤ Mth
      have h1 : Finsupp.mapDomain (fun x : Fin M' × Fin r => (ι x.1, x.2)) m ∈
          (rename (fun x : Fin M' × Fin r => (ι x.1, x.2)) G).support := by
        rw [support_rename_of_injective hinj]; exact Finset.mem_image_of_mem _ hm
      have h2 := Formalism.GM.FrozenVariableComponents.wt_le_of_mem p LB j Mth _ hG _ h1
      rwa [← weight_wv, weight_mapDomain, hwv, weight_wv] at h2
    · intro c d G hG
      show rename _ (glAct p LA j c d G) ∈ YCond p LB j Mth
      rw [glAct_rename LA LB ι hι hv j c d G]
      exact Formalism.GM.FrozenVariableComponents.ycond_stable p LB j Mth c d _ hG
  exact hle hF
end Formalism.CountingSumsFrames
