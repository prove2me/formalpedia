-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioZetaBound.lValEta_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:11:11.13626+00:00
-- url     : https://prove2.me/submissions/3bf8daf2-b46a-4468-b5e0-e3f20809f8ed

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_sum_norm_le
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_two_le_absNorm
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_eulerFac_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioZetaBound
open NumberField
variable {K : Type*} [Field K] [NumberField K]
namespace Formalism.MainNotions.MassRatioZetaBound
theorem _root_.solution [StarRing K] {M : ℕ} (hM : 3 ≤ M) :
    Formalism.HermitianLatticesTheory.lValEta K M ≤ Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) := by
  classical
  unfold Formalism.HermitianLatticesTheory.lValEta
  by_cases hm : Multipliable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac K M P.1)
  · refine hm.tprod_le_of_prod_le fun s => ?_
    have hN : ∀ P : {P : Ideal (𝓞 K) // P.IsMaximal}, 2 ≤ Ideal.absNorm P.1 := fun P => by
      haveI := P.2; exact two_le_absNorm P.1
    calc ∏ P ∈ s, Formalism.HermitianLatticesTheory.eulerFac K M P.1
        ≤ ∏ P ∈ s, Real.exp (2 * (1 / ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2))) :=
          Finset.prod_le_prod (fun P _ => (eulerFac_le hM P.1 (hN P)).1.le) (fun P _ => (eulerFac_le hM P.1 (hN P)).2)
      _ = Real.exp (2 * ∑ P ∈ s, 1 / ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) := by
          rw [← Real.exp_sum, Finset.mul_sum]
      _ ≤ Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) := by
          refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (by norm_num))
          have e : ∑ P ∈ s, 1 / ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) =
              ∑ Q ∈ s.map (Function.Embedding.subtype _), 1 / ((Ideal.absNorm Q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by
            rw [Finset.sum_map]; rfl
          rw [e]
          refine sum_norm_le _ fun Q hQ => ?_
          obtain ⟨P, -, rfl⟩ := Finset.mem_map.1 hQ
          exact P.2
  · rw [tprod_eq_one_of_not_multipliable hm]
    have hZ : 0 ≤ zetaGL3GL2 := tsum_nonneg fun m => by positivity
    exact Real.one_le_exp (by positivity)
end Formalism.MainNotions.MassRatioZetaBound
