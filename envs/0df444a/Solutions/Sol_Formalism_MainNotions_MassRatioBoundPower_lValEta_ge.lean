-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioBoundPower.lValEta_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:11:08.206543+00:00
-- url     : https://prove2.me/submissions/7518ba2f-ae27-49b8-ac3c-6dce213027a4

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBoundPower
import Theorems.Thm_Formalism_MainNotions_MassRatioBoundPower_zeta_three_halves_nonneg
import Theorems.Thm_Formalism_MainNotions_MassRatioBoundPower_eulerFac_ge
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_sum_norm_le
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_two_le_absNorm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioBoundPower
open NumberField Formalism.MainNotions.MassRatioZetaBound
variable {K : Type*} [Field K] [NumberField K]
namespace Formalism.MainNotions.MassRatioBoundPower
theorem _root_.solution [StarRing K] {M : ℕ} (hM : 3 ≤ M) :
    Real.exp (-(2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2))) ≤ Formalism.HermitianLatticesTheory.lValEta K M := by
  classical
  unfold Formalism.HermitianLatticesTheory.lValEta
  have hN : ∀ P : {P : Ideal (𝓞 K) // P.IsMaximal}, 2 ≤ Ideal.absNorm P.1 := fun P => by
    haveI := P.2; exact two_le_absNorm P.1
  by_cases hm : Multipliable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac K M P.1)
  · refine ge_of_tendsto' hm.hasProd fun s => ?_
    calc Real.exp (-(2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)))
        ≤ Real.exp (-(2 * ∑ P ∈ s, 1 / ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2))) := by
          refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ (by norm_num)))
          have e : ∑ P ∈ s, 1 / ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) =
              ∑ Q ∈ s.map (Function.Embedding.subtype _), 1 / ((Ideal.absNorm Q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by
            rw [Finset.sum_map]; rfl
          rw [e]
          refine sum_norm_le _ fun Q hQ => ?_
          obtain ⟨P, -, rfl⟩ := Finset.mem_map.1 hQ
          exact P.2
      _ = ∏ P ∈ s, Real.exp (-(2 * (1 / ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)))) := by
          rw [← Real.exp_sum]; congr 1; rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      _ ≤ ∏ P ∈ s, Formalism.HermitianLatticesTheory.eulerFac K M P.1 :=
          Finset.prod_le_prod (fun P _ => (Real.exp_pos _).le) (fun P _ => eulerFac_ge hM P.1 (hN P))
  · rw [tprod_eq_one_of_not_multipliable hm]
    exact Real.exp_le_one_iff.2 (by have := zeta_three_halves_nonneg; have : (0 : ℝ) ≤ Module.finrank ℚ K := by positivity
                                    nlinarith)
end Formalism.MainNotions.MassRatioBoundPower
