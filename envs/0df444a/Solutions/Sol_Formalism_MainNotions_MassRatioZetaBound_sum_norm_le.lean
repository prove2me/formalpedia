-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioZetaBound.sum_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:00:08.868716+00:00
-- url     : https://prove2.me/submissions/4d17c153-e207-44f6-9c09-a40bcbc8e87c

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_exists_prime_mem
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_absNorm_ge
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_card_over_le
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_summable_Z

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
theorem _root_.solution (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, P.IsMaximal) :
    ∑ P ∈ S, 1 / ((Ideal.absNorm P : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (Module.finrank ℚ K : ℝ) * zetaGL3GL2 := by
  classical
  have hex : ∀ P ∈ S, ∃ l : ℕ, l.Prime ∧ (l : 𝓞 K) ∈ P := fun P hP => by
    haveI := hS P hP; exact exists_prime_mem P
  choose! lp hlp hlpP using hex
  have hterm : ∀ P ∈ S, 1 / ((Ideal.absNorm P : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 1 / ((lp P : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by
    intro P hP
    haveI := hS P hP
    have hge := (absNorm_ge P (hlp P hP) (hlpP P hP)).2
    have hl0 : (0 : ℝ) < (lp P : ℝ) := by exact_mod_cast (hlp P hP).pos
    apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hl0 _)
    exact Real.rpow_le_rpow hl0.le (by exact_mod_cast hge) (by norm_num)
  calc ∑ P ∈ S, 1 / ((Ideal.absNorm P : ℕ) : ℝ) ^ ((3 : ℝ) / 2)
      ≤ ∑ P ∈ S, 1 / ((lp P : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := Finset.sum_le_sum hterm
    _ = ∑ l ∈ S.image lp, ∑ P ∈ S with lp P = l, 1 / ((lp P : ℕ) : ℝ) ^ ((3 : ℝ) / 2) :=
        (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem lp hP) _).symm
    _ = ∑ l ∈ S.image lp, ((S.filter (fun P => lp P = l)).card : ℝ) * (1 / (l : ℝ) ^ ((3 : ℝ) / 2)) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.1 hP).2]), Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ l ∈ S.image lp, (Module.finrank ℚ K : ℝ) * (1 / (l : ℝ) ^ ((3 : ℝ) / 2)) := by
        refine Finset.sum_le_sum fun l hl => ?_
        obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 hl
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast card_over_le (hlp P0 hP0) _ fun P hP => ⟨hS P (Finset.mem_filter.1 hP).1, by
          have := hlpP P (Finset.mem_filter.1 hP).1; rwa [(Finset.mem_filter.1 hP).2] at this⟩
    _ = (Module.finrank ℚ K : ℝ) * ∑ l ∈ S.image lp, 1 / (l : ℝ) ^ ((3 : ℝ) / 2) := by rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ K : ℝ) * zetaGL3GL2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact summable_Z.sum_le_tsum _ (fun m _ => by positivity)
end Formalism.MainNotions.MassRatioZetaBound
