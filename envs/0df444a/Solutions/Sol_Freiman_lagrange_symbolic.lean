-- Prove2me | solution 1 for Freiman.lagrange_symbolic
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:24:30.917889+00:00
-- url     : https://prove2.me/submissions/f161811b-d58e-4b9a-97b3-bb1fde722cd5

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Theorems.Thm_Freiman_irrational_integer_normalization
import Theorems.Thm_Freiman_cfValue_surjective_irrational_unit
import Theorems.Thm_Freiman_approximationValue_integer_translate
import Theorems.Thm_Freiman_perron_formula
import Theorems.Thm_Freiman_perron_local_difference_tendsto
import Theorems.Thm_Freiman_hasFiniteLimsup_congr_of_tendsto_sub_zero
import Theorems.Thm_Freiman_cf_convergence

open Freiman

theorem solution  :
    lagrangeSpectrum = symbolicLagrangeSpectrum := by
  apply Set.Subset.antisymm
  · rintro t ⟨ξ, hξ, ht⟩
    obtain ⟨x, z, hx, h0, h1, hξx⟩ := irrational_integer_normalization ξ hξ
    obtain ⟨b, hb⟩ := cfValue_surjective_irrational_unit x hx h0 h1
    let a : ℤ → ℕ+ := fun i => if 0 ≤ i then b i.toNat else 1
    have ha : (fun k : ℕ => a (k : ℤ)) = b := by
      funext k
      simp [a]
    have hseq : (fun n : ℕ => approximationValue ξ (n + 1)) =
        (fun n : ℕ => approximationValue (cfValue b) (n + 1)) := by
      funext n
      rw [hξx, approximationValue_integer_translate, hb]
    rw [hseq] at ht
    refine ⟨a, ?_⟩
    have hP := (perron_formula b t).mp ht
    have hdiff := perron_local_difference_tendsto a
    rw [ha] at hdiff
    exact (hasFiniteLimsup_congr_of_tendsto_sub_zero _ _ t hdiff).mp hP
  · rintro t ⟨a, ht⟩
    let b : ℕ → ℕ+ := fun n => a (n : ℤ)
    refine ⟨cfValue b, (cf_convergence b).2.1, ?_⟩
    apply (perron_formula b t).mpr
    exact (hasFiniteLimsup_congr_of_tendsto_sub_zero _ _ t
      (perron_local_difference_tendsto a)).mpr ht
