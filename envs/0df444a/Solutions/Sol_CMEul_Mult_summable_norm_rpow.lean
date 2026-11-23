-- Prove2me | solution 1 for CMEul.Mult.summable_norm_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:24.930281+00:00
-- url     : https://prove2.me/submissions/140648ad-e095-4c72-9f88-2427dce948ce

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_EulerFactorsMultipliable
import Theorems.Thm_CMEul_Mult_two_le_absNorm
import Theorems.Thm_CMEul_Mult_card_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open CMEul CMEul.Mult
open Formalism.HermitianLatticesTheory
namespace CMEul.Mult
theorem _root_.solution {K : Type} [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ (-s)) := by
  classical
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := Real.summable_nat_rpow.mpr (by linarith)
  refine summable_of_sum_le (c := (Module.finrank ℤ (𝓞 K) : ℝ) * ∑' n : ℕ, (n : ℝ) ^ (-s))
    (fun P => by positivity) ?_
  intro u
  have hmap : ∀ P ∈ u, Ideal.absNorm P.1 ∈ u.image (fun P => Ideal.absNorm P.1) :=
    fun P hP => Finset.mem_image_of_mem _ hP
  calc ∑ P ∈ u, ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ (-s)
      = ∑ n ∈ u.image (fun P => Ideal.absNorm P.1),
        ∑ P ∈ u with Ideal.absNorm P.1 = n, ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ (-s) :=
        (Finset.sum_fiberwise_of_maps_to hmap (fun P => ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ (-s))).symm
    _ = ∑ n ∈ u.image (fun P => Ideal.absNorm P.1),
          ((u.filter (fun P => Ideal.absNorm P.1 = n)).card : ℝ) * (n : ℝ) ^ (-s) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2]),
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ u.image (fun P => Ideal.absNorm P.1),
          (Module.finrank ℤ (𝓞 K) : ℝ) * (n : ℝ) ^ (-s) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        obtain ⟨P, hPu, rfl⟩ := Finset.mem_image.mp hn
        have hc := card_le (Ideal.absNorm P.1) (two_le_absNorm P.1 P.2)
          (u.filter (fun Q => Ideal.absNorm Q.1 = Ideal.absNorm P.1))
          (fun Q hQ => (Finset.mem_filter.mp hQ).2)
        have hc' : ((u.filter (fun Q => Ideal.absNorm Q.1 = Ideal.absNorm P.1)).card : ℝ) ≤ (Module.finrank ℤ (𝓞 K) : ℝ) := by
          exact_mod_cast hc
        exact mul_le_mul_of_nonneg_right hc' (by positivity)
    _ = (Module.finrank ℤ (𝓞 K) : ℝ) * ∑ n ∈ u.image (fun P => Ideal.absNorm P.1), (n : ℝ) ^ (-s) := by
        rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℤ (𝓞 K) : ℝ) * ∑' n : ℕ, (n : ℝ) ^ (-s) := by
        gcongr
        exact hsum.sum_le_tsum _ (fun n _ => by positivity)
end CMEul.Mult
