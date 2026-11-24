-- Prove2me | solution 1 for Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:33:29.040226+00:00
-- url     : https://prove2.me/submissions/ebf464b1-d397-49e1-a054-4300032cdfdb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_degree_snd_lt
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_degree_fst_lt
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
variable {K : Type} [Field K] {σ : Type} {R : Subring K}
namespace Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
theorem _root_.solution {g : MvPowerSeries σ K} (h2 : (2 : K)⁻¹ ∈ R) (h20 : (2 : K) ≠ 0)
    (hg0 : MvPowerSeries.constantCoeff g = 1) (hgg : IntMv R (g * g)) : IntMv R g := by
  classical
  have hh0 : MvPowerSeries.coeff 0 (g - 1) = 0 := by
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, hg0, map_one, sub_self]
  have hid : ∀ n, MvPowerSeries.coeff n (g - 1) = (2 : K)⁻¹ * (MvPowerSeries.coeff n (g * g)
      - MvPowerSeries.coeff n (1 : MvPowerSeries σ K)
      - MvPowerSeries.coeff n ((g - 1) * (g - 1))) := by
    intro n
    have : g * g - 1 - (g - 1) * (g - 1) = (g - 1) + (g - 1) := by ring
    rw [← map_sub, ← map_sub, this, map_add]
    field_simp
    ring
  have key : ∀ (m : ℕ) (n : σ →₀ ℕ), n.degree = m → MvPowerSeries.coeff n (g - 1) ∈ R := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro n hn
      rw [hid n, MvPowerSeries.coeff_mul n (g - 1)]
      refine R.mul_mem h2 (R.sub_mem (R.sub_mem (hgg n) (intMv_one n))
        (Subring.sum_mem _ fun p hp => ?_))
      by_cases h1 : p.1 = 0
      · rw [h1, hh0, zero_mul]; exact R.zero_mem
      by_cases h2' : p.2 = 0
      · rw [h2', hh0, mul_zero]; exact R.zero_mem
      exact R.mul_mem (ih _ (hn ▸ degree_fst_lt hp h2') _ rfl)
        (ih _ (hn ▸ degree_snd_lt hp h1) _ rfl)
  intro n
  have : g = (g - 1) + 1 := by ring
  rw [this, map_add]
  exact R.add_mem (key _ n rfl) (intMv_one n)
end Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
