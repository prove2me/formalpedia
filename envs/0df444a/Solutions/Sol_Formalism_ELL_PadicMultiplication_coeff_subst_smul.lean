-- Prove2me | solution 1 for Formalism.ELL.PadicMultiplication.coeff_subst_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:21:54.890874+00:00
-- url     : https://prove2.me/submissions/10a6d50b-3cdd-4ee3-a013-8248b47c4d0d

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_PadicMult

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
universe u
open Formalism Formalism.ELL Formalism.ELL.PadicMultiplication
open Formalism.G Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.PadicMultiplication
theorem _root_.solution (l e : PowerSeries K) (hl0 : constantCoeff l = 0) (c : K) (n : ℕ) :
    coeff n (e.subst (c • l)) = (coeffPoly l e n).eval c := by
  have hcl : constantCoeff (c • l) = 0 := by simp [hl0]
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr hl0
  have hz : ∀ d, n < d → coeff n (l ^ d) = 0 := by
    intro d hd
    rw [hg, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hcl),
    finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · simp only [coeffPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, smul_pow, PowerSeries.coeff_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun d _ => by ring
  · intro d hd
    rw [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hd
    rw [smul_pow, PowerSeries.coeff_smul, hz d (by omega), smul_zero, smul_zero]
end Formalism.ELL.PadicMultiplication
