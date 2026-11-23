-- Prove2me | solution 1 for Formalism.DivisionValues.shift_sum_e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:11.124533+00:00
-- url     : https://prove2.me/submissions/ff0c7491-f540-4f18-8cc1-0caff5c6cf7f

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TwistedLatticeNaturality
import Theorems.Thm_Formalism_HN_sizeMu_finrank_eq
import Theorems.Thm_P2M_Formalism_DivisionValues_prod_formula__ad6919c95c2d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable [IsTotallyComplex K]
namespace Formalism.DivisionValues
theorem _root_.solution (p : ℕ) (hp : p.Prime) :
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (vw w (p : K) : ℝ)).Finite ∧
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (vw w (p : K) : ℝ) = Real.log p := by
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨hfin, hsum⟩ := prod_formula' K (p : K) hpK
  refine ⟨hfin, ?_⟩
  rw [← hsum]
  have hnorm : ∀ v : InfinitePlace K, Real.log ‖v.embedding (p : K)‖ = Real.log p := by
    intro v
    simp
  simp only [hnorm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 := Formalism.HN.sizeMu_finrank_eq K
  unfold Formalism.HN.nPl at h2
  have hc : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by
    have h1 : 0 < Module.finrank ℚ K := Module.finrank_pos
    have h3 : Fintype.card (InfinitePlace K) ≠ 0 := by omega
    exact_mod_cast h3
  have hn' : (Module.finrank ℚ K : ℝ) = 2 * Fintype.card (InfinitePlace K) := by
    exact_mod_cast h2
  rw [hn']
  field_simp
end Formalism.DivisionValues
