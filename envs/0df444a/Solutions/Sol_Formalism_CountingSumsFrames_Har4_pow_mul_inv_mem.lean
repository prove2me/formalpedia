-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.pow_mul_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:32:18.657477+00:00
-- url     : https://prove2.me/submissions/4c21db34-a703-453d-a76d-772ba1acf95e

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har4
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution {K : Type} [Field K] [CharZero K] (R : Subring K) {p : ℕ} (hp : p.Prime)
    (hR : PLocal R p) {M e : ℕ} (hM : M ≠ 0) (hv : M.factorization p ≤ e) :
    (p : K) ^ e * (M : K)⁻¹ ∈ R := by
  have hsplit : p ^ M.factorization p * (M / p ^ M.factorization p) = M :=
    Nat.ordProj_mul_ordCompl_eq_self M p
  have hnd : ¬ p ∣ M / p ^ M.factorization p := Nat.not_dvd_ordCompl hp hM
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have e : (p : K) ^ e * (M : K)⁻¹ = (p : K) ^ (e - M.factorization p) * ((M / p ^ M.factorization p : ℕ) : K)⁻¹ := by
    conv_lhs => rw [← hsplit]
    rw [Nat.cast_mul, Nat.cast_pow, mul_inv, ← mul_assoc, ← pow_sub₀ _ hpK hv]
  rw [e]
  exact R.mul_mem (R.pow_mem (natCast_mem R p) _) (hR _ hnd)
end Formalism.CountingSumsFrames.Har4
