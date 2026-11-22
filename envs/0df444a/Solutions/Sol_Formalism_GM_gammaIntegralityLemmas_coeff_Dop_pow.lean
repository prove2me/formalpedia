-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.coeff_Dop_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:27:48.482116+00:00
-- url     : https://prove2.me/submissions/4a87135d-d06d-43cc-b478-ef4857be03ea

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_zero
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_congr
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_Dop_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [DecidableEq σ]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (u v : σ) (huv : u ≠ v) (a : ℕ) (G : MvPolynomial σ ℚ_[p]) (β : σ →₀ ℕ) :
    coeff β ((Dop u v ^ a) G) = coeff (β + a • (Finsupp.single u 1 + Finsupp.single v 1)) G *
      (((β u + a).descFactorial a : ℕ) : ℚ_[p]) * (((β v + a).descFactorial a : ℕ) : ℚ_[p]) := by
  induction a generalizing β with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply, Dop_apply, coeff_pderiv, coeff_pderiv]
    rw [ih]
    have hv : ((β + Finsupp.single u 1 : σ →₀ ℕ) : σ → ℕ) v = β v := by
      simp [Finsupp.single_apply, huv]
    have hu' : ((β + Finsupp.single u 1 + Finsupp.single v 1 : σ →₀ ℕ) : σ → ℕ) u = β u + 1 := by
      simp [Finsupp.single_apply, huv]
    have hv' : ((β + Finsupp.single u 1 + Finsupp.single v 1 : σ →₀ ℕ) : σ → ℕ) v = β v + 1 := by
      simp [Finsupp.single_apply, huv]
    rw [hv, hu', hv']
    have hm : β + Finsupp.single u 1 + Finsupp.single v 1 + a • (Finsupp.single u 1 + Finsupp.single v 1) =
        β + (a + 1) • (Finsupp.single u 1 + Finsupp.single v 1) := by
      rw [add_smul, one_smul]; abel
    rw [hm]
    have d1 : (β u + (a + 1)).descFactorial (a + 1) = (β u + 1) * (β u + 1 + a).descFactorial a := by
      rw [show β u + (a + 1) = β u + 1 + a by ring, Nat.descFactorial_succ]
      congr 1; omega
    have d2 : (β v + (a + 1)).descFactorial (a + 1) = (β v + 1) * (β v + 1 + a).descFactorial a := by
      rw [show β v + (a + 1) = β v + 1 + a by ring, Nat.descFactorial_succ]
      congr 1; omega
    rw [d1, d2]
    push_cast
    ring
end Formalism.GM.gammaIntegralityLemmas
