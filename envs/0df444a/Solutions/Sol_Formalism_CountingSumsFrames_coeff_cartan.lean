-- Prove2me | solution 1 for Formalism.CountingSumsFrames.coeff_cartan
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:10.349747+00:00
-- url     : https://prove2.me/submissions/70dba463-da13-4964-af33-839248aa3a97

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_wt_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
section Peel
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι]
end Peel
section Lat
variable {p : ℕ} [Fact p.Prime]
end Lat
section Codim
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
end Codim
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section Stab
variable {k σ : Type} [Field k]
end Stab
section Keep
variable {p : ℕ} [Fact p.Prime]
end Keep
section Keep2
variable {p : ℕ} [Fact p.Prime]
end Keep2
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section XD
variable {k σ : Type} [Field k]
end XD
section Gl
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Gl
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section Wt
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
private theorem coeff_XD_lemma (v : Fin N × Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (m : Fin N × Fin r →₀ ℕ) : coeff m (X v * pderiv v x) = (m v : ℚ_[p]) * coeff m x := by
  induction x using MvPolynomial.induction_on'
  · rename_i n a
    rw [pderiv_monomial, X, monomial_mul, one_mul, coeff_monomial, coeff_monomial]
    by_cases hn : n v = 0
    · simp only [hn, Nat.cast_zero, mul_zero, ite_self]
      split_ifs with h
      · subst h; simp [hn]
      · simp
    · have hsum : Finsupp.single v 1 + (n - Finsupp.single v 1) = n := by
        ext w
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs with h
        · subst h; omega
        · simp
      rw [hsum]
      split_ifs with h
      · subst h; ring
      · simp
  · rename_i f g hf hg
    simp only [map_add, mul_add, coeff_add, hf, hg]
end Wt
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section Comm
variable {k σ : Type} [Field k]
end Comm
section Terms
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Terms
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section Gen
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
end Gen
section Rep
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Rep
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section Proj
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Proj
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section Comp
variable {K σ : Type} [Field K]
end Comp
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section HW
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end HW
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section E1
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end E1
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section E2
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end E2
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section E3
end E3
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM
end Formalism.CountingSumsFrames
end

set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters N) (j : ℕ) (c : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (m : Fin N × Fin r →₀ ℕ) : coeff m (glAct p LL j c c x) = ((wt LL j c m : ℤ) : ℚ_[p]) * coeff m x := by
  unfold glAct
  rw [LinearMap.sum_apply, coeff_sum, wt_eq, Int.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < j
  · by_cases hv : LL.vec i = true
    · simp only [if_pos h, if_pos hv]
      show coeff m (X (i, c) * pderiv (i, c) x) = _
      rw [coeff_XD_lemma]
      push_cast
      ring
    · simp only [if_pos h, if_neg hv, LinearMap.neg_apply, coeff_neg]
      show -coeff m (X (i, c) * pderiv (i, c) x) = _
      rw [coeff_XD_lemma]
      push_cast
      ring
  · simp only [if_neg h]
    simp
end Formalism.CountingSumsFrames
