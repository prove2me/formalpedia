-- Prove2me | solution 1 for Formalism.CountingSumsFrames.comm_XD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:41.223562+00:00
-- url     : https://prove2.me/submissions/f9e85440-d01a-41d0-8503-005d3421ae61

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
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
end Wt
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section Comm
variable {k σ : Type} [Field k]
private theorem pderiv_pderiv_lemma [DecidableEq σ] (i j : σ) (g : MvPolynomial σ k) :
    pderiv i (pderiv j g) = pderiv j (pderiv i g) := by
  have hX : ∀ (l i : σ) (n : σ), pderiv l (pderiv i (X n : MvPolynomial σ k)) = 0 := by
    intro l i n
    by_cases h : n = i
    · subst h; simp
    · rw [pderiv_X_of_ne h, map_zero]
  apply MvPolynomial.induction_on g
  · intro a; simp
  · intro p q hp hq; simp only [map_add, hp, hq]
  · intro p n hp
    simp only [Derivation.leibniz, smul_eq_mul, map_add, hp, hX, mul_zero, zero_add, add_zero]
    ring
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
variable {k σ : Type} [Field k]
namespace Formalism.CountingSumsFrames
theorem _root_.solution [DecidableEq σ] (u v u' v' : σ) (g : MvPolynomial σ k) :
    X u * pderiv v (X u' * pderiv v' g) - X u' * pderiv v' (X u * pderiv v g) =
      (if u' = v then X u * pderiv v' g else 0) - (if u = v' then X u' * pderiv v g else 0) := by
  have hXa : ∀ a b : σ, pderiv b (X a : MvPolynomial σ k) = if a = b then 1 else 0 := by
    intro a b
    by_cases h : a = b
    · subst h; simp
    · rw [if_neg h, pderiv_X_of_ne h]
  simp only [Derivation.leibniz, smul_eq_mul, hXa]
  rw [pderiv_pderiv_lemma v v' g]
  split_ifs <;> ring
end Formalism.CountingSumsFrames
