-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.card_bideg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:14.712805+00:00
-- url     : https://prove2.me/submissions/16fbb959-87d3-4ea8-b178-d13ea6a90c6b

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.CountingSumsFrames
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
end Har2
open Har2
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
private theorem card_finsupp_fin_sum_eq_choose (n A : ℕ) :
    Nat.card {x : Fin (n + 1) →₀ ℕ // ∑ i, x i = A} = (A + n).choose n := by
  have e : {x : Fin (n + 1) →₀ ℕ // ∑ i, x i = A} ≃ Sym (Fin (n + 1)) A :=
    Equiv.subtypeEquiv Multiset.toFinsupp.symm.toEquiv fun x => by
      simp [Multiset.toFinsupp_symm_apply, Finsupp.card_toMultiset, Finsupp.sum_fintype]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin,
    show n + 1 + A - 1 = A + n by omega, Nat.choose_symm_add]
end Har2
end Formalism.CountingSumsFrames
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Har2
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution (k' A B : ℕ) :
    Nat.card {m : XY (k' + 1) →₀ ℕ | xDeg m = A ∧ yDeg m = B} =
      (A + k').choose k' * (B + k').choose k' := by
  have e := (Equiv.subtypeEquiv (p := fun m : XY (k' + 1) →₀ ℕ => xDeg m = A ∧ yDeg m = B)
      (q := fun c : (Fin (k' + 1) →₀ ℕ) × (Fin (k' + 1) →₀ ℕ) => (∑ i, c.1 i = A) ∧ (∑ i, c.2 i = B))
      Finsupp.sumFinsuppEquivProdFinsupp fun m => by
        simp [xDeg, yDeg, Finsupp.fst_sumFinsuppEquivProdFinsupp,
          Finsupp.snd_sumFinsuppEquivProdFinsupp]).trans
    (Equiv.subtypeProdEquivProd (p := fun x : Fin (k' + 1) →₀ ℕ => ∑ i, x i = A)
      (q := fun y : Fin (k' + 1) →₀ ℕ => ∑ i, y i = B))
  rw [show Nat.card ↥{m : XY (k' + 1) →₀ ℕ | xDeg m = A ∧ yDeg m = B} = _ from Nat.card_congr e,
    Nat.card_prod]
  exact congrArg₂ (· * ·) (card_finsupp_fin_sum_eq_choose k' A) (card_finsupp_fin_sum_eq_choose k' B)
end Formalism.CountingSumsFrames.Har2
