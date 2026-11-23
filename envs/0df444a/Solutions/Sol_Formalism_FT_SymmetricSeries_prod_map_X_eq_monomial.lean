-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.prod_map_X_eq_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:09.909741+00:00
-- url     : https://prove2.me/submissions/bb34b356-2308-4a7a-bf8e-9dbcbb50a1df

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.FT Formalism.FT.SymmetricSeries
variable {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]
namespace Formalism.FT.SymmetricSeries
theorem _root_.solution (s : Multiset σ) :
    (s.map (MvPolynomial.X : σ → MvPolynomial σ R)).prod =
      MvPolynomial.monomial (Multiset.toFinsupp s) 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add, Multiset.toFinsupp_add,
      Multiset.toFinsupp_singleton, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
end Formalism.FT.SymmetricSeries
