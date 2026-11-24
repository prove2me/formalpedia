-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_sym_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:15.299073+00:00
-- url     : https://prove2.me/submissions/4d2fc9e7-7713-4a63-ab59-72794719f8a9

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [CommRing A] (G : Matrix (Fin n) (Fin n) A)
    (m : ι → Fin n) (β : Fin n → ℕ) (hβ : ∀ x, qs_cnt m x = β x) (α : Fin n →₀ ℕ) :
    MvPolynomial.coeff α (∏ x : Fin n, (∑ a : Fin n, MvPolynomial.C (G a x) * X a) ^ (β x)) =
      ∑ a : ι → Fin n, if (∀ x, qs_cnt a x = α x) then ∏ c, G (a c) (m c) else 0 := by
  classical
  have h1 : (∏ x : Fin n, (∑ a : Fin n, (MvPolynomial.C (G a x) * X a : MvPolynomial (Fin n) A)) ^ (β x)) =
      ∏ c : ι, ∑ a : Fin n, MvPolynomial.C (G a (m c)) * X a := by
    rw [← Finset.prod_fiberwise (s := univ) (g := m)]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => ∑ a : Fin n, (MvPolynomial.C (G a x) * X a : MvPolynomial (Fin n) A))
      (fun c hc => by rw [(Finset.mem_filter.1 hc).2]), Finset.prod_const, ← hβ x]
    rfl
  rw [h1, Fintype.prod_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 : (∏ c : ι, (MvPolynomial.C (G (a c) (m c)) * X (a c) : MvPolynomial (Fin n) A)) =
      MvPolynomial.monomial (∑ c : ι, Finsupp.single (a c) 1) (∏ c, G (a c) (m c)) := by
    rw [MvPolynomial.monomial_sum_prod]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [MvPolynomial.C_mul_X_eq_monomial]
  rw [h2, MvPolynomial.coeff_monomial]
  have h3 : (∑ c : ι, Finsupp.single (a c) 1 = α) ↔ ∀ x, qs_cnt a x = α x := by
    rw [Finsupp.ext_iff]
    refine forall_congr' fun x => ?_
    rw [Finsupp.finsetSum_apply, qs_cnt, Finset.card_filter]
    simp only [Finsupp.single_apply]
  simp only [h3]
end Formalism.InvariantFactorPaths.ColumnFamilies
