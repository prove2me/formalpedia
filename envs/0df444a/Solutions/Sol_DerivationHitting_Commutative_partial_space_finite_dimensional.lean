-- Prove2me | solution 1 for DerivationHitting.Commutative.partial_space_finite_dimensional
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:36:13.356129+00:00
-- url     : https://prove2.me/submissions/8e4bd0fd-52be-4557-bcd3-14b754c77c79

import Mathlib
import Definitions.Def_DerivationHitting_Commutative_PolynomialData

section
open DerivationHitting.Commutative

namespace DerivationHitting.Dev.PartialFD
noncomputable section

lemma totalDegree_pderiv_le {F : Type*} [Field F] {n : ℕ} (i : Fin n)
    (p : MvPolynomial (Fin n) F) :
    (MvPolynomial.pderiv i p).totalDegree ≤ p.totalDegree := by
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro m hm
  have hne : MvPolynomial.coeff m (MvPolynomial.pderiv i p) ≠ 0 := by simpa using hm
  rw [MvPolynomial.coeff_pderiv] at hne
  have h1 : MvPolynomial.coeff (m + Finsupp.single i 1) p ≠ 0 := left_ne_zero_of_mul hne
  have h2 := MvPolynomial.le_totalDegree (s := m + Finsupp.single i 1) (by simpa using h1)
  have e : ((m + Finsupp.single i 1).sum fun _ e => e) = (m.sum fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (by simp) (by intros; rfl)]
    simp
  omega

lemma iteratedPartial_mem {F : Type*} [Field F] {n : ℕ} (f : MvPolynomial (Fin n) F)
    (w : List (Fin n)) :
    iteratedPartial f w ∈ MvPolynomial.restrictTotalDegree (Fin n) F f.totalDegree := by
  have : ∀ (w : List (Fin n)) (g : MvPolynomial (Fin n) F), g.totalDegree ≤ f.totalDegree →
      (w.foldl (fun g i => MvPolynomial.pderiv i g) g).totalDegree ≤ f.totalDegree := by
    intro w
    induction w with
    | nil => intro g hg; simpa using hg
    | cons a w ih =>
      intro g hg
      exact ih _ ((totalDegree_pderiv_le a g).trans hg)
  rw [MvPolynomial.mem_restrictTotalDegree]
  exact this w f le_rfl

end
end DerivationHitting.Dev.PartialFD

open DerivationHitting.Dev.PartialFD
namespace DerivationHitting.Commutative
theorem chk_partial_space_finite_dimensional {F : Type*} [Field F] [CharZero F] {n : ℕ}
    (f : MvPolynomial (Fin n) F) :
    partialSpace f ≤ MvPolynomial.restrictTotalDegree (Fin n) F f.totalDegree ∧
      FiniteDimensional F (partialSpace f) := by
  have hle : partialSpace f ≤ MvPolynomial.restrictTotalDegree (Fin n) F f.totalDegree := by
    unfold partialSpace
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact iteratedPartial_mem f w
  exact ⟨hle, Submodule.finiteDimensional_of_le hle⟩

end DerivationHitting.Commutative
end

theorem solution : type_of% @DerivationHitting.Commutative.chk_partial_space_finite_dimensional := @DerivationHitting.Commutative.chk_partial_space_finite_dimensional
