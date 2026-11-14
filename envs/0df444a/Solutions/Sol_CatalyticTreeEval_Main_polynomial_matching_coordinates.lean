-- Prove2me | solution 1 for CatalyticTreeEval.Main.polynomial_matching_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T01:36:26.935564+00:00
-- url     : https://prove2.me/submissions/d060f1a9-ad1b-478a-97c7-85ec42e4fb02

import Definitions.Def_CatalyticTreeEval_PolynomialCoordinates

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- Evaluation can be summed over any finite support cover, setting unused coefficients to zero. -/
theorem eval_eq_sum_cover {m H : ℕ} (f : Poly m H) (x : Vec m H)
    (s : Finset (Monomial H)) (hcover : f.support ⊆ s) :
    MvPolynomial.eval x f = ∑ v ∈ s, MvPolynomial.coeff v f * monomialValue x v := by
  classical
  rw [MvPolynomial.eval_eq']
  apply Finset.sum_subset hcover
  intro v hv hn
  have hc : MvPolynomial.coeff v f = 0 := by
    simpa using hn
  simp [hc]

/-- The algebraic conversion in Lemma B.4. This does not assume a printer. -/
theorem coefficient_dot_evaluation {m H : ℕ} (f : Poly m H) (x : Vec m H)
    (ms : List (Monomial H)) (hnodup : ms.Nodup)
    (hcover : ∀ v ∈ f.support, v ∈ ms) :
    coefficientCoordinates f ms ⬝ᵥ evaluationCoordinates x ms = MvPolynomial.eval x f := by
  classical
  rw [eval_eq_sum_cover f x ms.toFinset (by
    intro v hv
    exact List.mem_toFinset.mpr (hcover v hv))]
  change (∑ j : Fin ms.length, MvPolynomial.coeff (ms.get j) f * monomialValue x (ms.get j)) = _
  rw [List.sum_toFinset _ hnodup]
  exact Fin.sum_univ_fun_getElem ms (fun v => MvPolynomial.coeff v f * monomialValue x v)

/-- A polynomial matching family yields matching vectors in any nonduplicated support-covering
monomial order. Uniform access remains a separate computational obligation of Lemma B.4. -/
theorem polynomial_matching_coordinates {m H N : ℕ} (S₀ : Set (ZMod m))
    (f : Fin N → Poly m H) (x : Fin N → Vec m H) (ms : List (Monomial H))
    (hmatching : PolyMatching S₀ f x) (hnodup : ms.Nodup)
    (hcover : ∀ i, ∀ v ∈ (f i).support, v ∈ ms) :
    SMatching (S₀ ∪ {0})
      (fun i => coefficientCoordinates (f i) ms)
      (fun i => evaluationCoordinates (x i) ms) := by
  classical
  refine ⟨by simp, ⟨?_, ?_⟩, ?_⟩
  · intro i
    rw [coefficient_dot_evaluation (f i) (x i) ms hnodup (hcover i)]
    exact hmatching.2.1 i
  · intro i j hij
    rw [coefficient_dot_evaluation (f i) (x j) ms hnodup (hcover i)]
    intro hzero
    exact hmatching.1 (hzero ▸ hmatching.2.2 j i hij.symm)
  · intro i j hij
    rw [coefficient_dot_evaluation (f i) (x j) ms hnodup (hcover i)]
    exact Or.inl (hmatching.2.2 j i hij.symm)

end CatalyticTreeEval.Main

open CatalyticTreeEval.Main

theorem solution {m H N : ℕ} (S₀ : Set (ZMod m))
    (f : Fin N → Poly m H) (x : Fin N → Vec m H) (ms : List (Monomial H))
    (hmatching : PolyMatching S₀ f x) (hnodup : ms.Nodup)
    (hcover : ∀ i, ∀ v ∈ (f i).support, v ∈ ms) :
    SMatching (S₀ ∪ {0})
      (fun i => coefficientCoordinates (f i) ms)
      (fun i => evaluationCoordinates (x i) ms) := by
  exact polynomial_matching_coordinates S₀ f x ms hmatching hnodup hcover
