-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.weylModuleRowDividedPowerStable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:16.918901+00:00
-- url     : https://prove2.me/submissions/229a4358-2f24-4943-a30c-99bb699b1874

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylRowDivStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial
noncomputable section
namespace Formalism.GradedWeylDivisibility
private theorem rowDiv_add_fock_space_tableaux (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f g : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (f + g) = rowDiv R a b k f + rowDiv R a b k g := by
  unfold rowDiv
  rw [map_add, Polynomial.coeff_add]
private theorem rowDiv_smul_fock_space_tableaux (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (c : R) (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (c • f) = c • rowDiv R a b k f := by
  unfold rowDiv
  rw [map_smul, Polynomial.coeff_smul]
end Formalism.GradedWeylDivisibility
end
end

set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : WeylRowDivStable := by
  unfold WeylRowDivStable
  intro R _ r n hn ν a b k f hf
  let L : MvPolynomial (Fin r × Fin n) R →ₗ[R] MvPolynomial (Fin r × Fin n) R :=
    { toFun := rowDiv R a b k
      map_add' := rowDiv_add_fock_space_tableaux R a b k
      map_smul' := rowDiv_smul_fock_space_tableaux R a b k }
  have key : weyl R r n hn ν ≤ (weyl R r n hn ν).comap L := by
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    exact Submodule.subset_span ⟨(a, b, k) :: w, rfl⟩
  exact key hf
end Formalism.GradedWeylDivisibility
