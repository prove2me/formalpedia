-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.KP.tensorMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:42.494418+00:00
-- url     : https://prove2.me/submissions/9d0b55f4-c5b3-4e92-963a-c99a895aa647

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_TensorKP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial
namespace Formalism.MainNotions.flipOneThree.Pf.KP
private theorem tm_comap {S α : Type} [Fintype S] [DecidableEq S] (n : S → α →₀ ℕ) (s : S) :
    (∑ t, Finsupp.mapDomain (fun v => (t, v)) (n t)).comapDomain (fun v => (s, v))
      (Prod.mk_right_injective s).injOn = n s := by
  ext a
  rw [Finsupp.comapDomain_apply, Finsupp.finsetSum_apply, Finset.sum_eq_single s]
  · exact Finsupp.mapDomain_apply (Prod.mk_right_injective s) (n s) a
  · intro t _ hts
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨v, hv⟩
    exact hts (congrArg Prod.fst hv)
  · intro h
    exact absurd (Finset.mem_univ s) h
end Formalism.MainNotions.flipOneThree.Pf.KP
open MvPolynomial
namespace Formalism.MainNotions.flipOneThree.Pf.KP
end Formalism.MainNotions.flipOneThree.Pf.KP
open MvPolynomial
namespace Formalism.MainNotions.flipOneThree.Pf.KP
end Formalism.MainNotions.flipOneThree.Pf.KP
open MvPolynomial
namespace Formalism.MainNotions.flipOneThree.Pf.KP
end Formalism.MainNotions.flipOneThree.Pf.KP
end

set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.KP
namespace Formalism.MainNotions.flipOneThree.Pf.KP
theorem _root_.solution {K : Type} [Field K] {S α B : Type} [Fintype S] [DecidableEq S] [CommRing B]
    [Algebra K B] (g : S → MvPolynomial α K →ₗ[K] B) :
    ∃ F : MvPolynomial (S × α) K →ₗ[K] B, ∀ P : S → MvPolynomial α K,
      F (∏ s, rename (fun v => (s, v)) (P s)) = ∏ s, g s (P s) := by
  classical
  let F : MvPolynomial (S × α) K →ₗ[K] B :=
    (MvPolynomial.basisMonomials (S × α) K).constr K
      (fun m => ∏ s, g s (monomial (m.comapDomain (fun v => (s, v))
        (Prod.mk_right_injective s).injOn) 1))
  refine ⟨F, ?_⟩
  have key : F.compMultilinearMap
      ((MultilinearMap.mkPiAlgebra K S (MvPolynomial (S × α) K)).compLinearMap
        (fun s => (rename (R := K) (fun v : α => (s, v))).toLinearMap)) =
      (MultilinearMap.mkPiAlgebra K S B).compLinearMap g := by
    apply Module.Basis.ext_multilinear (fun _ => MvPolynomial.basisMonomials α K)
    intro n
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, coe_basisMonomials,
      rename_monomial]
    rw [← monomial_sum_one]
    have h := (MvPolynomial.basisMonomials (S × α) K).constr_basis K
      (fun m => ∏ s, g s (monomial (m.comapDomain (fun v => (s, v))
        (Prod.mk_right_injective s).injOn) 1))
      (∑ t, Finsupp.mapDomain (fun v => (t, v)) (n t))
    rw [coe_basisMonomials] at h
    refine h.trans ?_
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [tm_comap]
  intro P
  have := congrArg (fun f => f P) key
  simpa using this
end Formalism.MainNotions.flipOneThree.Pf.KP
