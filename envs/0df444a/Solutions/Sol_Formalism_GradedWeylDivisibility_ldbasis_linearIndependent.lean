-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldbasis_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:06.420158+00:00
-- url     : https://prove2.me/submissions/dca68f0c-ba7c-416d-b873-a0bc5d6877d9

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.GradedWeylDivisibility
open scoped MonomialOrder
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {σ R ι : Type*} [CommRing R] (o : MonomialOrder σ)
    (v : ι → MvPolynomial σ R) (hinj : Function.Injective fun i => o.degree (v i))
    (hlc : ∀ i, o.leadingCoeff (v i) = 1) : LinearIndependent R v := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  have htne : (s.filter fun j => g j ≠ 0).Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  obtain ⟨j, hj, hjmax⟩ :=
    (s.filter fun j => g j ≠ 0).exists_max_image (fun j => o.toSyn (o.degree (v j))) htne
  have hcoeff := congrArg (MvPolynomial.coeff (o.degree (v j))) hsum
  rw [coeff_zero, coeff_sum, Finset.sum_eq_single j] at hcoeff
  · rw [coeff_smul, smul_eq_mul] at hcoeff
    have hone : (v j).coeff (o.degree (v j)) = 1 := hlc j
    rw [hone, mul_one] at hcoeff
    exact (Finset.mem_filter.mp hj).2 hcoeff
  · intro k hk hkj
    rw [coeff_smul]
    by_cases hgk : g k = 0
    · rw [hgk, zero_smul]
    · have hle := hjmax k (Finset.mem_filter.mpr ⟨hk, hgk⟩)
      have hne : o.degree (v k) ≠ o.degree (v j) := fun h => hkj (hinj h)
      have hlt : o.toSyn (o.degree (v k)) < o.toSyn (o.degree (v j)) :=
        lt_of_le_of_ne hle (fun h => hne (o.toSyn.injective h))
      rw [o.coeff_eq_zero_of_lt hlt, smul_zero]
  · intro hj'
    exact absurd (Finset.mem_filter.mp hj).1 hj'
end Formalism.GradedWeylDivisibility
