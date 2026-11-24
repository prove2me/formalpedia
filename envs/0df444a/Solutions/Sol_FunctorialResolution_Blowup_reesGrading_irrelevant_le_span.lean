-- Prove2me | solution 1 for FunctorialResolution.Blowup.reesGrading_irrelevant_le_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:46:31.3834+00:00
-- url     : https://prove2.me/submissions/221f7a5a-948b-400b-bc45-444d6a46414f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial
namespace FunctorialResolution.Blowup
variable {R : Type*} [CommRing R]
private theorem reesComponent_coe (I : Ideal R) (p : ↥(reesAlgebra I)) (i : ℕ) :
    ((reesMonomialOfCoeff I p i : ↥(reesAlgebra I)) : R[X])
      = Polynomial.monomial i ((p : R[X]).coeff i) := rfl
private theorem reesComponent_mem_reesGrading (I : Ideal R) (p : ↥(reesAlgebra I)) (i : ℕ) :
    reesMonomialOfCoeff I p i ∈ reesGrading I i := by
  refine (mem_reesGrading_iff_coeff I i _).2 fun j hj => ?_
  rw [reesComponent_coe, Polynomial.coeff_monomial, if_neg (Ne.symm hj)]
private theorem eq_sum_reesComponent (I : Ideal R) (p : ↥(reesAlgebra I)) :
    p = ∑ i ∈ (p : R[X]).support, reesMonomialOfCoeff I p i := by
  have hval : ∀ x y : ↥(reesAlgebra I),
      (reesAlgebra I).val x = (reesAlgebra I).val y → x = y := fun _ _ h => Subtype.ext h
  exact hval _ _ (by rw [map_sum]; exact Polynomial.as_sum_support _)
private theorem mem_span_reesGenerator_of_eq_monomial_succ (I : Ideal R) :
    ∀ (n : ℕ) (r : R), r ∈ I ^ (n + 1) →
      ∀ x : ↥(reesAlgebra I), (x : R[X]) = Polynomial.monomial (n + 1) r →
        x ∈ Ideal.span (Set.range (reesGenerator I)) := by
  intro n
  induction n with
  | zero =>
    intro r hr x hx
    have hr' : r ∈ I := by simpa using hr
    have hxe : x = reesGenerator I ⟨r, hr'⟩ := Subtype.ext (hx.trans rfl)
    rw [hxe]
    exact Ideal.subset_span (Set.mem_range_self _)
  | succ n ih =>
    intro r hr
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on'
      (C := fun s _ => ∀ x : ↥(reesAlgebra I),
        (x : R[X]) = Polynomial.monomial (n + 1 + 1) s →
          x ∈ Ideal.span (Set.range (reesGenerator I))) ?_ ?_ hr
    · intro m hm a ha x hx
      have hy : reesMonomial I (n + 1) m hm ∈ Ideal.span (Set.range (reesGenerator I)) :=
        ih m hm (reesMonomial I (n + 1) m hm) rfl
      have hco : ((reesMonomial I (n + 1) m hm * reesGenerator I ⟨a, ha⟩ : ↥(reesAlgebra I)) : R[X])
          = Polynomial.monomial (n + 1 + 1) (m * a) := by
        show (Polynomial.monomial (n + 1) m : R[X]) * Polynomial.monomial 1 a
            = Polynomial.monomial (n + 1 + 1) (m * a)
        rw [Polynomial.monomial_mul_monomial]
      have hxe : x = reesMonomial I (n + 1) m hm * reesGenerator I ⟨a, ha⟩ :=
        Subtype.ext (hx.trans hco.symm)
      rw [hxe]
      exact Ideal.mul_mem_right _ _ hy
    · intro s hs t ht hs' ht' x hx
      have hsm : s ∈ I ^ (n + 1 + 1) := by rw [pow_succ]; exact hs
      have htm : t ∈ I ^ (n + 1 + 1) := by rw [pow_succ]; exact ht
      have hxe : x = reesMonomial I (n + 1 + 1) s hsm
          + reesMonomial I (n + 1 + 1) t htm := by
        refine Subtype.ext ?_
        show (x : R[X]) = Polynomial.monomial (n + 1 + 1) s + Polynomial.monomial (n + 1 + 1) t
        rw [hx]
        exact map_add (Polynomial.monomial (R := R) (n + 1 + 1)) s t
      rw [hxe]
      exact add_mem (hs' _ rfl) (ht' _ rfl)
end FunctorialResolution.Blowup
end

set_option autoImplicit false
open Polynomial
open FunctorialResolution FunctorialResolution.Blowup
variable {R : Type*} [CommRing R]
namespace FunctorialResolution.Blowup
theorem _root_.solution (I : Ideal R) :
    (HomogeneousIdeal.irrelevant (reesGrading I)).toIdeal ≤
      Ideal.span (Set.range (reesGenerator I)) := by
  intro p hp
  have hp1 : p ∈ HomogeneousIdeal.irrelevant (reesGrading I) := hp
  rw [HomogeneousIdeal.mem_irrelevant_iff] at hp1
  have hsum : p = ∑ i ∈ (p : R[X]).support, reesMonomialOfCoeff I p i := eq_sum_reesComponent I p
  have hmapsum : (GradedRing.proj (reesGrading I) 0)
        (∑ i ∈ (p : R[X]).support, reesMonomialOfCoeff I p i)
      = ∑ i ∈ (p : R[X]).support, (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p i) :=
    map_sum (GradedRing.proj (reesGrading I) 0) (fun i => reesMonomialOfCoeff I p i)
      ((p : R[X]).support)
  have hprojsum : ∑ i ∈ (p : R[X]).support,
      (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p i) = 0 := by
    rw [← hmapsum, ← hsum]
    exact hp1
  have hsingle : ∑ i ∈ (p : R[X]).support,
      (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p i)
      = (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p 0) := by
    refine Finset.sum_eq_single 0 (fun i _ hi => ?_) (fun h0 => ?_)
    · rw [GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_ne (reesGrading I) (reesComponent_mem_reesGrading I p i) hi
    · have hc : (p : R[X]).coeff 0 = 0 :=
        not_not.mp (fun h => h0 (Polynomial.mem_support_iff.mpr h))
      have hz : reesMonomialOfCoeff I p 0 = 0 := by
        refine Subtype.ext ?_
        show Polynomial.monomial 0 ((p : R[X]).coeff 0) = (0 : R[X])
        rw [hc, map_zero]
      rw [hz, map_zero]
  have hz0 : reesMonomialOfCoeff I p 0 = 0 := by
    have h1 : (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p 0) = 0 := by
      rw [← hsingle]
      exact hprojsum
    rw [GradedRing.proj_apply,
      DirectSum.decompose_of_mem_same (reesGrading I) (reesComponent_mem_reesGrading I p 0)] at h1
    exact h1
  rw [hsum]
  refine sum_mem fun i _ => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [hz0]
    exact zero_mem _
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    exact mem_span_reesGenerator_of_eq_monomial_succ I k ((p : R[X]).coeff (k + 1))
      (coeff_mem_pow I p (k + 1)) (reesMonomialOfCoeff I p (k + 1))
      (reesComponent_coe I p (k + 1))
end FunctorialResolution.Blowup
