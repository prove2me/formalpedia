-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan.eq_zero_of_tan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:46:23.303724+00:00
-- url     : https://prove2.me/submissions/6fb05e0b-eb14-4313-b142-34b37501b201

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqTan
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqTan_jetTan_alt
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR IsUnivChart sp spMap spMap_comp comp_one')
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
private theorem sub_C_mem_lemma {κ : Type} (r : MvPolynomial κ R) : r - C (constantCoeff r) ∈ orig R κ := by
  refine MvPolynomial.induction_on (motive := fun r => r - C (constantCoeff r) ∈ orig R κ) r ?_ ?_ ?_
  · intro a
    simp
  · intro p q hp hq
    have e : p + q - C (constantCoeff (p + q)) = (p - C (constantCoeff p)) + (q - C (constantCoeff q)) := by
      rw [map_add, map_add]
      ring
    rw [e]
    exact add_mem hp hq
  · intro p i _
    have e : p * X i - C (constantCoeff (p * X i)) = p * X i := by simp
    rw [e]
    exact Ideal.mul_mem_left _ _ (by first | exact Ideal.subset_span ⟨i, rfl⟩ | (unfold orig; exact Ideal.subset_span ⟨i, rfl⟩))
private theorem aug_mk_lemma_2 {κ : Type} (r : MvPolynomial κ R) :
    (jetAug : Jet R κ (0 + 1) →ₐ[R] R) (Ideal.Quotient.mk (orig R κ ^ (0 + 1 + 1)) r) = constantCoeff r := by
  have e : (jetAug : Jet R κ (0 + 1) →ₐ[R] R) (Ideal.Quotient.mk (orig R κ ^ (0 + 1 + 1)) r)
      = (aeval fun _ : κ => (0 : R)) r := by
    first | rfl | simp [jetAug, liftJet]
  rw [e]
  refine MvPolynomial.induction_on (motive := fun r => (aeval fun _ : κ => (0 : R)) r = constantCoeff r) r ?_ ?_ ?_
  · intro a
    simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro p i _
    simp
private theorem orig_sq_lemma_3 {κ : Type} : orig R κ ^ (0 + 1 + 1) = orig R κ * orig R κ := by
  first | exact pow_two _ | rw [pow_succ, pow_succ, pow_zero, one_mul]
private theorem mul_zz_lemma_4 {κ : Type} (c : Jet R κ (0 + 1)) (i : κ) :
    c * zz (0 + 1) i = algebraMap R (Jet R κ (0 + 1)) ((jetAug : Jet R κ (0 + 1) →ₐ[R] R) c) * zz (0 + 1) i := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [aug_mk_lemma_2]
  change Ideal.Quotient.mk (orig R κ ^ (0 + 1 + 1)) r * Ideal.Quotient.mk (orig R κ ^ (0 + 1 + 1)) (X i)
    = Ideal.Quotient.mk (orig R κ ^ (0 + 1 + 1)) (C (constantCoeff r)) * Ideal.Quotient.mk (orig R κ ^ (0 + 1 + 1)) (X i)
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← sub_mul, orig_sq_lemma_3]
  exact Ideal.mul_mem_mul (sub_C_mem_lemma r) (by first | exact Ideal.subset_span ⟨i, rfl⟩ | (unfold orig; exact Ideal.subset_span ⟨i, rfl⟩))
section Univ
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G}
  (hx : IsUnivChart G n x)
include hx
end Univ
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR IsUnivChart sp spMap spMap_comp comp_one')
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] (p : Jet R κ (0 + 1)) (hp : p ∈ Ij R κ (0 + 1))
    (ht : ∀ ℓ, (jetTan ℓ : Jet R κ (0 + 1) →ₐ[R] DualNumber R) p = 0) : p = 0 := by
  have hp' : p ∈ Ideal.span (Set.range (zz (R := R) (κ := κ) (0 + 1))) := hp
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hp'
  have e : ∑ i, c i * zz (0 + 1) i
      = ∑ i, algebraMap R (Jet R κ (0 + 1)) ((jetAug : Jet R κ (0 + 1) →ₐ[R] R) (c i)) * zz (0 + 1) i :=
    Finset.sum_congr rfl fun i _ => mul_zz_lemma_4 (c i) i
  rw [e] at ht ⊢
  have ha : ∀ i, (jetAug : Jet R κ (0 + 1) →ₐ[R] R) (c i) = 0 := by
    intro ℓ
    have h := ht ℓ
    simp only [map_sum, map_mul, AlgHom.commutes, jetTan_alt, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h
    first
      | (rw [← Algebra.smul_def] at h; simpa using congrArg TrivSqZeroExt.snd h)
      | simpa using congrArg TrivSqZeroExt.snd h
  simp only [ha, map_zero, zero_mul, Finset.sum_const_zero]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan
