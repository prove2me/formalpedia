-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.monomial_mul_prod_binomial_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:40:15.768781+00:00
-- url     : https://prove2.me/submissions/cfcc7b20-d78e-4d3d-950f-c7f872630fe6

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionX
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_prod_monomial_eq_monomial_sum_prod
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sum_single_sourceVar_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.G
section mono
variable {B : Type*} [CommRing B] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
  (a b : Fin n) (t : B) (m : ι × Fin n →₀ ℕ)
variable {R : Type*} [CommRing R] (φ : R →+* B)
private theorem letterSign_pow_mul_choose_sourceExp (p : ι → ℕ) (l : ι) (hpl : p l ≤ sourceExp LL S a b m l) :
    letterSign B LL l ^ p l * ((sourceExp LL S a b m l).choose (p l) : B) =
      (if LL.vec l then ((m (l, b)).choose (p l) : B) else (-1 : B) ^ (p l) * ((m (l, a)).choose (p l) : B)) := by
  classical
  by_cases hS : l ∈ S
  · have he : sourceExp LL S a b m l = m (sourceVar LL a b l) := by
      unfold sourceExp
      rw [if_pos hS]
    rw [he]
    unfold sourceVar letterSign
    cases LL.vec l <;> simp
  · have he : sourceExp LL S a b m l = 0 := by
      unfold sourceExp
      rw [if_neg hS]
    rw [he] at hpl ⊢
    have hp0 : p l = 0 := by omega
    rw [hp0]
    simp
end mono
end Formalism.MainNotions.G.GLWeightTheory
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.G
variable {B : Type*} [CommRing B] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
  (a b : Fin n) (t : B) (m : ι × Fin n →₀ ℕ)
variable {R : Type*} [CommRing R] (φ : R →+* B)
namespace Formalism.MainNotions.G.GLWeightTheory
theorem _root_.solution (p : ι → ℕ) (hp : ∀ l, p l ≤ sourceExp LL S a b m l) :
    monomial (m - sourceVariableExponent LL S a b m) (1 : B) *
      ∏ l : ι, ((C (letterSign B LL l * t) * X (targetVar LL a b l)) ^ (p l) *
        X (sourceVar LL a b l) ^ (sourceExp LL S a b m l - p l) * (((sourceExp LL S a b m l).choose (p l) : ℕ) :
          MvPolynomial (ι × Fin n) B)) =
      C (t ^ (∑ l, p l)) * monomial (shiftedExponent LL a b m p) (rootShiftCoefficient B LL a b m p) := by
  classical
  have hfac : ∀ l : ι, (C (letterSign B LL l * t) * X (targetVar LL a b l)) ^ (p l) *
        X (sourceVar LL a b l) ^ (sourceExp LL S a b m l - p l) *
        (((sourceExp LL S a b m l).choose (p l) : ℕ) : MvPolynomial (ι × Fin n) B) =
      monomial (Finsupp.single (targetVar LL a b l) (p l) +
          Finsupp.single (sourceVar LL a b l) (sourceExp LL S a b m l - p l))
        ((letterSign B LL l * t) ^ (p l) * ((sourceExp LL S a b m l).choose (p l) : B)) := by
    intro l
    rw [← monomial_mul, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
    simp only [mul_pow, map_pow, map_mul, map_natCast]
    ring
  simp_rw [hfac]
  rw [prod_monomial_eq_monomial_sum_prod, monomial_mul, C_mul_monomial, one_mul]
  refine congrArg₂ (fun (s : ι × Fin n →₀ ℕ) (c : B) => (monomial s c : MvPolynomial (ι × Fin n) B)) ?_ ?_
  · have key : m - sourceVariableExponent LL S a b m +
        ∑ l : ι, Finsupp.single (sourceVar LL a b l) (sourceExp LL S a b m l - p l) =
        m - ∑ l : ι, Finsupp.single (sourceVar LL a b l) (p l) := by
      unfold sourceVariableExponent
      ext v
      rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.tsub_apply, sum_single_sourceVar_apply,
        sum_single_sourceVar_apply, sum_single_sourceVar_apply]
      split_ifs with h
      · have h1 := hp v.1
        have h2 : sourceExp LL S a b m v.1 ≤ m v := by
          unfold sourceExp
          split_ifs
          · exact (congrArg m h.symm).le
          · exact Nat.zero_le _
        omega
      · simp
    rw [Finset.sum_add_distrib, shiftedExponent, ← key, add_assoc,
      add_comm (∑ l : ι, Finsupp.single (targetVar LL a b l) (p l))]
  · unfold rootShiftCoefficient
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← letterSign_pow_mul_choose_sourceExp (B := B) LL S a b m p l (hp l)]
    ring
end Formalism.MainNotions.G.GLWeightTheory
