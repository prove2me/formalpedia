-- Prove2me | solution 1 for CauchyRiemannIndex.periodic_weak_solution_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T21:09:51.091216+00:00
-- url     : https://prove2.me/submissions/b03ce136-434a-4f26-a560-8e5fa13614fb

import Theorems.Thm_CauchyRiemannIndex_exists_periodic_solution_bound
import Theorems.Thm_CauchyRiemannIndex_weak_identity_of_contDiff_one
import Theorems.Thm_CauchyRiemannIndex_abs_le_of_forall_abs_integral_mul_le
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace CauchyRiemannIndex

lemma crPerP_norm_le_sum {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖x‖ ≤ ∑ i, |x i| := by
  conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr x]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  simp [norm_smul]

theorem solution_aux (n : ℕ) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    (hnd : IsNondegenerate Sinf) :
    ∃ C : ℝ, ∀ η f : ℝ → Vec n, IntegrableOn η (Set.Ico 0 1) → IntegrableOn f (Set.Ico 0 1) →
      (∀ ψ : ℝ → Vec n, ContDiff ℝ ∞ ψ → Function.Periodic ψ 1 →
        ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (Matrix.toEuclideanLin (J₀ n) (deriv ψ t) +
          Matrix.toEuclideanLin (Sinf t) (ψ t)) (η t) =
        ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (ψ t) (f t)) →
      ∀ᵐ t ∂(volume.restrict (Set.Ico (0 : ℝ) 1)), ‖η t‖ ≤ C * ∫ t in Set.Ico (0 : ℝ) 1, ‖f t‖ := by
  obtain ⟨C, hC⟩ := exists_periodic_solution_bound n Sinf hS hnd
  set C' := max C 0
  refine ⟨(Fintype.card (Fin n ⊕ Fin n) : ℝ) * C', fun η f hη hf hw => ?_⟩
  have hw1 := weak_identity_of_contDiff_one n Sinf hS.1 η f hη hf hw
  set F := ∫ t in Set.Ico (0 : ℝ) 1, ‖f t‖ with hF
  have hcomp : ∀ i : Fin n ⊕ Fin n, ∀ᵐ t ∂(volume.restrict (Set.Ico (0 : ℝ) 1)),
      |η t i| ≤ C' * F := by
    intro i
    have hint : IntegrableOn (fun t => η t i) (Set.Ico 0 1) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hη
    refine abs_le_of_forall_abs_integral_mul_le (fun t => η t i) (C' * F) hint ?_
    intro φ hφ hφp
    let e : Vec n := EuclideanSpace.single i 1
    let g : ℝ → Vec n := fun t => φ t • e
    obtain ⟨ψ, hcd, hper, hsol, hb⟩ := hC g (hφ.smul continuous_const)
      (fun t => by simp [g, hφp t])
    have hG : ∫ τ in Set.Ico (0 : ℝ) 1, ‖g τ‖ = ∫ τ in Set.Ico (0 : ℝ) 1, |φ τ| := by
      congr 1; funext τ; simp [g, e, norm_smul]
    have hb' : ∀ t, ‖ψ t‖ ≤ C' * ∫ τ in Set.Ico (0 : ℝ) 1, |φ τ| := fun t => by
      rw [← hG]
      exact (hb t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (MeasureTheory.integral_nonneg fun _ => norm_nonneg _))
    have hid := hw1 ψ hcd hper
    have hL : ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (Matrix.toEuclideanLin (J₀ n) (deriv ψ t) +
          Matrix.toEuclideanLin (Sinf t) (ψ t)) (η t) =
        ∫ t in Set.Ico (0 : ℝ) 1, φ t * η t i := by
      congr 1; funext t
      rw [hsol t]
      simp [g, e, real_inner_smul_left, EuclideanSpace.inner_single_left]
    rw [hL] at hid
    rw [hid]
    calc |∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (ψ t) (f t)|
        ≤ ∫ t in Set.Ico (0 : ℝ) 1, (C' * ∫ τ in Set.Ico (0 : ℝ) 1, |φ τ|) * ‖f t‖ := by
          rw [← Real.norm_eq_abs]
          refine norm_integral_le_of_norm_le (hf.norm.const_mul _)
            (Eventually.of_forall fun t => ?_)
          exact (norm_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_right (hb' t) (norm_nonneg _))
      _ = C' * F * ∫ t in Set.Ico (0 : ℝ) 1, |φ t| := by
          rw [integral_const_mul, hF]; ring
  rw [← ae_all_iff] at hcomp
  filter_upwards [hcomp] with t ht
  calc ‖η t‖ ≤ ∑ i, |η t i| := crPerP_norm_le_sum (η t)
    _ ≤ ∑ _i : Fin n ⊕ Fin n, C' * F := Finset.sum_le_sum fun i _ => ht i
    _ = (Fintype.card (Fin n ⊕ Fin n) : ℝ) * C' * F := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

end CauchyRiemannIndex

open CauchyRiemannIndex in
theorem solution (n : ℕ) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    (hnd : IsNondegenerate Sinf) :
    ∃ C : ℝ, ∀ η f : ℝ → Vec n, IntegrableOn η (Set.Ico 0 1) → IntegrableOn f (Set.Ico 0 1) →
      (∀ ψ : ℝ → Vec n, ContDiff ℝ ∞ ψ → Function.Periodic ψ 1 →
        ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (Matrix.toEuclideanLin (J₀ n) (deriv ψ t) +
          Matrix.toEuclideanLin (Sinf t) (ψ t)) (η t) =
        ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (ψ t) (f t)) →
      ∀ᵐ t ∂(volume.restrict (Set.Ico (0 : ℝ) 1)), ‖η t‖ ≤ C * ∫ t in Set.Ico (0 : ℝ) 1, ‖f t‖ :=
  solution_aux n Sinf hS hnd
