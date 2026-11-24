-- Prove2me | solution 1 for Formalism.UG.P.dual_weyl_module_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:07.693623+00:00
-- url     : https://prove2.me/submissions/80985049-5d8e-4f29-8795-e12fa4e9730b

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_DualWeylModuleStable
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
noncomputable section
open MvPolynomial
namespace Formalism.UG.P
private theorem isWeightedHomogeneous_pow' {σ R M : Type*} [CommRing R] [AddCommMonoid M] {w : σ → M}
    {φ : MvPolynomial σ R} {m : M} (h : IsWeightedHomogeneous w φ m) (k : ℕ) :
    IsWeightedHomogeneous w (φ ^ k) (k • m) := by
  induction k with
  | zero =>
    first
    | simpa using isWeightedHomogeneous_C w (1 : R)
    | simpa using isWeightedHomogeneous_one R w
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact ih.mul h
private theorem isWeightedHomogeneous_algHom_apply {σ R M : Type*} [CommRing R] [AddCommMonoid M] (w : σ → M)
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hφ : ∀ v, IsWeightedHomogeneous w (φ (X v)) (w v)) (f : MvPolynomial σ R) (m : M)
    (hf : IsWeightedHomogeneous w f m) : IsWeightedHomogeneous w (φ f) m := by
  rw [← mem_weightedHomogeneousSubmodule, f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [mem_weightedHomogeneousSubmodule]
  have hdw : Finsupp.weight w d = m := hf (mem_support_iff.mp hd)
  have hprod : IsWeightedHomogeneous w (φ (d.prod fun n e => X n ^ e)) (Finsupp.weight w d) := by
    rw [Finsupp.prod, map_prod, Finsupp.weight_apply, Finsupp.sum]
    apply IsWeightedHomogeneous.prod
    intro v _
    rw [map_pow]
    exact isWeightedHomogeneous_pow' (hφ v) (d v)
  have hC : φ (C (coeff d f)) = C (coeff d f) := by
    rw [← MvPolynomial.algebraMap_eq]
    exact φ.commutes _
  rw [monomial_eq, map_mul, hC, ← hdw, ← zero_add (Finsupp.weight w d)]
  exact (isWeightedHomogeneous_C w _).mul hprod
end Formalism.UG.P
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.DwStable := by
  intro R _ r n ν g f hf
  unfold Formalism.UG.dwAct
  generalize ((g⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) = M
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf ⊢
  rw [Submodule.mem_inf] at hf ⊢
  obtain ⟨hw, hk⟩ := hf
  constructor
  · rw [mem_weightedHomogeneousSubmodule] at hw ⊢
    apply isWeightedHomogeneous_algHom_apply _ _ _ f ν hw
    intro v
    simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_X]
    rw [← mem_weightedHomogeneousSubmodule]
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [mem_weightedHomogeneousSubmodule]
    have h1 := (isWeightedHomogeneous_C (Formalism.GradedWeylDivisibility.colW r n) (M v.1 b)).mul
      (isWeightedHomogeneous_X R (Formalism.GradedWeylDivisibility.colW r n) (b, v.2))
    rw [zero_add] at h1
    exact h1
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      AlgHom.toLinearMap_apply, sub_eq_zero] at hk ⊢
    intro l j hlj
    have h1 : (Formalism.GradedWeylDivisibility.colAddGen R (r := r) l j).comp (Formalism.GradedWeylDivisibility.rowAct R (n := n) M) =
        (aeval (fun o : Option (Fin r × Fin n) => o.elim (X none)
          (fun v => ∑ b : Fin r, C (M v.1 b) * X (some (b, v.2))))).comp
          (Formalism.GradedWeylDivisibility.colAddGen R (r := r) l j) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, k⟩
      by_cases hkj : k = j
      · subst hkj
        simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.colAddGen, aeval_X, map_sum, map_mul,
          aeval_C, map_add, if_true, Option.elim, algebraMap_eq]
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro b _
        ring
      · simp [Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.colAddGen, hkj]
    have h2 : (aeval (fun o : Option (Fin r × Fin n) => o.elim (X none)
          (fun v => ∑ b : Fin r, C (M v.1 b) * X (some (b, v.2))))).comp
          (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))) =
        (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).comp
          (Formalism.GradedWeylDivisibility.rowAct R (n := n) M) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, k⟩
      simp [Formalism.GradedWeylDivisibility.rowAct]
    have e1 := DFunLike.congr_fun h1 f
    have e2 := DFunLike.congr_fun h2 f
    simp only [AlgHom.comp_apply] at e1 e2
    rw [e1, hk l j hlj, e2]
end Formalism.UG.P
