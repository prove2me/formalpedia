-- Prove2me | solution 1 for Formalism.HermitianLattices.ModelCocycles.isotropic_vector_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:56.618487+00:00
-- url     : https://prove2.me/submissions/4184df6e-3f9e-48e4-bcfe-c2669f841259

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ModelCocycleExponent
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_TeichmullerUnitAllPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ModelCocycles
open Finset Formalism.HermitianLattices.IntegralLatticeDensity
namespace Formalism.HermitianLattices.ModelCocycles
theorem _root_.solution : IsotropicZero := by
  classical
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm hinj hnm hadd hadj hφ n ι _ _ f hiso t
  have symm : ∀ a b, cob φ a b = cob φ b a := by
    intro a b; unfold cob; rw [add_comm a b]; abel
  have hadd2 : ∀ a b b', cob φ a (b + b') = cob φ a b + cob φ a b' := by
    intro a b b'; rw [symm, hadd, symm b, symm b']
  have nm0 : nm 0 = 0 := hinj (by rw [hnm, map_zero, mul_zero])
  have φ0 : φ 0 = 0 := by
    have := hφ 0 0; rwa [zero_smul, nm0, zero_smul] at this
  let c : M → M →+ Q := fun a => AddMonoidHom.mk' (fun b => cob φ a b) (hadd2 a)
  have hc : ∀ a b, c a b = cob φ a b := fun _ _ => rfl
  have key : ∀ s : Finset ι, ∑ i, φ (∑ e ∈ s, f e i • t e) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [φ0]
    | insert a s ha ih =>
      have e1 : ∀ i, φ (∑ e ∈ insert a s, f e i • t e) =
          cob φ (f a i • t a) (∑ e ∈ s, f e i • t e) + φ (f a i • t a) + φ (∑ e ∈ s, f e i • t e) := by
        intro i; rw [Finset.sum_insert ha]; unfold cob; abel
      simp only [e1, Finset.sum_add_distrib, ih, add_zero]
      have e2 : ∑ i, φ (f a i • t a) = 0 := by
        simp only [hφ]
        rw [← Finset.sum_smul]
        have : ∑ i, nm (f a i) = 0 := hinj (by rw [map_sum, map_zero]; simp only [hnm]; exact hiso a a)
        rw [this, zero_smul]
      have e3 : ∑ i, cob φ (f a i • t a) (∑ e ∈ s, f e i • t e) = 0 := by
        have : ∀ i, cob φ (f a i • t a) (∑ e ∈ s, f e i • t e) =
            ∑ e ∈ s, c (t a) ((star (f a i) * f e i) • t e) := by
          intro i
          rw [hadj, ← hc, Finset.smul_sum, map_sum]
          simp only [smul_smul]
        simp only [this]
        rw [Finset.sum_comm]
        apply Finset.sum_eq_zero
        intro e _
        rw [← map_sum, ← Finset.sum_smul, hiso, zero_smul, map_zero]
      rw [e2, e3, add_zero]
  simpa using key Finset.univ
end Formalism.HermitianLattices.ModelCocycles
