-- Prove2me | solution 1 for CompanionTheory.D.LK.exists_poly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:22.562239+00:00
-- url     : https://prove2.me/submissions/331596bc-d647-4143-9544-399ee42c4d8f

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialCommutesWeightOperator
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KTypeCount
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_DoubleSumReduceSecond
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_FilterAll
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car
open Formalism.REAL (GlRel KHighest IsWeight CasK)
open PI.UpqRep (rhoC nsq lowK)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
variable {n : ℕ} {ε : Fin n → Bool}
namespace CompanionTheory.D.LK
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (T : Module.End ℂ V)
    (hT : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) (W : Submodule ℂ V) [FiniteDimensional ℂ W] (hW : ∀ x ∈ W, T x ∈ W) (s : ℝ) :
    ∃ q : Polynomial ℂ, ∀ x ∈ W, ∀ y, y = x + Polynomial.aeval T q (T x - (s : ℂ) • x) → T y = (s : ℂ) • y := by
  classical
  have hs : (T.restrict hW).IsSymmetric := fun x y => hT x y
  let ev := hs.eigenvalues rfl
  let p : Polynomial ℂ := Lagrange.basis (insert (s : ℂ) (univ.image fun i => (ev i : ℂ))) id (s : ℂ)
  have hp1 : p.eval (s : ℂ) = 1 := Lagrange.eval_basis_self (v := id) (Set.injOn_id _) (mem_insert_self _ _)
  obtain ⟨q, hq⟩ : Polynomial.X - Polynomial.C (s : ℂ) ∣ p - 1 := Polynomial.dvd_iff_isRoot.2 (by simp [hp1])
  refine ⟨q, fun x hx y hy => ?_⟩
  have e : y = Polynomial.aeval T p x := by
    rw [hy, eq_add_of_sub_eq' hq, mul_comm]
    simp [Module.algebraMap_end_apply]
  rw [e, show x = ∑ i, (hs.eigenvectorBasis rfl).repr ⟨x, hx⟩ i • (hs.eigenvectorBasis rfl i : V) by
    simpa using (congrArg Subtype.val ((hs.eigenvectorBasis rfl).sum_repr ⟨x, hx⟩)).symm]
  simp only [map_sum, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : T (hs.eigenvectorBasis rfl i : V) = (ev i : ℂ) • (hs.eigenvectorBasis rfl i : V) :=
    congrArg Subtype.val (hs.apply_eigenvectorBasis rfl i)
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul h1, map_smul, h1]
  by_cases h : (ev i : ℂ) = s
  · rw [h]; module
  · have : p.eval (ev i : ℂ) = 0 := Lagrange.eval_basis_of_ne (v := id) (Ne.symm h)
      (mem_insert_of_mem (mem_image_of_mem _ (mem_univ i)))
    simp [this]
end CompanionTheory.D.LK
