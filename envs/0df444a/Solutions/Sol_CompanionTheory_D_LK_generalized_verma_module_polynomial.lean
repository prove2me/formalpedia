-- Prove2me | solution 1 for CompanionTheory.D.LK.generalized_verma_module_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:14:39.564069+00:00
-- url     : https://prove2.me/submissions/5ffbbbed-94d9-4467-a2d5-9cf62d0f7db6

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KummerLiftedCocycleImageEqPicardClass
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_GeneralizedVermaModulePolynomial
import Theorems.Thm_CompanionTheory_D_LK_deg_X_pderiv
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_DSVerma_dd_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_DSVerma_dd_yy
import Theorems.Thm_GlobalTheory_CompanionTheory_DSVerma_glRel_abstract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset MvPolynomial
open scoped TensorProduct
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Formalism.REAL GlobalTheory.CompanionTheory.DSVerma GlobalTheory.CompanionTheory.DSCover
open CompanionTheory.D.DSIC (KRel NC)
namespace CompanionTheory.D.LK
theorem _root_.solution : Verma2 := by
  intro n ε
  let u : Fin n → Fin n → Module.End ℂ (MvPolynomial (NC ε) ℂ) := fun a c => (if a = c then 1 else 0) - dd ε a c
  let v : Fin n → Fin n → Module.End ℂ (MvPolynomial (NC ε) ℂ) := fun a c => (if a = c then 1 else 0) + dd ε a c
  have hδ : ∀ (a c : Fin n) (T : Module.End ℂ (MvPolynomial (NC ε) ℂ)),
      Commute (if a = c then 1 else 0) T := by
    intro a c T
    split_ifs <;> simp
  refine ⟨fun c d => ∑ i : NC ε, yy i * (u i.1.1 c * v d i.1.2), ?_, ?_, ?_, ?_⟩
  · intro c d e f
    refine glRel_abstract yy u v ?_ ?_ ?_ ?_ ?_ ?_ ?_ c d e f
    · intro i j
      refine LinearMap.ext fun f => ?_
      simp [yy, mul_left_comm]
    · intro a b c d
      exact (hδ _ _ _).sub_left ((hδ _ _ _).symm.sub_right (dd_comm _ _ _ _))
    · intro a b c d
      exact (hδ _ _ _).sub_left ((hδ _ _ _).symm.add_right (dd_comm _ _ _ _))
    · intro a b c d
      exact (hδ _ _ _).add_left ((hδ _ _ _).symm.add_right (dd_comm _ _ _ _))
    · intro a c j
      rw [← dd_yy]
      simp only [u, sub_mul, mul_sub, (hδ a c (yy j)).eq]
      abel
    · intro a c j
      rw [← dd_yy]
      simp only [v, add_mul, mul_add, (hδ a c (yy j)).eq]
      abel
    · intro d e
      have h0 : ¬(ε d = true ∧ ε e = false) → dd ε d e = 0 := fun h => dif_neg h
      simp only [u, v]
      generalize dd ε d e = T at *
      by_cases hde : d = e
      · subst hde
        cases h : ε d <;> simp_all
      · cases h : ε d <;> cases h' : ε e <;> simp_all
  · intro i f
    have hu : ∀ j : NC ε, u j.1.1 i.1.1 = if j.1.1 = i.1.1 then 1 else 0 := by
      intro j
      simp [u, dd, i.2.1]
    have hv : ∀ j : NC ε, v i.1.2 j.1.2 = if i.1.2 = j.1.2 then 1 else 0 := by
      intro j
      simp [v, dd, i.2.2]
    simp only [hu, hv]
    rw [Finset.sum_eq_single i]
    · simp [yy]
    · intro j _ hj
      split_ifs with h1 h2
      · exact absurd (Subtype.ext (Prod.ext h1 h2.symm)) hj
      all_goals simp
    · simp
  · intro a b f
    simp [yy, LinearMap.sum_apply, map_sum]

  · intro c d f h
    have hd : ∀ (i : NC ε) (a b : Fin n), (X i * dd ε a b f).totalDegree ≤ f.totalDegree := fun i a b => by
      unfold dd
      split_ifs
      · exact deg_X_pderiv _ _ f
      · simp
    rw [LinearMap.sum_apply]
    refine totalDegree_finsetSum_le fun i _ => ?_
    have i1 := i.2.1
    have i2 := i.2.2
    cases hc : ε c
    · have e1 : i.1.1 ≠ c := fun e => by rw [e, hc] at i1; exact Bool.noConfusion i1
      have e2 : dd ε d i.1.2 = 0 := dif_neg (by simp [← h, hc])
      simp only [u, v, if_neg e1, e2, yy, Module.End.mul_apply, add_zero, zero_sub, LinearMap.neg_apply,
        LinearMap.mulLeft_apply]
      split_ifs
      · rw [mul_neg, totalDegree_neg]; exact hd _ _ _
      · simp
    · have e1 : d ≠ i.1.2 := fun e => by rw [← e, ← h, hc] at i2; exact Bool.noConfusion i2
      have e2 : dd ε i.1.1 c = 0 := dif_neg (by simp [hc])
      simp only [u, v, if_neg e1, e2, yy, Module.End.mul_apply, zero_add, sub_zero, LinearMap.mulLeft_apply]
      split_ifs
      · exact hd _ _ _
      · simp
end CompanionTheory.D.LK
