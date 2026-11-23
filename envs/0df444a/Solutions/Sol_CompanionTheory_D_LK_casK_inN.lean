-- Prove2me | solution 1 for CompanionTheory.D.LK.casK_inN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:14.540537+00:00
-- url     : https://prove2.me/submissions/4928f71e-7565-4246-9929-8f89cbd85521

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialCommutesWeightOperator
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KTypeCount
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_DoubleSumReduceSecond
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_FilterAll
import Theorems.Thm_CompanionTheory_D_LK_sum_pos
import Theorems.Thm_CompanionTheory_D_LK_wt_sum
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_LK_wt_om
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
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace CompanionTheory.D.LK
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ V} (hE : KRel ε E) (x : V) :
    InN ε E (CasK ε E x - (∑ c, E c c (E c c x) - ∑ c, ((2 * rhoC ε c : ℝ) : ℂ) • E c c x)) := by
  refine ⟨fun i => (2 : ℂ) • E i.1.2 i.1.1 x, ?_⟩
  have e : ∑ c, ((2 * rhoC ε c : ℝ) : ℂ) • E c c x =
      ∑ i : Pos n, if cpt ε i then E i.1.1 i.1.1 x - E i.1.2 i.1.2 x else 0 := by
    have : ∀ c, 2 * rhoC ε c = ∑ i ∈ om ε, al i c := fun c => by rw [← wt_sum, wt_om]; rfl
    simp only [this, Complex.ofReal_sum, Finset.sum_smul]
    rw [Finset.sum_comm, ← Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [al, sub_smul, apply_ite ((↑) : ℝ → ℂ), ite_smul]
  rw [e, CasK, sum_pos]
  simp only [if_true, LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply]
  rw [add_sub_sub_cancel, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : cpt ε i
  · have := LinearMap.congr_fun (hE i.1.1 i.1.2 i.1.2 i.1.1 hi (Eq.symm hi)) x
    simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply] at this
    rw [if_pos hi, if_pos hi, if_pos hi, if_pos (Eq.symm hi), ← this, map_smul, two_smul]
    simp only [Module.End.mul_apply]
    abel
  · rw [if_neg hi, if_neg hi, if_neg hi, if_neg fun h => hi h.symm]
    simp
end CompanionTheory.D.LK
