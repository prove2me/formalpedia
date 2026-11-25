-- Prove2me | solution 1 for CompanionTheory.D.LK.cok_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:55:59.395049+00:00
-- url     : https://prove2.me/submissions/251306d6-ced1-4c5d-a16c-bb0ee2aa3910

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialCommutesWeightOperator
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KTypeCount
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_DoubleSumReduceSecond
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_FilterAll
import Theorems.Thm_CompanionTheory_D_LK_casK_comm
import Theorems.Thm_CompanionTheory_D_LK_casK_inN
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_LK_evd_eig
import Theorems.Thm_UpperTheory_Reformulated_B_P6_r26a_PositivityTheory_D_LK_casK_comm
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
theorem _root_.solution (hG : GenCO) : COK := by
  intro n ε V _ _ E hE B j τ x hx hτ hb
  let a : FreeAlgebra ℂ (Fin n × Fin n) :=
    ∑ c, ∑ d, if ε c = ε d then FreeAlgebra.ι ℂ (c, d) * FreeAlgebra.ι ℂ (d, c) else 0
  let b : FreeAlgebra ℂ (Fin n) :=
    ∑ c, FreeAlgebra.ι ℂ c * FreeAlgebra.ι ℂ c - ∑ c, ((2 * rhoC ε c : ℝ) : ℂ) • FreeAlgebra.ι ℂ c
  have ha : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
      evK ε E a = CasK ε E := fun V _ _ E => by
    simp only [a, CasK, map_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    split_ifs with h
    · simp [evK, h]
    · exact map_zero _
  obtain ⟨w, hw, e⟩ := hG n ε ε a b (fun _ _ h => h) (fun V _ _ E hE => by
    rw [ha]
    refine ⟨fun i hi => casK_comm hE hi, fun x => ?_⟩
    simpa [b, evd, LinearMap.sum_apply] using casK_inN hE x) V E hE B j x hx (fun _ _ _ _ h => h) hb
  refine ⟨w, hw, ?_⟩
  rw [← e, ha, evd_eig _ _ _ hτ]
  congr 2
  simp only [b, map_sub, map_sum, map_mul, map_smul, FreeAlgebra.lift_ι_apply, smul_eq_mul, nsq, PI.UpqRep.dot,
    Pi.sub_apply, ← Finset.sum_sub_distrib]
  push_cast
  exact Finset.sum_congr rfl fun c _ => by ring
end CompanionTheory.D.LK
