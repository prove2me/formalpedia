-- Prove2me | solution 1 for CompanionTheory.D.LK.cyc_stab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:15:17.793813+00:00
-- url     : https://prove2.me/submissions/7e7d69ac-26c5-4e1c-b2b1-53ef7062d1b6

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Theorems.Thm_CompanionTheory_D_LK_mem_cyc
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
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight CasK Cas)
open PI.UpqRep (lowK vNormSq IsHCParam IsURepOn IsIrredOn UJset Kset IsKFin IsKTypeOf IsDS rhoC)
open CompanionTheory.D.DSIC (KRel KUnit KStab LowSpan HWMap)
variable {n : ℕ}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace CompanionTheory.D.LK
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ V} {v w : V} (c d : Fin n) (h : w ∈ Cyc E v) :
    E c d w ∈ Cyc E v := by
  obtain ⟨a, rfl⟩ := mem_cyc.1 h
  refine mem_cyc.2 ⟨FreeAlgebra.ι ℂ (c, d) * a, ?_⟩
  rw [map_mul, Module.End.mul_apply]
  simp only [CompanionTheory.D.LK.ev, FreeAlgebra.lift_ι_apply]
end CompanionTheory.D.LK
