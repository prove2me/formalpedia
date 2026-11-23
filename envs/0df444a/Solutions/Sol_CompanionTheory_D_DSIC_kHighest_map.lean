-- Prove2me | solution 1 for CompanionTheory.D.DSIC.kHighest_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:56.006638+00:00
-- url     : https://prove2.me/submissions/f83b9f72-61f0-46ac-af22-d547258a7ece

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CobApplyOfDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.DSIC
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight qdet qminor)
open PI.UpqRep (lowK vNormSq IsHCParam IsURepOn IsIrredOn UJset Kset IsKFin IsKTypeOf IsWtOn inG inK IsKStableOn)
variable {n : ℕ} {ε : Fin n → Bool}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace CompanionTheory.D.DSIC
theorem _root_.solution {F : Fin n → Fin n → Module.End ℂ V} {γ : Fin n → ℝ} {x : V} (h : KHighest ε F γ x)
    {T : Module.End ℂ V} (hT : ∀ c d, ε c = ε d → Commute (F c d) T) : KHighest ε F γ (T x) := by
  have e : ∀ c d, ε c = ε d → F c d (T x) = T (F c d x) := fun c d h =>
    congrArg (fun S : Module.End ℂ V => S x) (hT c d h).eq
  exact ⟨fun a => by rw [e a a rfl, h.1 a, map_smul], fun a b hab he => by rw [e a b he, h.2 a b hab he, map_zero]⟩
end CompanionTheory.D.DSIC
