-- Prove2me | solution 1 for CompanionTheory.D.gk.Poul.exists_riesz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:36:13.17744+00:00
-- url     : https://prove2.me/submissions/301f4436-4f85-4ec0-9663-63f6df278ae5

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.Poul
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Mat n)} {hG : IsMatGroup G}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat n → (H →L[ℂ] H)}
variable {ι : Type} [Fintype ι] {W : ι → List (Mat n)} {C : ℝ} {l : H → ℂ}
namespace CompanionTheory.D.gk.Poul
theorem _root_.solution (ha : ∀ x y, IsSm G σ x → IsSm G σ y → l (x + y) = l x + l y)
    (hs : ∀ (c : ℂ) x, IsSm G σ x → l (c • x) = c * l x) {D : ℝ} (hD : ∀ x, IsSm G σ x → ‖l x‖ ≤ D * ‖x‖) :
    ∃ z : H, ∀ x, IsSm G σ x → l x = ⟪z, x⟫_ℂ := by
  let S : Submodule ℂ H :=
    { carrier := {x | IsSm G σ x}
      add_mem' := fun ha hb => ha.add hb
      zero_mem' := IsSm.zero
      smul_mem' := fun c _ hx => hx.smul c }
  let L : S →ₗ[ℂ] ℂ :=
    { toFun := fun x => l x
      map_add' := fun x y => ha _ _ x.2 y.2
      map_smul' := fun c x => hs c _ x.2 }
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq S (L.mkContinuous D fun x => hD _ x.2)
  refine ⟨(InnerProductSpace.toDual ℂ H).symm g, fun x hx => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  exact (hg ⟨x, hx⟩).symm
end CompanionTheory.D.gk.Poul
