-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.apply_ds_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:13:17.218806+00:00
-- url     : https://prove2.me/submissions/63b25b2e-9a8d-4207-9f79-6978583314c9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_UniformCoefficientBounds_CoefBoundUniform
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ex_conj
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_differentiableAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {G K : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
namespace CompanionTheory.D.Upq.Sm
theorem _root_.solution (hG : IsMatGroup G) (h : RepOn G σ) {k X : Mat n} (hk : k ∈ G)
    (hX : ∀ t, ex X t ∈ G) {v : H} (hv : IsSm G σ v) :
    (∀ t, ex (k * X * k⁻¹) t ∈ G) ∧ σ k (ds σ X v) = ds σ (k * X * k⁻¹) (σ k v) := by
  have hm : ∀ t, ex (k * X * k⁻¹) t ∈ G := fun t => by
    rw [ex_conj hG hk]
    exact h.mul_mem _ (h.mul_mem _ hk _ (hX t)) _ (hG.2.2.2 k hk).1
  refine ⟨hm, ?_⟩
  rw [apply_ds h hX hk (hv.differentiableAt h hX)]
  unfold ds
  congr 1
  ext1 t
  rw [← h.apply_mul (hm t) hk, ex_conj hG hk, Matrix.mul_assoc (k * ex X t),
    mul_eq_one_comm.1 (hG.2.2.2 k hk).2, Matrix.mul_one]
end CompanionTheory.D.Upq.Sm
