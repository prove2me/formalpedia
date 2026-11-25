-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.ds_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:54:28.965158+00:00
-- url     : https://prove2.me/submissions/5968d3b0-85f4-4dfc-a1f8-fb98654a776a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_UniformCoefficientBounds_CoefBoundUniform
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ds_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ds_smul


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
theorem _root_.solution (h : RepOn G σ) {X : Mat n} (hX : ∀ t, ex X t ∈ G) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) {b : ι → H} (hb : ∀ i, IsSm G σ (b i)) :
    ds σ X (∑ i ∈ s, c i • b i) = ∑ i ∈ s, c i • ds σ X (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ds_smul h hX (IsSm.zero (G := G) (σ := σ)) 0
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ds_add h hX ((hb i).smul _)
      ((smSub G σ).sum_mem fun j _ => (hb j).smul _), ds_smul h hX (hb i), ih]
end CompanionTheory.D.Upq.Sm
