-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.thetaSummable_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:11.173394+00:00
-- url     : https://prove2.me/submissions/b49648f5-82f1-4670-a5e9-adc549de48c6

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] {g : ℤ → ℝ} (hg0 : ∀ n, 0 ≤ g n)
    (hg : Summable g) : Summable (fun c : ι → ℤ => ∏ i, g (c i)) := by
  refine summable_of_sum_le (c := ∏ i : ι, ∑' n, g n)
    (fun c => Finset.prod_nonneg (fun i _ => hg0 (c i))) (fun u => ?_)
  let S : ι → Finset ℤ := fun i => u.image (fun c => c i)
  have hsub : u ⊆ Fintype.piFinset S := by
    intro c hc
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image_of_mem _ hc
  calc ∑ c ∈ u, ∏ i, g (c i)
      ≤ ∑ c ∈ Fintype.piFinset S, ∏ i, g (c i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun c _ _ => Finset.prod_nonneg (fun i _ => hg0 (c i)))
    _ = ∏ i, ∑ n ∈ S i, g n := (Finset.prod_univ_sum S (fun _ n => g n)).symm
    _ ≤ ∏ i : ι, ∑' n, g n :=
        Finset.prod_le_prod (fun i _ => Finset.sum_nonneg (fun n _ => hg0 n))
          (fun i _ => hg.sum_le_tsum _ (fun n _ => hg0 n))
end Formalism.HermitianLatticesTheory
