-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.DualLatticeEmbeddings.exists_int_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:32.87089+00:00
-- url     : https://prove2.me/submissions/5a03fbaa-6fe4-4044-9ec2-e0f9dd4e9385

import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_SumUliftFinsetFinTwoExpand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Rec Formalism.L2.Geo.Rec.DualLatticeEmbeddings
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings
theorem _root_.solution (X : Submodule (𝓞 K) (Fin n → K))
    (hX : Submodule.span K (X : Set (Fin n → K)) = ⊤) (v : Fin n → K) :
    ∃ N : ℤ, N ≠ 0 ∧ N • v ∈ X := by
  classical
  have hv : v ∈ Submodule.span K (X : Set (Fin n → K)) := by rw [hX]; trivial
  obtain ⟨m, f, g, hg⟩ := (Submodule.mem_span_set' (R := K)).1 hv
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [← hg, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ (y • f i) := hint _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  let r : 𝓞 K := ⟨y • f i, hi⟩
  have hr : y • (f i • (g i : Fin n → K)) = r • (g i : Fin n → K) := by
    rw [← algebraMap_smul K r, ← smul_assoc]
    rfl
  rw [hr]
  exact X.smul_mem r (g i).2
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
