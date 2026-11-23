-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.span_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:20.896962+00:00
-- url     : https://prove2.me/submissions/83197e94-b344-486f-9280-c6aabe925ce0

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LLcv
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData
open scoped Matrix
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution {j : ℕ} (e : Fin j → V) (g : Matrix (Fin j) (Fin j) K)
    (hg : IsUnit g.det) :
    Submodule.span K (Set.range fun a => ∑ c, g c a • e c) = Submodule.span K (Set.range e) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact Submodule.sum_mem _ fun c _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self c))
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    have h : e k = ∑ a, g⁻¹ a k • ∑ c, g c a • e c := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have : ∀ c, ∑ a, (g⁻¹ a k * g c a) • e c = ((g * g⁻¹) c k) • e c := by
        intro c
        rw [← Finset.sum_smul, Matrix.mul_apply]
        congr 1
        exact Finset.sum_congr rfl fun a _ => mul_comm _ _
      simp only [this, Matrix.mul_nonsing_inv g hg, Matrix.one_apply]
      simp
    rw [h]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a))
end Formalism.LFunctionChainParameters.LLcv
