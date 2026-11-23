-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenyPAux.eventually_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:27:56.788299+00:00
-- url     : https://prove2.me/submissions/a7d56b42-d37b-4a37-aed0-ad29160fa80a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Elliptic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenyP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.IsogenyPAux
namespace Formalism.L2.Th1.F.IsogenyPAux
theorem _root_.solution (L : PeriodPair) (α z : ℂ) (hα : α ≠ 0) :
    ∀ᶠ w in 𝓝[≠] z, α * w ∉ L.lattice := by
  have h1 : ∀ᶠ w in 𝓝 z, α * w ∈ ((L.lattice : Set ℂ) \ {α * z})ᶜ :=
    ((continuous_const.mul continuous_id).tendsto z).eventually
      (L.compl_lattice_sdiff_singleton_mem_nhds (α * z))
  filter_upwards [h1.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hne hmem
  refine hw ⟨hmem, ?_⟩
  simpa [hα] using hne
end Formalism.L2.Th1.F.IsogenyPAux
