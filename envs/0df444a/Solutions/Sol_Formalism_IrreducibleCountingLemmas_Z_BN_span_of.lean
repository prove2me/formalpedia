-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.span_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:57.72728+00:00
-- url     : https://prove2.me/submissions/15776bcc-9e1e-42c5-bd77-4608a44848b6

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN
open TensorProduct
variable {k G V W : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
namespace Formalism.IrreducibleCountingLemmas.Z.BN
theorem _root_.solution (K : Type) [Field K] :
    Submodule.span K (Set.range (MonoidAlgebra.of K G)) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  exact Submodule.span_mono (Set.image_subset_range _ _) (MonoidAlgebra.mem_span_support_coeff f)
end Formalism.IrreducibleCountingLemmas.Z.BN
