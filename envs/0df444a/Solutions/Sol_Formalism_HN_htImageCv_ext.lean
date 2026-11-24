-- Prove2me | solution 1 for Formalism.HN.htImageCv_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:27.187095+00:00
-- url     : https://prove2.me/submissions/694beb07-5727-4055-bbfc-4302f4395817

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage

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
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution {P ι : Type*} [Fintype P] [Fintype ι] {y z : EuclideanSpace ℝ (P × ι × Fin 2)}
    (h : ∀ v, htImageCv y v = htImageCv z v) : y = z := by
  ext ⟨v, i, j⟩
  have h1 := congrArg Complex.re (congrFun (h v) i)
  have h2 := congrArg Complex.im (congrFun (h v) i)
  fin_cases j
  · exact h1
  · exact h2
end Formalism.HN
