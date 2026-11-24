-- Prove2me | solution 1 for Formalism.L2.PjFree.supE_cusp_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:26:20.753319+00:00
-- url     : https://prove2.me/submissions/57146b8c-4538-4cb9-8622-dd0adf5af5fb

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RulInst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Theorems.Thm_Formalism_L2_PjFree_supE_ne_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.PjFree
open Formalism.L2.Pj
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
variable {Xo c U}
namespace Formalism.L2.PjFree
theorem _root_.solution {a n} {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {f : Rul Xo c} (hf : f ∈ cusp Xo c U a n) :
    supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) ≠ ⊤ := by
  unfold cusp at hf
  have h1 := (Submodule.mem_inf.mp hf).2
  have h2 := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp h1 σ) hσ
  exact supE_ne_top _ _ (Submodule.mem_comap.mp h2)
end Formalism.L2.PjFree
