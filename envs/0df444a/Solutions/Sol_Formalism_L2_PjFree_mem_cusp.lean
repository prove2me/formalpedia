-- Prove2me | solution 1 for Formalism.L2.PjFree.mem_cusp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:54.1219+00:00
-- url     : https://prove2.me/submissions/2e43531b-9e7e-4b93-b12a-1e9f87293027

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
namespace Formalism.L2.PjFree
theorem _root_.solution (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    f ∈ cusp Xo c U a n ↔ f ∈ sec Xo c a n ∧ ∀ σ : c.F →+* ℂ, GoodEmb c σ → rdU (U σ) f ∈ holSub (U σ).X (laU (U σ) a n) := by
  simp only [cusp, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
end Formalism.L2.PjFree
