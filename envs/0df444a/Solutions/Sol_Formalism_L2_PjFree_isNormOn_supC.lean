-- Prove2me | solution 1 for Formalism.L2.PjFree.isNormOn_supC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:11:11.34153+00:00
-- url     : https://prove2.me/submissions/7582a825-b940-4009-9234-71ae7ec4286a

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RulInst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Theorems.Thm_Formalism_L2_PjFree_supE_add_le
import Theorems.Thm_Formalism_L2_PjFree_supE_smul
import Theorems.Thm_Formalism_L2_PjFree_lieFac_pos
import Theorems.Thm_Formalism_L2_PjFree_supE_cusp_ne_top
import Theorems.Thm_Formalism_L2_PjFree_supN_nonneg


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
theorem _root_.solution (x : ℝ) (h : SupDef Xo c U) {a n} (hd : Dom a n) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) :
    IsNormOn (cusp Xo c U a n) σ (supC Xo c U x σ a n) where
  nonneg f _ := mul_nonneg (lieFac_pos _ _ _).le (supN_nonneg _ _ _)
  defin f hf h0 := h a n hd σ hσ f hf ((mul_eq_zero.mp h0).resolve_left (lieFac_pos _ _ _).ne')
  smul y f _ := by
    unfold supC supN
    rw [map_smulₛₗ, supE_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
    ring
  add f hf g hg := by
    unfold supC supN
    rw [← mul_add, map_add, ← ENNReal.toReal_add (supE_cusp_ne_top hσ hf) (supE_cusp_ne_top hσ hg)]
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono ?_ (supE_add_le _ _ _ _)) (lieFac_pos _ _ _).le
    exact ENNReal.add_ne_top.mpr ⟨supE_cusp_ne_top hσ hf, supE_cusp_ne_top hσ hg⟩
end Formalism.L2.PjFree
