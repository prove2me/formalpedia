-- Prove2me | solution 1 for Formalism.L2.Pj.gfp_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:04:23.441506+00:00
-- url     : https://prove2.me/submissions/49f109a4-f16e-4634-a66b-81573d9a4311

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfV
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfB
import Theorems.Thm_Formalism_L2_Pj_gfp_finrank
import Theorems.Thm_Formalism_L2_Pj_gfp_comb_iff
import Theorems.Thm_Formalism_L2_Pj_gfp_eig_iff
import Theorems.Thm_Formalism_L2_Pj_gfp_exists
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable {L : Type} [Field L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
variable [Algebra c.F L]
namespace Formalism.L2.Pj
theorem _root_.solution (hx0 : x ≫ Xo.s = sOf c L) (hx : IsUnivChart _ n xc) (τ : E →+* ℂ)
    (d : Fin (Dw.mult τ) → Fin n → L) (hd : LinearIndependent L d) (hdW : ∀ i, d i ∈ gfpEig (c := c) hx τ)
    (w : Sp (DualNumber L) ⟶ Xo.univ.t.G.left) (hw : IsTanAt x w) (he : IsEigAt c τ w) :
    ∃! a : Fin (Dw.mult τ) → L, IsCombAt x (fun i => gfpVec x xc (d i)) a w := by
  obtain ⟨cc, rfl⟩ := gfp_exists hx w hw
  have hcc : cc ∈ gfpEig (c := c) hx τ := (gfp_eig_iff hx τ cc).1 he
  have hle : Submodule.span L (Set.range d) ≤ gfpEig (c := c) hx τ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hdW i
  have hfr : Module.finrank L (Submodule.span L (Set.range d)) =
      Module.finrank L (gfpEig (c := c) hx τ) := by
    rw [finrank_span_eq_card hd, Fintype.card_fin, gfp_finrank hx0 hx τ]
  have heq : Submodule.span L (Set.range d) = gfpEig (c := c) hx τ :=
    Submodule.eq_of_le_of_finrank_eq hle hfr
  have hspan : cc ∈ Submodule.span L (Set.range d) := heq ▸ hcc
  obtain ⟨a, ha⟩ : ∃ a : Fin (Dw.mult τ) → L, ∑ i, a i • d i = cc := by
    first
    | exact (Submodule.mem_span_range_iff_exists_fun L).1 hspan
    | exact Submodule.mem_span_range_iff_exists_fun.1 hspan
  refine ⟨a, (gfp_comb_iff hx d a cc).2 ha.symm, ?_⟩
  intro a' ha'
  have h2 : cc = ∑ j, a' j • d j := (gfp_comb_iff hx d a' cc).1 ha'
  have h3 : ∑ j, a' j • d j = ∑ j, a j • d j := h2.symm.trans ha.symm
  funext i
  have h4 := Fintype.linearIndependent_iff.1 hd (a' - a) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h3, sub_self]) i
  simpa [sub_eq_zero] using h4
end Formalism.L2.Pj
