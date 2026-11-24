-- Prove2me | solution 1 for Formalism.L2.Pj.log_supN_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:44:11.45397+00:00
-- url     : https://prove2.me/submissions/bd2fe0c6-ab31-4b2c-a1f8-ef9b34a9b44c

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompHt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PTNonempty
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
import Theorems.Thm_Formalism_L2_Pj_nrmC_valC_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]
variable {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
  {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}
namespace Formalism.L2.Pj
theorem _root_.solution (hfn : FnNe Xo c fn) (hPT : PTNe Xo c) (hcx : ValAtCx h yP) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul Xo c} (hS : f ∈ sec Xo c a n) (hB : SupBdd Xo c fn a n f) (hN : NZSome h f) (σ : c.F →+* ℂ) :
    Real.log (⨆ p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ), nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2) ≤
      Real.log (supR Xo c fn σ a n f) := by
  have hbd : ∀ p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ),
      nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2 ≤ supR Xo c fn σ a n f := by
    rintro ⟨Z, P, hP⟩
    have hσ : sgOf P = σ := hP
    have key := nrmC_valC_le (h := h) (yP := yP) hcx hS hB Z P
    rw [hσ] at key
    exact key
  obtain ⟨Z0, hZ0⟩ := hN
  obtain ⟨P0, hP0⟩ := hPT Z0 σ
  have hpos : 0 < nrmC fn (yP Z0) (wtZ a n) (valC h a n f Z0) P0 := by
    have hc : (valC h a n f Z0).coeff (wtZ a n) = evC h Z0 f := by
      unfold valC
      simp
    unfold nrmC
    rw [hc]
    apply mul_pos
    · exact norm_pos_iff.mpr ((map_ne_zero P0).mpr hZ0)
    · apply Finset.prod_pos
      intro i _
      exact zpow_pos (abs_pos.mpr (hfn _ _ i)) _
  have hne : Nonempty (Σ Z : Comp Xo c, PT (Ω := Om Z) σ) := ⟨⟨Z0, P0, hP0⟩⟩
  have hB' : BddAbove (Set.range fun p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ) =>
      nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2) := ⟨_, Set.forall_mem_range.mpr hbd⟩
  apply Real.log_le_log
  · exact lt_of_lt_of_le hpos (le_ciSup hB' ⟨Z0, P0, hP0⟩)
  · exact ciSup_le hbd
end Formalism.L2.Pj
