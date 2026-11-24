-- Prove2me | solution 1 for Formalism.L2.Pj.nrmC_valC_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:35:08.13349+00:00
-- url     : https://prove2.me/submissions/8874a8ab-f06f-402b-839f-b47c226b289a

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompHt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PTNonempty
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
import Theorems.Thm_Formalism_L2_Pj_exZ_wtZ

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
theorem _root_.solution (hcx : ValAtCx h yP) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hS : f ∈ sec Xo c a n) (hB : SupBdd Xo c fn a n f) (Z : Comp Xo c) (P : Om Z →+* ℂ) :
    nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P ≤ supR Xo c fn (sgOf P) a n f := by
  have hb := hB (sgOf P)
  unfold BddAt at hb
  have hle := le_ciSup hb (yP Z P)
  have hc : (valC h a n f Z).coeff (wtZ a n) = evC h Z f := by
    unfold valC
    simp
  have heq : nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P =
      ptNorm (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (sgOf P) (fn (sgOf P)) (ex Dw a n) f (yP Z P) := by
    unfold nrmC ptNorm
    rw [hc, hcx Z P a n f hS]
    simp only [exZ_wtZ, zpow_neg, zpow_natCast, inv_pow] <;> rfl
  rw [heq]
  exact hle
end Formalism.L2.Pj
