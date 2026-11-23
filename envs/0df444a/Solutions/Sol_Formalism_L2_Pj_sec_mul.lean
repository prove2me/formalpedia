-- Prove2me | solution 1 for Formalism.L2.Pj.sec_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:17.600149+00:00
-- url     : https://prove2.me/submissions/3d87e167-7faa-4035-b62e-5bdcd6a51788

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}
variable (Xo c)
variable {Xo c}
variable (Xo c)
namespace Formalism.L2.Pj
theorem _root_.solution (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) {f g : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (hg : g ∈ sec Xo c a' n') : f * g ∈ sec Xo c (a + a') (n + n') := by
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, ?_⟩
  · intro p q φ y z h
    change f q z * g q z = φ (f p y * g p y)
    rw [hf1 p q φ y z h, hg1 p q φ y z h, map_mul]
  · intro p t y y' h
    change f p y' * g p y' = _ * (f p y * g p y)
    rw [hf2 p t y y' h, hg2 p t y y' h]
    have he : ∀ i, ex Dw (a + a') (n + n') i = ex Dw a n i + ex Dw a' n' i := by
      intro i
      cases i <;> rfl
    try unfold wchar
    rw [show (∏ i, (t i : p.R) ^ ex Dw (a + a') (n + n') i) =
        (∏ i, (t i : p.R) ^ ex Dw a n i) * ∏ i, (t i : p.R) ^ ex Dw a' n' i by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [he, pow_add]]
    ring
end Formalism.L2.Pj
