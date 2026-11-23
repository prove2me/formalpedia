-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx6.blk_psd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:00.684807+00:00
-- url     : https://prove2.me/submissions/52d9ce6e-4f19-4773-9b2d-4b87ba21da53

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionGivesUniformBoundsForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx6_psd_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx6
namespace Formalism.FourierDecayAlt.P.Jx6
theorem _root_.solution {E : Type} [Field E] {Y : Finset (TB.Pt E)} {S : Finset E} {s : ℕ}
    {κ : TB.Pt E → TB.Pt E → ℂ} (hκ : TB.PSDOn (TB.pts Y s S) κ) {t : E} (ht : t ∈ S) :
    TB.PSDOn Y (TB.blk κ s t t) := by
  classical
  have hm : ∀ x ∈ Y, TB.join x s t ∈ TB.pts Y s S := by
    intro x hx
    unfold TB.pts
    exact Finset.mem_image.2 ⟨(x, t), Finset.mem_product.2 ⟨hx, ht⟩, rfl⟩
  exact psd_pull (fun x : Y => ⟨TB.join x.1 s t, hm x.1 x.2⟩) (fun _ _ => rfl) hκ
end Formalism.FourierDecayAlt.P.Jx6
