-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.cro_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:22:09.422917+00:00
-- url     : https://prove2.me/submissions/3b75cac6-6e23-48e2-bf54-4a663d78fc89

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_ordGe_add
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


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
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}
variable (Op Op' : PS k n d → PS k n d)
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (hsub : ∀ X Y, Op (X - Y) = Op X - Op Y)
    (hlow : ∀ t X, OrdGe (t + 1) X → OrdGe t (Op X)) (hlow' : ∀ t X, OrdGe (t + 1) X → OrdGe t (Op' X))
    (hdiff : ∀ t X, OrdGe (t + 1) X → OrdGe (t + 1) (Op X - Op' X)) (c : ℕ) :
    ∀ (s : ℕ) (X Y : PS k n d), OrdGe (c + s) X → OrdGe (c + s) Y → OrdGe (c + s + 1) (X - Y) →
      OrdGe s (Op^[c] X) ∧ OrdGe s (Op'^[c] Y) ∧ OrdGe (s + 1) (Op^[c] X - Op'^[c] Y) := by
  induction c with
  | zero =>
    intro s X Y hX hY hXY
    simp only [Function.iterate_zero_apply]
    exact ⟨by simpa using hX, by simpa using hY, by simpa using hXY⟩
  | succ c ih =>
    intro s X Y hX hY hXY
    have hX' : OrdGe (c + s + 1) X := by rwa [show c + s + 1 = c + 1 + s by omega]
    have hY' : OrdGe (c + s + 1) Y := by rwa [show c + s + 1 = c + 1 + s by omega]
    have hXY' : OrdGe (c + s + 1 + 1) (X - Y) := by rwa [show c + s + 1 + 1 = c + 1 + s + 1 by omega]
    have h1 : OrdGe (c + s) (Op X) := hlow _ _ hX'
    have h2 : OrdGe (c + s) (Op' Y) := hlow' _ _ hY'
    have h3 : OrdGe (c + s + 1) (Op X - Op' Y) := by
      have e : Op X - Op' Y = Op (X - Y) + (Op Y - Op' Y) := by
        rw [hsub]
        abel
      rw [e]
      exact cro_ordGe_add (hlow _ _ hXY') (hdiff _ _ hY')
    simp only [Function.iterate_succ_apply]
    exact ih s (Op X) (Op' Y) h1 h2 h3
end Formalism.L2.Pj.Crude
