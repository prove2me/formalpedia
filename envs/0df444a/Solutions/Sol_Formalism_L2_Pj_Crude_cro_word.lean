-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.cro_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:33:46.897926+00:00
-- url     : https://prove2.me/submissions/ad75a44b-3247-4b6d-ba2d-42879fee4b7a

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_iter

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
namespace Formalism.L2.Pj.Crude
theorem _root_.solution {ι : Type} (Op Op' : ι → PS k n d → PS k n d) (m : ι →₀ ℕ)
    (hsub : ∀ l X Y, Op l (X - Y) = Op l X - Op l Y)
    (hlow : ∀ l t X, OrdGe (t + 1) X → OrdGe t (Op l X)) (hlow' : ∀ l t X, OrdGe (t + 1) X → OrdGe t (Op' l X))
    (hdiff : ∀ l t X, OrdGe (t + 1) X → OrdGe (t + 1) (Op l X - Op' l X)) (L : List ι) :
    ∀ (s : ℕ) (X Y : PS k n d), OrdGe ((L.map m).sum + s) X → OrdGe ((L.map m).sum + s) Y →
      OrdGe ((L.map m).sum + s + 1) (X - Y) →
      OrdGe s (L.foldr (fun l g => (Op l)^[m l] g) X) ∧ OrdGe s (L.foldr (fun l g => (Op' l)^[m l] g) Y) ∧
      OrdGe (s + 1) (L.foldr (fun l g => (Op l)^[m l] g) X - L.foldr (fun l g => (Op' l)^[m l] g) Y) := by
  induction L with
  | nil =>
    intro s X Y hX hY hXY
    simp only [List.map_nil, List.sum_nil, List.foldr_nil, zero_add] at hX hY hXY ⊢
    exact ⟨hX, hY, hXY⟩
  | cons l L ih =>
    intro s X Y hX hY hXY
    rw [List.map_cons, List.sum_cons] at hX hY hXY
    have hX' : OrdGe ((L.map m).sum + (m l + s)) X := by
      rwa [show (L.map m).sum + (m l + s) = m l + (L.map m).sum + s by omega]
    have hY' : OrdGe ((L.map m).sum + (m l + s)) Y := by
      rwa [show (L.map m).sum + (m l + s) = m l + (L.map m).sum + s by omega]
    have hXY' : OrdGe ((L.map m).sum + (m l + s) + 1) (X - Y) := by
      rwa [show (L.map m).sum + (m l + s) + 1 = m l + (L.map m).sum + s + 1 by omega]
    obtain ⟨h1, h2, h3⟩ := ih (m l + s) X Y hX' hY' hXY'
    simp only [List.foldr_cons]
    exact cro_iter (Op l) (Op' l) (hsub l) (hlow l) (hlow' l) (hdiff l) (m l) s _ _ h1 h2 h3
end Formalism.L2.Pj.Crude
