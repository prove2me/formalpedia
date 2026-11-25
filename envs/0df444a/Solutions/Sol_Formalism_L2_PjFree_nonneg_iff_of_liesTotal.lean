-- Prove2me | solution 1 for Formalism.L2.PjFree.nonneg_iff_of_liesTotal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:58:30.747806+00:00
-- url     : https://prove2.me/submissions/6ffded58-0ae7-43e7-95e2-8ec54d710b19

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RulInst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree

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
open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
  (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop)
variable {Xo c cls}
variable (Xo c cls)
variable {Xo c cls}
namespace Formalism.L2.PjFree
theorem _root_.solution {PY : HeightOneSpectrum (𝓞 c.F) → Type}
    {lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop}
    (h : LiesTotal Xo c cls PY lies) (f : Rul Xo c) :
    (∀ la, ∀ v ∈ valSet Xo c cls la, 0 ≤ v f) ↔
      ∀ la (y : PtV Xo c cls (PY la) (lies la) la), 0 ≤ vAtV y f := by
  constructor
  · intro H la y
    obtain ⟨⟨g, hg⟩, T, io, e, hO, y0, hcls, eta, hl, heq⟩ := y
    have hg1 := congrArg Prod.fst heq
    dsimp only at hg1
    subst hg1
    have hv := H la (vAtV (⟨profI Xo c Unit e y0 (), T, io, e, hO, y0, hcls, (), trivial, rfl⟩ :
      PtV Xo c cls Unit (fun _ _ _ _ => True) la)) ⟨_, rfl⟩
    exact hv
  · rintro H la v ⟨y, rfl⟩
    obtain ⟨⟨g, hg⟩, T, io, e, hO, y0, hcls, eta, hl, heq⟩ := y
    have hg1 := congrArg Prod.fst heq
    dsimp only at hg1
    subst hg1
    obtain ⟨η, hη⟩ := h la T io e hO y0 hcls
    exact H la ⟨profI Xo c (PY la) e y0 η, T, io, e, hO, y0, hcls, η, hη, rfl⟩
end Formalism.L2.PjFree
