-- Prove2me | solution 1 for Formalism.L2.Pj.existsUnique_thRule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:09:39.932465+00:00
-- url     : https://prove2.me/submissions/2e0133e1-1889-4bbc-be41-b0cf082a0f78

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsThRule
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
namespace Formalism.L2.Pj
theorem _root_.solution (nab : NabV Xo c) (h : ThValTot Xo c nab) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (x : Fin n → Dw.La) {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) :
    ∃! f : Rul Xo c, IsThRule Xo c nab x P f := by
  refine ⟨fun p y => (h p.R y a n x P hP).exists.choose,
    fun p y => (h p.R y a n x P hP).exists.choose_spec, ?_⟩
  intro g hg
  funext p y
  exact (h p.R y a n x P hP).unique (hg p y) (h p.R y a n x P hP).exists.choose_spec
end Formalism.L2.Pj
