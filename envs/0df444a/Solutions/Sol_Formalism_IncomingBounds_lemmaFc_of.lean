-- Prove2me | solution 1 for Formalism.IncomingBounds.lemmaFc_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:14.159345+00:00
-- url     : https://prove2.me/submissions/437435a7-8d47-41fe-a483-9270df78a8fb

import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.IncomingBounds
section Helpers
variable {l d : ℕ} [NeZero d]
private theorem sum_deficit_le_Fnum_of_isDual (hA : LemmaFa) (hl : 3 ≤ l) (hd : 2 ≤ d) (hev : Even d)
    {D sig : ZMod d → ℝ} (hD : 0 ≤ D) (hsig : IsDual l d sig) :
    ∑ s, D s * (gam l - sig s) ≤ Fnum l d D := by
  have h := (hA l d hl hd hev D hD).2
  exact h.2 ⟨sig, hsig, rfl⟩
private theorem exists_isDual_Fnum_eq_sum_deficit (hA : LemmaFa) (hl : 3 ≤ l) (hd : 2 ≤ d) (hev : Even d)
    {D : ZMod d → ℝ} (hD : 0 ≤ D) :
    ∃ sig, IsDual l d sig ∧ Fnum l d D = ∑ s, D s * (gam l - sig s) :=
  (hA l d hl hd hev D hD).2.1
private theorem sum_add_apply_mul (D E f : ZMod d → ℝ) :
    ∑ s, (D + E) s * f s = ∑ s, D s * f s + ∑ s, E s * f s := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Pi.add_apply, add_mul]
end Helpers
end Formalism.IncomingBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution (hF : FlowAttained) (hA : LemmaFa) : LemmaFc := by
  intro l d _ hl hd hev D E sig hD hE hopt
  have hDE : 0 ≤ D + E := add_nonneg hD hE
  obtain ⟨hsig, hdef⟩ := hopt
  constructor
  · have h1 := sum_deficit_le_Fnum_of_isDual hA hl hd hev hDE hsig
    rw [sum_add_apply_mul, ← hdef] at h1
    have h2 : -(∑ s, E s * max (sig s - gam l) 0) ≤ ∑ s, E s * (gam l - sig s) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun s _ => ?_
      have hEs : 0 ≤ E s := hE s
      have hm := le_max_left (sig s - gam l) 0
      nlinarith
    linarith
  · obtain ⟨sg, hsg, e⟩ := exists_isDual_Fnum_eq_sum_deficit hA hl hd hev hDE
    have h3 := sum_deficit_le_Fnum_of_isDual hA hl hd hev hD hsg
    have h4 : ∑ s, E s * (gam l - sg s) ≤ gam l * ∑ s, E s := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      have hEs : 0 ≤ E s := hE s
      have hs0 : 0 ≤ sg s := (hsg.1 s).1
      nlinarith
    rw [e, sum_add_apply_mul]
    linarith
end Formalism.IncomingBounds
