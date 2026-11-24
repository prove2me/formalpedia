-- Prove2me | solution 1 for Formalism.GM.TM.pointM_of_partner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:08.984451+00:00
-- url     : https://prove2.me/submissions/42c976a2-60db-4317-b930-66577d9a583e

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Theorems.Thm_Formalism_GM_TM_yZ_fg
import Theorems.Thm_Formalism_GM_TM_fockBil_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.GM.TM
theorem _root_.solution (hBad : BadCrit) (hPart : PartnerM) : PointM := by
  obtain ⟨C₁, hC₁, hP⟩ := hPart
  refine ⟨C₁, hC₁, ?_⟩
  intro C hC p _ N r _ _ LL T a E κ n ρ h2p hr hρ hadm hE hS hdeg hz hκ hHP hHW hL4 nb f U V dg fw h1 h2 h3
  obtain ⟨L₁, hle, hsat, hpart, hrank⟩ :=
    hP C hC p N r LL T a E κ n ρ h2p hr hρ hadm hE hS hdeg hz hκ hHP hHW hL4 nb f U V dg fw h1 h2 h3
  haveI hfin : Module.Finite ℤ_[p] (YZ p (r := r) (LL.setTies T n) T.J T.thr) :=
    Module.Finite.iff_fg.mpr (yZ_fg _ _ _)
  have hb := hBad p (MvPolynomial (Fin N × Fin r) ℚ_[p]) (fockBil (LL.setTies T n) (T.phis p (LL.setTies T n)))
    (YZ p (r := r) (LL.setTies T n) T.J T.thr) L₁ ⌊(T.t : ℝ) * (E + C * κ) + C * κ⌋ hfin hle hsat
    (fun u hu hprim => by
      obtain ⟨u', hu', h⟩ := hpart u hu hprim
      exact ⟨u', hu', by rw [fockBil_apply]; exact h⟩)
  exact (Nat.cast_le.mpr hb).trans hrank
end Formalism.GM.TM
