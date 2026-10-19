-- Prove2me | solution 1 for CohnElkies.stripHolomorphicPoissonKernel_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/5984b972-9815-4106-b9a4-b0c32be64e08

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripComplexPoissonKernel_re
import Theorems.Thm_CohnElkies_stripHolomorphicPoissonKernel_eq_scaled

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ σ : ℝ} (hℓ : 0 < ℓ)
    (hbelow : -1 < σ) (habove : σ < 1) (s y : ℝ) :
    (stripHolomorphicPoissonKernel ℓ
      ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y).re =
      stripPoissonKernel σ ((s - y) / ℓ) / ℓ := by
  rw [stripHolomorphicPoissonKernel_eq_scaled hℓ,
    Complex.div_ofReal_re,
    stripComplexPoissonKernel_re hbelow habove]
end CohnElkies
