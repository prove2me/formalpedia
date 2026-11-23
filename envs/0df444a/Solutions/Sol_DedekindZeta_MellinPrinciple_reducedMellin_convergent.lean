-- Prove2me | solution 1 for DedekindZeta.MellinPrinciple.reducedMellin_convergent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:27:06.739803+00:00
-- url     : https://prove2.me/submissions/ea458b47-1723-44f2-9826-9fefdab614e4

import Mathlib
import Definitions.Def_DedekindZeta_MellinPrinciple
import Theorems.Thm_DedekindZeta_MellinPrinciple_reducedMellin_isBigO_atTop
import Theorems.Thm_DedekindZeta_MellinPrinciple_reducedMellin_isBigO_zero

set_option autoImplicit true
open MeasureTheory Set Filter Asymptotics Topology Complex
open DedekindZeta DedekindZeta.MellinPrinciple
variable {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}
namespace DedekindZeta.MellinPrinciple
theorem _root_.solution (h : IsMellinPair f g a₀ b₀ C k c α) {s : ℂ}
    (hs : k < s.re) : MellinConvergent (fun y : ℝ => f y - a₀) s :=
  mellinConvergent_of_isBigO_rpow
    ((h.hf_cont.sub continuousOn_const).locallyIntegrableOn measurableSet_Ioi)
    (reducedMellin_isBigO_atTop h (s.re + 1)) (by linarith)
    (reducedMellin_isBigO_zero h) hs
end DedekindZeta.MellinPrinciple
