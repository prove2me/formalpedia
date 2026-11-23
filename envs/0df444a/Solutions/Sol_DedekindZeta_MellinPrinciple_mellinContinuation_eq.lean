-- Prove2me | solution 1 for DedekindZeta.MellinPrinciple.mellinContinuation_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:31:59.996407+00:00
-- url     : https://prove2.me/submissions/b483e0df-f190-4c3a-a907-b1cde7406c3c

import Mathlib
import Definitions.Def_DedekindZeta_MellinPrinciple
import Theorems.Thm_DedekindZeta_MellinPrinciple_reducedMellin_split
import Theorems.Thm_DedekindZeta_MellinPrinciple_mellinTail_integrable_left
import Theorems.Thm_DedekindZeta_MellinPrinciple_mellinTail_integrable_right
import Theorems.Thm_DedekindZeta_MellinPrinciple_reducedMellin_lower

set_option autoImplicit true
open MeasureTheory Set Filter Asymptotics Topology Complex
open DedekindZeta DedekindZeta.MellinPrinciple
variable {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}
namespace DedekindZeta.MellinPrinciple
theorem _root_.solution (h : IsMellinPair f g a₀ b₀ C k c α) {s : ℂ}
    (hs : k < s.re) :
    mellinContinuation f g a₀ b₀ C k s = reducedMellin f a₀ s := by
  rw [reducedMellin_split h hs, reducedMellin_lower h hs]
  unfold mellinContinuation mellinTail
  rw [integral_add (mellinTail_integrable_left h) (mellinTail_integrable_right h)]
  ring
end DedekindZeta.MellinPrinciple
