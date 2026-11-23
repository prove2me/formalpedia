-- Prove2me | solution 1 for DedekindZeta.MellinPrinciple.reducedMellin_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:29:11.360629+00:00
-- url     : https://prove2.me/submissions/eb3e2f60-f371-4ac3-866f-04f107b34d10

import Mathlib
import Definitions.Def_DedekindZeta_MellinPrinciple
import Theorems.Thm_DedekindZeta_MellinPrinciple_reducedMellin_convergent

set_option autoImplicit true
open MeasureTheory Set Filter Asymptotics Topology Complex
open DedekindZeta DedekindZeta.MellinPrinciple
variable {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}
namespace DedekindZeta.MellinPrinciple
theorem _root_.solution (h : IsMellinPair f g a₀ b₀ C k c α) {s : ℂ}
    (hs : k < s.re) :
    reducedMellin f a₀ s
      = (∫ y in Ioc (0 : ℝ) 1, (f y - a₀) * (y : ℂ) ^ (s - 1))
        + (∫ y in Ioi (1 : ℝ), (f y - a₀) * (y : ℂ) ^ (s - 1)) := by
  -- Rewrite Mathlib's `smul` integrand into the `mul` form used in the goal.
  have key : ∀ y : ℝ,
      (y : ℂ) ^ (s - 1) • (f y - a₀) = (f y - a₀) * (y : ℂ) ^ (s - 1) := by
    intro y; rw [smul_eq_mul, mul_comm]
  -- Integrability on `Ioi 0` from `MellinConvergent`.
  have hconv : IntegrableOn
      (fun y : ℝ => (f y - a₀) * (y : ℂ) ^ (s - 1)) (Ioi 0) := by
    have hc := reducedMellin_convergent h hs
    unfold MellinConvergent at hc
    simpa only [key] using hc
  have hsub₁ : Ioc (0 : ℝ) 1 ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have hsub₂ : Ioi (1 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi zero_le_one
  unfold reducedMellin mellin
  simp_rw [key]
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hconv.mono_set hsub₁) (hconv.mono_set hsub₂)]
end DedekindZeta.MellinPrinciple
