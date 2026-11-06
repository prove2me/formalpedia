-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_pair_moment_from_disjoint_union_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:15:32.229194+00:00
-- url     : https://prove2.me/submissions/61a2507d-0545-46b8-867e-c33678664519

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- The physical count's disjoint-union second moment isolates the
cross-band product moment without an independent-copy process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (A B : Ω → ℝ) (r s : ℝ)
    (hA2 : Integrable (fun ω => (A ω) ^ 2) P)
    (hB2 : Integrable (fun ω => (B ω) ^ 2) P)
    (hAB : Integrable (fun ω => A ω * B ω) P)
    (hAmean : (∫ ω, (A ω) ^ 2 ∂P) = r ^ 2 + r)
    (hBmean : (∫ ω, (B ω) ^ 2 ∂P) = s ^ 2 + s)
    (hUnion : (∫ ω, (A ω + B ω) ^ 2 ∂P) =
      (r + s) ^ 2 + (r + s)) :
    (∫ ω, A ω * B ω ∂P) = r * s := by
  have h2AB : Integrable (fun ω => 2 * (A ω * B ω)) P :=
    hAB.const_mul 2
  have hExpansion :
      (∫ ω, (A ω + B ω) ^ 2 ∂P) =
      (∫ ω, (A ω) ^ 2 ∂P) +
        (∫ ω, (B ω) ^ 2 ∂P) +
        2 * (∫ ω, A ω * B ω ∂P) := by
    calc
      (∫ ω, (A ω + B ω) ^ 2 ∂P) =
          ∫ ω, (A ω) ^ 2 + (B ω) ^ 2 +
            2 * (A ω * B ω) ∂P := by
        congr 1
        funext ω
        ring
      _ = (∫ ω, (A ω) ^ 2 ∂P) +
          (∫ ω, (B ω) ^ 2 ∂P) +
            2 * (∫ ω, A ω * B ω ∂P) := by
        have hOuter :
            (∫ ω, (A ω) ^ 2 + (B ω) ^ 2 +
              2 * (A ω * B ω) ∂P) =
              (∫ ω, (A ω) ^ 2 + (B ω) ^ 2 ∂P) +
                (∫ ω, 2 * (A ω * B ω) ∂P) := by
          simpa only [Pi.add_apply] using
            (integral_add (hA2.add hB2) h2AB)
        have hInner :
            (∫ ω, (A ω) ^ 2 + (B ω) ^ 2 ∂P) =
              (∫ ω, (A ω) ^ 2 ∂P) +
                (∫ ω, (B ω) ^ 2 ∂P) := by
          simpa only [Pi.add_apply] using (integral_add hA2 hB2)
        calc
          _ = (∫ ω, (A ω) ^ 2 + (B ω) ^ 2 ∂P) +
                (∫ ω, 2 * (A ω * B ω) ∂P) := hOuter
          _ = (∫ ω, (A ω) ^ 2 ∂P) +
                (∫ ω, (B ω) ^ 2 ∂P) +
                  2 * (∫ ω, A ω * B ω ∂P) := by
            rw [hInner, integral_const_mul]
  rw [hUnion, hAmean, hBmean] at hExpansion
  nlinarith [hExpansion]
