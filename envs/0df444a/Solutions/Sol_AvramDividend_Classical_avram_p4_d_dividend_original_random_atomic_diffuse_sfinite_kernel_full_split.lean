-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_random_atomic_diffuse_sfinite_kernel_full_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:14:59.572348+00:00
-- url     : https://prove2.me/submissions/6a6bd21e-731b-4680-a660-7367b55d95f9

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_canonical_atomic_sfinite_kernel
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_canonical_diffuse_sfinite_kernel
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_canonical_diffuse_submeasure_null_singletons
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_atomic_support_jointly_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Canonical original source payment atoms and its atomless complement are
both measurable s-finite kernels whose pointwise sum is the entire Stieltjes
dividendMeasure, with no lost time-zero or horizon mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∃ (κatom κdiff : Kernel Ω ℝ),
      IsSFiniteKernel κatom ∧ IsSFiniteKernel κdiff ∧
      (∀ ω : Ω, κatom ω + κdiff ω = dividendMeasure D ω) ∧
      (∀ (ω : Ω) (t : ℝ), κdiff ω {t} = 0) := by
  obtain ⟨κatom, hAtomFinite, hAtom⟩ :=
    avram_p4_d_dividend_original_canonical_atomic_sfinite_kernel D hD
  obtain ⟨κdiff, hDiffFinite, hDiff⟩ :=
    avram_p4_d_dividend_original_canonical_diffuse_sfinite_kernel D hD
  refine ⟨κatom, κdiff, hAtomFinite, hDiffFinite, ?_, ?_⟩
  · intro ω
    have hs : MeasurableSet
        {t : ℝ | 0 < dividendMeasure D ω {t}} := by
      have hgraph :=
        avram_p4_d_dividend_original_random_atomic_support_jointly_measurable
          D hD
      have hpre := hgraph.preimage
        ((measurable_const : Measurable (fun _ : ℝ => ω)).prodMk measurable_id)
      simpa only [Set.preimage, Set.mem_setOf_eq, id_eq] using hpre
    calc
      κatom ω + κdiff ω =
          (dividendMeasure D ω).restrict
            {t : ℝ | 0 < dividendMeasure D ω {t}} +
          (dividendMeasure D ω).restrict
            ({t : ℝ | 0 < dividendMeasure D ω {t}})ᶜ := by
              rw [hAtom ω, hDiff ω]
              rfl
      _ = dividendMeasure D ω := Measure.restrict_add_restrict_compl hs
  · intro ω t
    rw [hDiff ω]
    exact avram_p4_d_dividend_original_canonical_diffuse_submeasure_null_singletons
      D hD ω t
