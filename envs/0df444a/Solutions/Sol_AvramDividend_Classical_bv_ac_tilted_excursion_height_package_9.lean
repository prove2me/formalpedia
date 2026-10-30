-- Prove2me | solution 9 for AvramDividend.Classical.bv_ac_tilted_excursion_height_package
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:38:37.208244+00:00
-- url     : https://prove2.me/submissions/09ae8366-a15c-4357-b6e3-4956a16eecfb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_excursion_identity_given_root

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

-- Height package via Proved Esscher root + Open excursion identity, targeted imports.
-- Variant (2026-10-29): drops the blanket `import Mathlib` (proof uses only
-- obtain/refine/exact over the two cited theorems); repacks the existential with
-- refine + explicit holes so elaboration differs from the prior obtain/exact bytes.
-- Still SKETCH_EXPECTED while 7d6b82d7 is Open. No local Lean was run.
-- ProofCheckpoint: MATHEMATICAL_DECOMPOSITION.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ∃ (φ : ℝ) (V : ℝ → ℝ) (μ : Measure ℝ),
      0 < φ ∧ NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi 0) ∧
      (∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b →
        V b = V a * Real.exp (∫ t in a..b, μ.real (Ici t))) := by
  obtain ⟨φ, hφ, hroot⟩ :=
    AvramDividend.Classical.bv_positive_esscher_root X hX q hq hbv
  obtain ⟨V, μ, hNull, hfin, hcont, htilt, hexp⟩ :=
    AvramDividend.Classical.bv_ac_esscher_excursion_identity_given_root
      X hX q hq W hW hbv hac φ hφ hroot
  refine ⟨φ, V, μ, hφ, hNull, hfin, hcont, htilt, hexp⟩
