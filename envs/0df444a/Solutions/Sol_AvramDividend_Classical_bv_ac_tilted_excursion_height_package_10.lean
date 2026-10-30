-- Prove2me | solution 10 for AvramDividend.Classical.bv_ac_tilted_excursion_height_package
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:07:19.834283+00:00
-- url     : https://prove2.me/submissions/54d3d98a-1712-4511-a246-0906c7ddee97
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_excursion_measure_given_root
import Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Ici_of_finite_pos_noAtoms

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

-- Height package via Proved root + Open excursion-measure (e56a) + Proved continuity bridge.
-- Variant (2026-10-29): bypasses Open identity child 7d6b82d7 by combining Open
-- measure child e56a853a with Proved continuity bridge 432e2de3 (null-singleton +
-- finite tails imply ContinuousOn on Ioi 0). Distinct edge and elaboration
-- (haveI + have hcont) from candidate 18140. Still SKETCH_EXPECTED while e56a is
-- Open. No local Lean was run.
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
  obtain ⟨V, μ, hNull, hfin, htilt, hexp⟩ :=
    AvramDividend.Classical.bv_ac_esscher_excursion_measure_given_root
      X hX q hq W hW hbv hac φ hφ hroot
  haveI := hNull
  have hcont :=
    AvramDividend.Classical.continuousOn_measureReal_Ici_of_finite_pos_noAtoms
      μ hfin
  exact ⟨φ, V, μ, hφ, hNull, hfin, hcont, htilt, hexp⟩
