-- Prove2me | solution 1 for DeletedPrimes.ae_theta_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:18:41.71982+00:00
-- url     : https://prove2.me/submissions/ef679612-2d22-4515-bbda-d824fcbfb276

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (S : Ω → Set ℕ) {α : ℝ}
    (hup : ∀ᵐ ω ∂P, theta (S ω) ≤ α / 2) (hlow : ∀ᵐ ω ∂P, α / 2 ≤ theta (S ω)) :
    ∀ᵐ ω ∂P, theta (S ω) = α / 2 := by
  filter_upwards [hup, hlow] with ω h1 h2
  exact le_antisymm h1 h2
end DeletedPrimes
