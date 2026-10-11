-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.isHermCol_finsetSum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:22:12.648881+00:00
-- url     : https://prove2.me/submissions/6a824959-eed3-429f-baee-b42b7cf1871d

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.isHermCol_finsetSum
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.QgCouplingDGammaSum




open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)}
    (h : ∀ i ∈ s, IsHermCol (cols i)) : IsHermCol (fun k => ∑ i ∈ s, cols i k) := by

  intro j k
  simp only [Finsupp.finset_sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i hi => h i hi j k
