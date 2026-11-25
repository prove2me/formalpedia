-- Prove2me | solution 1 for CertRandQROM.lemma_3_1_trace_dist_le_euclid
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T17:36:26.072482+00:00
-- url     : https://prove2.me/submissions/dba8e498-67bf-4931-88c6-cf3356b3483d

import Theorems.Thm_SqrtQueries_pure_traceDist_le
import Definitions.Def_CommitOpen_Benign_Model
open Matrix WildeQIT

set_option autoImplicit false



/-- **Lemma 3.1** (Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, *Unconditional Certified
Randomness without Structure*, arXiv:2608.31112 (sha256 b75095a2…), §3, p.14): for any pure
states `|ψ⟩, |φ⟩`, `TraceDist(|ψ⟩, |φ⟩) ≤ ‖|ψ⟩ − |φ⟩‖₂`.

**Formalization Note** `TraceDist(|ψ⟩, |φ⟩)` is the published
`CommitOpen.Benign.traceDistance` of the density matrices `|ψ⟩⟨ψ|` and `|φ⟩⟨φ|`
(`½‖ρ − σ‖₁`). Pure states are unit vectors of `ℂ^ι` for any finite basis set `ι`. -/
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ φ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    CommitOpen.Benign.traceDistance (CommitOpen.Benign.pureState ψ)
      (CommitOpen.Benign.pureState φ) ≤ ‖ψ - φ‖ := by
  simpa only [CommitOpen.Benign.traceDistance,CommitOpen.Benign.pureState,WildeQIT.traceDist,Matrix.vecMulVec,Pi.star_apply] using SqrtQueries.pure_traceDist_le ψ φ hψ hφ