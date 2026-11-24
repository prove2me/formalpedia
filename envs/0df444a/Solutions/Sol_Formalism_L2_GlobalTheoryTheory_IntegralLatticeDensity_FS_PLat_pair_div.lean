-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.PLat.pair_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:17:54.947471+00:00
-- url     : https://prove2.me/submissions/6ce548c9-6abb-4a53-87a5-cd54db43aea3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PUnitBasis
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_norm_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K] [CharZero K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {c : K →+* K} {h : V → V → K} {O : Subring K} {L : AddSubgroup V} {p : ℕ}
variable (P : PLat c h O L p) {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} {n : ι → ℕ} (G : Good h L p v n)
  (hdiv : ∀ y ∈ L, (∀ i, h y (v i) = 0) → ∃ k : ℕ, h y y = (p : K) * k)
include P G hdiv
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
namespace PLat
theorem _root_.solution (y z : V) (hy : y ∈ L) (hy' : ∀ i, h y (v i) = 0) (hz : z ∈ L) (hz' : ∀ i, h z (v i) = 0) :
    ∃ t' ∈ O, h y z = (p : K) * t' := by
  have H := P.herm
  have tr : ∀ y z : V, y ∈ L → (∀ i, h y (v i) = 0) → z ∈ L → (∀ i, h z (v i) = 0) →
      ∃ k : ℤ, h y z + c (h y z) = (p : K) * k := by
    intro y z hy hy' hz hz'
    obtain ⟨k1, e1⟩ := hdiv (y + z) (L.add_mem hy hz) (fun i => by rw [H.add_left, hy' i, hz' i, add_zero])
    obtain ⟨k2, e2⟩ := hdiv y hy hy'
    obtain ⟨k3, e3⟩ := hdiv z hz hz'
    have E0 := H.norm_add y z
    refine ⟨(k1 : ℤ) - k2 - k3, ?_⟩
    push_cast
    linear_combination e1 - E0 - e2 - e3
  obtain ⟨ω, hω, crit⟩ := P.crit
  refine crit _ (P.int _ hy _ hz) (tr y z hy hy' hz hz') ?_
  have := tr (ω • y) z (P.smul _ hω _ hy) (fun i => by rw [H.smul_left, hy' i, mul_zero]) hz hz'
  rwa [H.smul_left] at this
end PLat
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
