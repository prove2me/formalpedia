-- Prove2me | solution 1 for BookProof.ChapterStoneSeparable.gen_eq_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-20T05:04:01.571576+00:00
-- url     : https://prove2.me/submissions/b57b5628-60f3-466f-a045-4098b4a26a94

-- Generated from ChapterStoneSeparable.lean — solution of BookProof.ChapterStoneSeparable.gen_eq_of_hasDerivAt
import Mathlib
import Definitions.Def_ChapterStoneSeparable
import Theorems.Thm_BookProof_ChapterStoneMeasurable_WeakMeasurableUnitaryGroup_mem_genDomain_of_hasDerivAt
import Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_ext_prime
import Theorems.Thm_BookProof_FriedrichsSquare_IsFriedrichsSqExtension_symmetric
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterStoneResolvent
open BookProof.ChapterStoneSeparable



open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

set_option maxHeartbeats 1000000 in
theorem solution (T : UnboundedSelfAdjoint H) (G : WeakMeasurableUnitaryGroup H)
    (h : ∀ x : T.domain, HasDerivAt (fun t : ℝ => G.U t (x : H)) ((-Complex.I) • T.op x) 0) :
    G.gen = T := by

  have hdom : T.domain ≤ G.genDomain := fun x hx => G.mem_genDomain_of_hasDerivAt (h ⟨x, hx⟩)
  have hop : ∀ x : T.domain, G.genOp ⟨(x : H), hdom x.2⟩ = T.op x := fun x =>
    G.genOp_eq_of_hasDerivAt (x := ⟨(x : H), hdom x.2⟩) (h x)
  refine UnboundedSelfAdjoint.ext_prime (le_antisymm ?_ hdom) ?_
  · intro x hx
    refine T.mem_domain_of_inner (eta := G.genOp ⟨x, hx⟩) ?_
    intro psi
    rw [← hop psi]
    exact G.symmetric ⟨(psi : H), hdom psi.2⟩ ⟨x, hx⟩
  · intro x _ hx'
    exact hop ⟨x, hx'⟩
