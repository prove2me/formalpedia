-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.pencil_choose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:05:24.459858+00:00
-- url     : https://prove2.me/submissions/86cbf180-91ff-461b-af1c-f8c9e5b6dc1b

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_FinrankRangeEq
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdemFactor
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_DensityPointOfCornerSimple
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_pencil_disc
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_charpoly_smul_sep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution {O : Type*} [CommRing O] [Infinite O] {K : Type*} [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) {S : Type*} [Fintype S] [DecidableEq S]
    (B0 B1 : Matrix S S K) (h : B1.charpoly.Separable) (c0 : K) (hc0 : c0 ≠ 0) :
    ∃ l : O, (B0 + (c0 * algebraMap O K l) • B1).charpoly.Separable := by
  classical
  obtain ⟨D, hD0, hD⟩ := pencil_disc B0 B1 h
  have hfin : Set.Finite {l : O | D.eval (c0 * algebraMap O K l)⁻¹ = 0} := by
    apply Set.Finite.of_finite_image (f := fun l => (c0 * algebraMap O K l)⁻¹)
    · refine (D.roots.toFinset.finite_toSet).subset ?_
      rintro _ ⟨l, hl, rfl⟩
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_roots hD0).2 hl
    · intro l1 _ l2 _ h12
      exact hinj (mul_left_cancel₀ hc0 (inv_inj.1 h12))
  obtain ⟨l, hl⟩ := (hfin.union (Set.finite_singleton (0 : O))).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff, not_or] at hl
  obtain ⟨hDl, hl0⟩ := hl
  have hν : c0 * algebraMap O K l ≠ 0 :=
    mul_ne_zero hc0 fun h0 => hl0 (hinj (by rw [h0, map_zero]))
  refine ⟨l, ?_⟩
  have heq : B0 + (c0 * algebraMap O K l) • B1 =
      (c0 * algebraMap O K l) • ((c0 * algebraMap O K l)⁻¹ • B0 + B1) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hν, one_smul]
  rw [heq]
  exact charpoly_smul_sep _ _ hν (hD _ hDl)
end Formalism.RepresentationBoundsCohomology.ringDataObjects
