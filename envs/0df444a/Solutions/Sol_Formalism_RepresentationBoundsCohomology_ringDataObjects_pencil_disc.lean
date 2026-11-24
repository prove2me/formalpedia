-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.pencil_disc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:50:09.303032+00:00
-- url     : https://prove2.me/submissions/beb0c9d5-c170-473a-a37e-0b7993352db7

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_FinrankRangeEq
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdemFactor
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_DensityPointOfCornerSimple
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_sep_iff_resultant

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
theorem _root_.solution {K : Type*} [Field K] {S : Type*} [Fintype S] [DecidableEq S] (B0 B1 : Matrix S S K)
    (h : B1.charpoly.Separable) :
    ∃ D : Polynomial K, D ≠ 0 ∧ ∀ c, D.eval c ≠ 0 → (c • B0 + B1).charpoly.Separable := by
  classical
  set M : Matrix S S (Polynomial K) :=
    (Polynomial.X : Polynomial K) • B0.map Polynomial.C + B1.map Polynomial.C with hM
  set p := M.charpoly with hp
  have hev : ∀ c : K, (p.resultant (Polynomial.derivative p) (Fintype.card S) (Fintype.card S)).eval c =
      (c • B0 + B1).charpoly.resultant (Polynomial.derivative (c • B0 + B1).charpoly)
        (Fintype.card S) (Fintype.card S) := by
    intro c
    have hm : M.map (Polynomial.evalRingHom c) = c • B0 + B1 := by
      ext i j
      simp [hM]
      try ring
    rw [← hm, Matrix.charpoly_map, Polynomial.derivative_map, Polynomial.resultant_map_map]
    rfl
  have hsep : ∀ c : K, (p.resultant (Polynomial.derivative p) (Fintype.card S) (Fintype.card S)).eval c ≠ 0 ↔
      (c • B0 + B1).charpoly.Separable := by
    intro c
    rw [hev, ← sep_iff_resultant (c • B0 + B1).charpoly (Matrix.charpoly_monic _),
      Matrix.charpoly_natDegree_eq_dim]
  refine ⟨p.resultant (Polynomial.derivative p) (Fintype.card S) (Fintype.card S), fun h0 => ?_,
    fun c hc => (hsep c).mp hc⟩
  have h1 := (hsep 0).mpr (by simpa using h)
  rw [h0, Polynomial.eval_zero] at h1
  exact h1 rfl
end Formalism.RepresentationBoundsCohomology.ringDataObjects
