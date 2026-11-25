-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.density_point_of_corner_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:22:51.986195+00:00
-- url     : https://prove2.me/submissions/ec88892c-00c7-4c91-8f26-8b97555d6c7b

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_FinrankRangeEq
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdemFactor
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_DensityPointOfCornerSimple
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_point_generic
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_point_pi

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
theorem _root_.solution (hD : StatDensity) (hC : StatCornerSimple) : DensityPointExists := by
  intro O _ _ _ X _ T d _ _ G _ r π t bl χ₁ ε hP eB e₁ hI hG3 g₀ hε L ϖ hϖ
  classical
  have hsep := hP.2.1
  obtain ⟨heBm, -, heBB, -, -, -, -, -, heBπ, -⟩ := hI
  have hpt : ∀ y : {y : X // y ≠ π}, ∃ (j : X → O) (a : X → Matrix d d O), j ∈ T ∧
      (∀ z, z ≠ y.1 → j z = 0) ∧ a ∈ tSpan T r ∧
      (blockPoly ((eB y.1).map (algebraMap O (FractionRing O)))
        ((eB y.1 * r g₀ y.1 * eB y.1 + ϖ ^ L • (j y.1 • (eB y.1 * a y.1 * eB y.1))).map
          (algebraMap O (FractionRing O)))).Separable := by
    intro y
    obtain ⟨m, c, P, hG⟩ := hG3 y.1
    exact point_generic hD hC T r hsep eB heBm heBB y.1 m c P hG (r g₀ y.1) (ϖ ^ L) (pow_ne_zero _ hϖ)
  choose j a hjT hj0 haT hjsep using hpt
  let eqv := Fintype.equivFin {y : X // y ≠ π}
  refine ⟨Fintype.card {y : X // y ≠ π}, fun i => j (eqv.symm i), fun i => a (eqv.symm i),
    fun i => ⟨hjT _, hj0 _ π (eqv.symm i).2.symm, haT _⟩, fun x => ?_⟩
  beta_reduce
  by_cases hx : x = π
  · rw [hx]
    have hzero : ∑ i, j (eqv.symm i) π • (eB π * a (eqv.symm i) π * eB π) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hj0 _ π (eqv.symm i).2.symm, zero_smul]
    rw [hzero, smul_zero, add_zero]
    exact point_pi T r π bl χ₁ ε hP eB heBπ g₀ hε
  · have hsum : ∑ i, j (eqv.symm i) x • (eB x * a (eqv.symm i) x * eB x) =
        j ⟨x, hx⟩ x • (eB x * a ⟨x, hx⟩ x * eB x) := by
      rw [Finset.sum_eq_single (eqv ⟨x, hx⟩)]
      · simp
      · intro i _ hi
        rw [hj0 _ x, zero_smul]
        intro hxe
        apply hi
        rw [← eqv.apply_symm_apply i]
        exact congrArg eqv (Subtype.ext hxe.symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsum]
    exact hjsep ⟨x, hx⟩
end Formalism.RepresentationBoundsCohomology.ringDataObjects
