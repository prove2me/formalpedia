-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.resConst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:25.706555+00:00
-- url     : https://prove2.me/submissions/8f5957f1-e6c6-4bc5-bb3a-cc20ab2f6446

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RightIdealImageOfSurjective
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalModuleOf
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective

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
theorem _root_.solution : StatResConst := by
  unfold StatResConst
  intro O _ _ X T hT f hf x y
  set g : T := ⟨f, hf⟩ - algebraMap O T (f x) with hg
  have hgnu : ¬ IsUnit g := by
    intro hu
    have := hu.map ((Pi.evalRingHom (fun _ : X => O) x).comp T.val.toRingHom)
    simp [hg] at this
  let ψ : T →+* IsLocalRing.ResidueField O :=
    (IsLocalRing.residue O).comp ((Pi.evalRingHom (fun _ : X => O) y).comp T.val.toRingHom)
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective z
    exact ⟨algebraMap O T c, by simp [ψ]⟩
  have hmax : (RingHom.ker ψ).IsMaximal := RingHom.ker_isMaximal_of_surjective ψ hsurj
  have hker : RingHom.ker ψ = IsLocalRing.maximalIdeal T := IsLocalRing.eq_maximalIdeal hmax
  have hgm : g ∈ RingHom.ker ψ := by
    rw [hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hgnu
  rw [RingHom.mem_ker] at hgm
  simp [ψ, hg, sub_eq_zero] at hgm
  exact hgm.symm
end Formalism.RepresentationBoundsCohomology.ringDataObjects
