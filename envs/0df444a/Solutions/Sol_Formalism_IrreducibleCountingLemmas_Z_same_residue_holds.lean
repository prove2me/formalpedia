-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.same_residue_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:33.424806+00:00
-- url     : https://prove2.me/submissions/5374d989-e97c-4573-b083-f27ace4e43b0

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
import Mathlib
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Adjugate
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Mobius
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Window
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Koszul
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Parabolic
import Definitions.Def_Formalism_ResultantValuation_BoundedCubic
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace
import Definitions.Def_Formalism_ResultantValuation_PrimePairDyadicDisjointAlt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_natAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_natAdd
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_natAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_natAdd
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : SameResidue := by
  intro O _ _ X _ T hT a ha x y
  let ev : X → (T →+* IsLocalRing.ResidueField O) := fun z =>
    (IsLocalRing.residue O).comp ((Pi.evalRingHom (fun _ : X => O) z).comp T.val.toRingHom)
  have hev : ∀ z (b : T), ev z b = IsLocalRing.residue O ((b : X → O) z) := fun z b => rfl
  have hsurj : ∀ z, Function.Surjective (ev z) := by
    intro z k
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective k
    exact ⟨algebraMap O T r, by rw [hev]; simp⟩
  have hmax : ∀ z, RingHom.ker (ev z) = IsLocalRing.maximalIdeal T := fun z =>
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (hsurj z))
  have hmem : ((⟨a, ha⟩ : T) - algebraMap O T (a x)) ∈ RingHom.ker (ev x) := by
    rw [RingHom.mem_ker, map_sub, hev, hev]
    simp
  rw [hmax x, ← hmax y, RingHom.mem_ker, map_sub, hev, hev, sub_eq_zero] at hmem
  simpa using hmem.symm
end Formalism.IrreducibleCountingLemmas.Z
