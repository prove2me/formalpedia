-- Prove2me | solution 1 for Formalism.NG.BlockDetAlt.phiMat_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:33:22.27729+00:00
-- url     : https://prove2.me/submissions/5aee523f-cdc7-4483-a02d-26cd18eb2f45

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst
import Theorems.Thm_Formalism_NG_BlockDetAlt_phiMat_block

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.BlockDetAlt
variable {O : Type*} [CommRing O] {X' : Type*}
variable {d : Type} [Fintype d] [DecidableEq d]
variable {d : Type} [Fintype d] [DecidableEq d]
namespace Formalism.NG.BlockDetAlt
theorem _root_.solution (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) {g : Type} [Fintype g]
    [DecidableEq g] (Θ : Matrix g g R') (p q : g) :
    (Matrix.of fun i j => phiMat R' Θ (p, i) (q, j)) ∈ goodM R' := by
  show ∀ n, coefMat n _ ∈ R'
  intro n
  rw [phiMat_block]
  apply Subalgebra.sub_mem
  · split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  · split_ifs
    · exact (Θ p q).2
    · exact Subalgebra.zero_mem _
end Formalism.NG.BlockDetAlt
