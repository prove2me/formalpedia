-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.unimodUnramUnique_transport
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:02.983507+00:00
-- url     : https://prove2.me/submissions/ce14fbca-cbd6-4b76-8aa4-72f93c2f6ddd

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementJac
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
open Polynomial IsLocalRing Matrix
variable {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R}
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ]
    [DecidableEq ι] (e : κ ≃ ι) (B : Matrix ι ι R) (g : Matrix κ κ R)
    (hg : gᴴ * B.submatrix e e * g = 1) :
    (g.submatrix e.symm e.symm)ᴴ * B * g.submatrix e.symm e.symm = 1 := by
  have hB : B = (B.submatrix e e).submatrix e.symm e.symm := by simp
  rw [hB, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hg,
    submatrix_one_equiv]
end Formalism.HermitianLatticesTheory
