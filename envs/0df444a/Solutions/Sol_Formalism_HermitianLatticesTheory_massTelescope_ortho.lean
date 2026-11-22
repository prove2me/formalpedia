-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.massTelescope_ortho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:42:56.15756+00:00
-- url     : https://prove2.me/submissions/fb9019f8-eb21-4908-961c-64af3258c8ee

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassTelescope
import Theorems.Thm_Formalism_HermitianLatticesTheory_massTelescope_form_apply
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable (K : Type) [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (n : ℕ) :
    IsOrthoLattice (massTelescope_form K n) (massTelescope_lat K n) n := by
  unfold IsOrthoLattice
  refine ⟨⇑(Pi.basisFun K (Fin n)), (Pi.basisFun K (Fin n)).linearIndependent,
    (Pi.basisFun K (Fin n)).span_eq, rfl, ?_⟩
  intro i j
  rw [massTelescope_form_apply]
  simp only [Pi.basisFun_apply]
  rw [Finset.sum_eq_single i]
  · by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Pi.single_eq_of_ne hij]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hi
    exact absurd (Finset.mem_univ i) hi
end Formalism.HermitianLatticesTheory
