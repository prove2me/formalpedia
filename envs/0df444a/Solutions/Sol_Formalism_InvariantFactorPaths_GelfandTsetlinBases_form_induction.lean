-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.form_induction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:06.558945+00:00
-- url     : https://prove2.me/submissions/bb884985-12df-45c2-9d6c-f4447098f098

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_basisF_empty
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_basisF_insert

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {R : Type*} [CommRing R] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution {P : Form R n → Prop} (h1 : P oneF)
    (hadd : ∀ K K', P K → P K' → P (K + K')) (hsmul : ∀ (c : R) K, P K → P (c • K))
    (hw : ∀ K X, P K → P (wedgeF K X)) (K : Form R n) : P K := by
  classical
  have hzero : P 0 := by
    have := hsmul 0 oneF h1
    rwa [zero_smul] at this
  have hbasis : ∀ I, P (basisF I) := by
    intro I
    exact Finset.induction_on_max I (by rw [basisF_empty]; exact h1)
      (fun a s hs ih => by rw [basisF_insert hs]; exact hw _ _ ih)
  have hK : K = ∑ I, K I • basisF I := by
    funext J
    simp [basisF, Finset.sum_apply]
  rw [hK]
  exact Finset.sum_induction _ P hadd hzero (fun I _ => hsmul _ _ (hbasis I))
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
