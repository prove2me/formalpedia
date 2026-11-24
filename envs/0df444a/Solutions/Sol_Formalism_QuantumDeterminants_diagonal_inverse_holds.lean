-- Prove2me | solution 1 for Formalism.QuantumDeterminants.diagonal_inverse_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:32:36.340573+00:00
-- url     : https://prove2.me/submissions/5b084974-f350-4e56-8bc0-c9ef7f41a704

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Theorems.Thm_Formalism_QuantumDeterminants_minor_eq_of_mul
import Theorems.Thm_Formalism_QuantumDeterminants_Zhat_eq
import Theorems.Thm_Formalism_QuantumDeterminants_Sset_UH
import Theorems.Thm_Formalism_QuantumDeterminants_S_F

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution : DInv := by
  intro k r z z' hz hz' s hs s' hs' g l
  obtain ⟨U, hU0, hU1, hsF⟩ := S_F hz hs
  obtain ⟨U', hU0', hU1', hsF'⟩ := S_F hz' hs'
  have hH : sᴴ * Hpk k r * s = Hpk k r := Sset_UH hs
  have hFs : (Fm k r z)ᴴ * sᴴ = Uᴴ * (Fm k r z)ᴴ := by
    rw [← conjTranspose_mul, hsF, conjTranspose_mul]
  have hL0 : ∀ i j : Fin (r + 1), i < j → Uᴴ i j = 0 := fun i j hij => by
    simp [conjTranspose_apply, hU0 j i hij]
  have hL1 : ∀ i, Uᴴ i i = 1 := fun i => by simp [conjTranspose_apply, hU1 i]
  have hmul : Uᴴ * Zhat k r z z' (s * g * s') = Zhat k r z z' g * U' := by
    rw [Zhat_eq, Zhat_eq]
    calc Uᴴ * ((Fm k r z)ᴴ * Hpk k r * (s * g * s') * Fm k r z')
        = (Uᴴ * (Fm k r z)ᴴ) * Hpk k r * (s * g * s') * Fm k r z' := by
          simp only [Matrix.mul_assoc]
      _ = (Fm k r z)ᴴ * (sᴴ * Hpk k r * s) * g * (s' * Fm k r z') := by
          rw [← hFs]
          simp only [Matrix.mul_assoc]
      _ = (Fm k r z)ᴴ * Hpk k r * g * Fm k r z' * U' := by
          rw [hH, hsF']
          simp only [Matrix.mul_assoc]
  exact minor_eq_of_mul Uᴴ U' _ _ hL0 hL1 hU0' hU1' hmul l.val _
end Formalism.QuantumDeterminants
