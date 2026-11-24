-- Prove2me | solution 1 for Formalism.L2.NX.tv_uniTri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:14:12.697899+00:00
-- url     : https://prove2.me/submissions/4ed3652a-aa09-40c4-b16b-271616566a3c

import Mathlib
import Definitions.Def_Formalism_AlgebraicWeights_IsAlgWeight
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.NX
variable {ι : Type} [Fintype ι] {p : ι → ℕ} {r : ℕ}
namespace Formalism.L2.NX
theorem _root_.solution {R : Type} [CommRing R] (hr : 2 ≤ r) (c : R) : IsUniTri r (tv hr c) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have hab' : (b : ℕ) < a := hab
    have hne : a ≠ b := fun e => by rw [e] at hab'; omega
    simp only [tv, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]
    apply Matrix.single_apply_of_ne
    rintro ⟨h1, h2⟩
    rw [Fin.ext_iff] at h1 h2
    simp only at h1 h2
    omega
  · simp only [tv, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq]
    rw [Matrix.single_apply_of_ne, add_zero]
    rintro ⟨h1, h2⟩
    rw [← h2, Fin.ext_iff] at h1
    simp at h1
end Formalism.L2.NX
