-- Prove2me | solution 1 for Formalism.L2.NX.supSum_tv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:19.675128+00:00
-- url     : https://prove2.me/submissions/c28113e4-c107-4ac3-8cdd-a654235db2be

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
theorem _root_.solution {R : Type} [CommRing R] (hr : 2 ≤ r) (c : R) : supSum r (tv hr c) = c := by
  simp only [supSum]
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin r), Finset.sum_eq_single (⟨1, by omega⟩ : Fin r)]
  · simp [tv, Matrix.transvection, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    ext
    simp only at h ⊢
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with h
    · have hne : a ≠ b := fun e => by rw [e] at h; omega
      simp only [tv, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]
      apply Matrix.single_apply_of_ne
      rintro ⟨h1, -⟩
      exact ha h1.symm
    · rfl
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.L2.NX
