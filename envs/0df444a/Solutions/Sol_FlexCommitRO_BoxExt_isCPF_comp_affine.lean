-- Prove2me | solution 1 for FlexCommitRO.BoxExt.isCPF_comp_affine
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:14:57.06099+00:00
-- url     : https://prove2.me/submissions/15186fed-8ad7-4b56-8209-314e56e75a76

import Mathlib
import Definitions.Def_FlexCommitRO_BoxExt_WorstCaseDP

set_option autoImplicit false
open Matrix FlexCommitRO.BoxExt

theorem solution {m k : ℕ} (g : (Fin k → ℝ) → EReal) (hg : IsCPF g)
    (M : Matrix (Fin k) (Fin m) ℝ) (v : Fin k → ℝ) :
    IsCPF (fun s : Fin m → ℝ => g (M *ᵥ s + v)) := by
  obtain ⟨h1, ⟨kk, G, g0, hdom⟩, hconv, hlsc⟩ := hg
  let φ : (Fin m → ℝ) →ᵃ[ℝ] (Fin k → ℝ) :=
    { toFun := fun s => M *ᵥ s + v
      linear := Matrix.mulVecLin M
      map_vadd' := by
        intro p w
        simp only [vadd_eq_add, Matrix.mulVecLin_apply, Matrix.mulVec_add]
        abel }
  have hcont : Continuous (fun s : Fin m → ℝ => M *ᵥ s + v) :=
    (continuous_const.matrix_mulVec continuous_id).add continuous_const
  refine ⟨fun s => h1 _, ⟨kk, G * M, g0 - G *ᵥ v, ?_⟩, ?_, ?_⟩
  · ext s
    have := Set.ext_iff.mp hdom (M *ᵥ s + v)
    simp only [Set.mem_setOf_eq] at this ⊢
    rw [this, Matrix.mulVec_add, Matrix.mulVec_mulVec]
    exact (le_sub_iff_add_le).symm
  · exact hconv.comp_affineMap φ
  · exact hlsc.comp hcont.continuousOn (fun x hx => hx)
