-- Prove2me | solution 1 for BookProof.YangMillsFriedrichs.weylOpDom_symmetricOn_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T20:38:45.779325+00:00
-- url     : https://prove2.me/submissions/ae9ce574-3b1b-4efc-93d1-2544e6bf8e6b

-- Generated from ChapterYangMillsFriedrichs.lean — solution of BookProof.YangMillsFriedrichs.weylOpDom_symmetricOn_inc
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
open BookProof.YangMillsFriedrichs




open BookProof.FarisLavine



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {n m : ℕ} {pi : Fin n → D →ₗ[ℂ] D} {Bf : Fin m → D →ₗ[ℂ] D}
    (hpi : ∀ i, SymmetricOn D (D.subtype.comp (pi i)))
    (hB : ∀ a, SymmetricOn D (D.subtype.comp (Bf a))) :
    SymmetricOn D (weylOp pi Bf) := by

  intro x y
  have hsq : ∀ (T : D →ₗ[ℂ] D), SymmetricOn D (D.subtype.comp T) →
      (inner ℂ ((T (T x) : D) : F) ((y : D) : F) : ℂ)
        = inner ℂ ((x : D) : F) ((T (T y) : D) : F) := by
    intro T hT
    have h1 := hT (T x) y
    have h2 := hT x (T y)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1 h2
    rw [h1, h2]
  rw [weylOp_apply, weylOp_apply, inner_smul_left, inner_smul_right, inner_add_left,
    inner_add_right, sum_inner, sum_inner, inner_sum, inner_sum]
  have hpisum : ∀ i : Fin n, (inner ℂ ((pi i (pi i x) : D) : F) ((y : D) : F) : ℂ)
      = inner ℂ ((x : D) : F) ((pi i (pi i y) : D) : F) := fun i => hsq (pi i) (hpi i)
  have hBsum : ∀ a : Fin m, (inner ℂ ((Bf a (Bf a x) : D) : F) ((y : D) : F) : ℂ)
      = inner ℂ ((x : D) : F) ((Bf a (Bf a y) : D) : F) := fun a => hsq (Bf a) (hB a)
  rw [Finset.sum_congr rfl fun i _ => hpisum i, Finset.sum_congr rfl fun a _ => hBsum a,
    Complex.conj_ofReal]
