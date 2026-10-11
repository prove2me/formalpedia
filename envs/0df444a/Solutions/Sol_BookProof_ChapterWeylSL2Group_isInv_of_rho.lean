-- Prove2me | solution 1 for BookProof.ChapterWeylSL2Group.isInv_of_rho
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:40:57.487988+00:00
-- url     : https://prove2.me/submissions/a5120b49-4da9-4075-9f05-067215bb38a5

-- Generated from ChapterWeylSL2Group.lean — solution of BookProof.ChapterWeylSL2Group.isInv_of_rho
import Mathlib
import Definitions.Def_ChapterWeylSL2Group
import Theorems.Thm_BookProof_ChapterWeylSL2Group_coeff_mem_of_poly_mem
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterGleasonPureMixed
import Definitions.Def_ChapterWeylSl2
open BookProof.ChapterWeylSL2Group




open BookProof.ChapterWeylSl2

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V} {R : Sl2Rep V} {N : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (h : IsExpOfSl2 rho R N) {W : Submodule ℂ V}
    (hplus : ∀ (t : ℂ), ∀ v ∈ W, rho (uPlus t) v ∈ W)
    (hminus : ∀ (t : ℂ), ∀ v ∈ W, rho (uMinus t) v ∈ W) : R.IsInv W := by

  have key : ∀ a : Module.End ℂ V,
      (∀ t : ℂ, ∀ v ∈ W,
        (∑ k ∈ Finset.range N, (t ^ k / (Nat.factorial k : ℂ)) • a ^ k) v ∈ W) →
      ∀ v ∈ W, a v ∈ W := by
    intro a ha v hv
    have hpoly : ∀ t : ℂ,
        ∑ k ∈ Finset.range N, t ^ k • (((Nat.factorial k : ℂ)⁻¹) • (a ^ k) v) ∈ W := by
      intro t
      have h1 := ha t v hv
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply] at h1
      have heq : ∀ k : ℕ, t ^ k • (((Nat.factorial k : ℂ)⁻¹) • (a ^ k) v)
          = (t ^ k / (Nat.factorial k : ℂ)) • (a ^ k) v := fun k => by
        rw [smul_smul, div_eq_mul_inv]
      simpa only [heq] using h1
    have h1 : (((Nat.factorial 1 : ℂ))⁻¹) • (a ^ 1) v ∈ W :=
      coeff_mem_of_poly_mem hpoly (lt_of_lt_of_le one_lt_two h.two_le)
    simpa using h1
  have hE : ∀ v ∈ W, R.E v ∈ W := key R.E (fun t => by rw [← h.expE t]; exact hplus t)
  have hF : ∀ v ∈ W, R.F v ∈ W := key R.F (fun t => by rw [← h.expF t]; exact hminus t)
  refine ⟨hE, hF, fun v hv => ?_⟩
  have hH : R.H v = R.E (R.F v) - R.F (R.E v) := by
    have hv' := congrArg (fun T : Module.End ℂ V => T v) R.hef
    simpa using hv'.symm
  rw [hH]
  exact Submodule.sub_mem _ (hE _ (hF _ hv)) (hF _ (hE _ hv))
