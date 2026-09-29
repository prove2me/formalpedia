-- Prove2me | solution 1 for FourToOneGames.exists_rank_one_nae_form
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-24T07:21:06.168885+00:00
-- url     : https://prove2.me/submissions/281907f8-f1f5-45b6-9e36-dd45afd253f9

import Definitions.Def_FourToOneGames_NAE

set_option autoImplicit false

open FourToOneGames

/-- The linear functional reading the 0-th coordinate of each triple:
    `phiNAE` is `1` on the basis vector `e_v` iff `v.2 = 0`. -/
noncomputable def phiNAE {ι : Type} [Fintype ι] [DecidableEq ι] :
    TripledSpace ι →ₗ[ZMod 2] ZMod 2 :=
  ((Pi.basisFun (ZMod 2) (ι × Fin 3)).constr (ZMod 2))
    (fun v : ι × Fin 3 => if v.2 = 0 then (1 : ZMod 2) else 0)

/-- `phiNAE` on standard basis vectors. -/
theorem phiNAE_single {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι × Fin 3) :
    phiNAE (Pi.single v 1) = if v.2 = 0 then (1 : ZMod 2) else 0 := by
  unfold phiNAE
  rw [← Pi.basisFun_apply (ZMod 2) (ι × Fin 3) v]
  exact Module.Basis.constr_basis _ _ _ _

/-- `phiNAE` is nonzero (needs `ι` nonempty). -/
theorem phiNAE_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    phiNAE ≠ (0 : TripledSpace ι →ₗ[ZMod 2] ZMod 2) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  intro h
  have h1 : phiNAE (Pi.single (i₀, 0) 1) = (0 : ZMod 2) := by rw [h]; rfl
  rw [phiNAE_single] at h1
  have h2 : ((i₀, 0) : ι × Fin 3).2 = (0 : Fin 3) := rfl
  rw [if_pos h2] at h1
  exact one_ne_zero h1

/-- The rank-one bilinear form `f x y = phiNAE x * phiNAE y`. -/
noncomputable def formNAE {ι : Type} [Fintype ι] [DecidableEq ι] :
    TripledSpace ι →ₗ[ZMod 2] TripledSpace ι →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) (fun x y => phiNAE x * phiNAE y)
    (fun x₁ x₂ y => by
      show phiNAE (x₁ + x₂) * phiNAE y = phiNAE x₁ * phiNAE y + phiNAE x₂ * phiNAE y
      rw [map_add, add_mul])
    (fun c x y => by
      show phiNAE (c • x) * phiNAE y = c • (phiNAE x * phiNAE y)
      simp [map_smul, smul_eq_mul, mul_assoc])
    (fun x y₁ y₂ => by
      show phiNAE x * phiNAE (y₁ + y₂) = phiNAE x * phiNAE y₁ + phiNAE x * phiNAE y₂
      rw [map_add, mul_add])
    (fun c x y => by
      show phiNAE x * phiNAE (c • y) = c • (phiNAE x * phiNAE y)
      simp [map_smul, smul_eq_mul, mul_left_comm])

/-- `formNAE` on pairs of standard basis vectors. -/
theorem formNAE_bilin {ι : Type} [Fintype ι] [DecidableEq ι] (u v : ι × Fin 3) :
    formNAE (Pi.single u 1) (Pi.single v 1)
      = (if u.2 = 0 then (1 : ZMod 2) else 0) * (if v.2 = 0 then 1 else 0) := by
  show phiNAE (Pi.single u 1) * phiNAE (Pi.single v 1) = _
  rw [phiNAE_single, phiNAE_single]

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    ∃ f : TripledSpace ι →ₗ[ZMod 2] TripledSpace ι →ₗ[ZMod 2] ZMod 2,
      IsSymmetricForm f ∧ NAESatisfyingForm f ∧
        ∃ φ : TripledSpace ι →ₗ[ZMod 2] ZMod 2, φ ≠ 0 ∧
          ∀ x y : TripledSpace ι, f x y = φ x * φ y := by
  refine ⟨formNAE, ?_, ?_, phiNAE, phiNAE_ne_zero, fun x y => rfl⟩
  · -- symmetric: phiNAE x * phiNAE y = phiNAE y * phiNAE x
    unfold IsSymmetricForm
    intro x y
    show phiNAE x * phiNAE y = phiNAE y * phiNAE x
    exact mul_comm _ _
  · -- NAE-satisfying: on each triple the coefficients are (1,0,0), so the sum is 1
    unfold NAESatisfyingForm
    intro i
    simp only [bilinCoeff, formNAE_bilin]
    -- the goal is now a closed ZMod 2 equation; kernel computation closes it
    rfl
