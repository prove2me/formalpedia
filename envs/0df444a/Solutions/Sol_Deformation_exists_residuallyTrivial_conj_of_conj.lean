-- Prove2me | solution 1 for Deformation.exists_residuallyTrivial_conj_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f6ec43e3-8d96-53ed-be6f-69d44d3d1ae6

import Mathlib
import Definitions.Def_Representation_AbsolutelyIrreducible
import Definitions.Def_Deformations_MatrixRepresentation
import Theorems.Thm_Deformation_exists_eq_smul_one_of_commute
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_exists_residuallyTrivial_conj_of_conj

set_option autoImplicit false

universe u v

theorem solution
    {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G]
    {k : Type u} [Field k] {A : Type v} [CommRing A] [IsLocalRing A]
    (π : A →+* k) (hπ : Function.Surjective π)
    (ρ₀ : G →* GL n k) [Representation.IsAbsolutelyIrreducible.{u} (Deformation.matrixRepresentation ρ₀)]
    (ρ₁ ρ₂ : G →* GL n A)
    (h₁ : ∀ g, ((ρ₁ g : GL n A) : Matrix n n A).map π = ((ρ₀ g : GL n k) : Matrix n n k))
    (h₂ : ∀ g, ((ρ₂ g : GL n A) : Matrix n n A).map π = ((ρ₀ g : GL n k) : Matrix n n k))
    (g : GL n A) (hg : ∀ x, g * ρ₁ x * g⁻¹ = ρ₂ x) :
    ∃ γ : GL n A, ((γ : GL n A) : Matrix n n A).map π = 1 ∧ ∀ x, γ * ρ₁ x * γ⁻¹ = ρ₂ x := by
  classical

  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨g, Subsingleton.elim _ _, hg⟩

  set gbar : GL n k := Matrix.GeneralLinearGroup.map π g with hgbar
  have hgbar_val : (gbar : Matrix n n k) = (g : Matrix n n A).map π := rfl

  have h₁' : ∀ x, Matrix.GeneralLinearGroup.map π (ρ₁ x) = ρ₀ x := fun x => Units.ext (h₁ x)
  have h₂' : ∀ x, Matrix.GeneralLinearGroup.map π (ρ₂ x) = ρ₀ x := fun x => Units.ext (h₂ x)

  have hcomm : ∀ x, (ρ₀ x : Matrix n n k) * (gbar : Matrix n n k) = (gbar : Matrix n n k) * (ρ₀ x : Matrix n n k) := by
    intro x
    have h := congrArg (Matrix.GeneralLinearGroup.map π) (hg x)
    rw [map_mul, map_mul, map_inv, h₁' x, h₂' x] at h

    have h' : gbar * ρ₀ x = ρ₀ x * gbar := by
      calc gbar * ρ₀ x = gbar * ρ₀ x * gbar⁻¹ * gbar := by rw [inv_mul_cancel_right]
        _ = ρ₀ x * gbar := by rw [h]
    exact (congrArg Units.val h').symm

  obtain ⟨abar, habar⟩ := Deformation.exists_eq_smul_one_of_commute (RingHom.id k) Function.surjective_id
    ρ₀ ρ₀ (fun x => by ext i j; rfl) (gbar : Matrix n n k) hcomm

  have habar0 : abar ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at habar
    have hdet := gbar.isUnit
    rw [Matrix.isUnit_iff_isUnit_det, habar, Matrix.det_zero] at hdet
    exact not_isUnit_zero hdet

  obtain ⟨a, ha⟩ := hπ abar
  have haker : RingHom.ker π = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π hπ)
  have hau : IsUnit a := by
    by_contra hau
    have : a ∈ RingHom.ker π := by
      rw [haker]; exact (IsLocalRing.mem_maximalIdeal a).mpr hau
    rw [RingHom.mem_ker] at this
    exact habar0 (ha.symm.trans this)
  obtain ⟨u, rfl⟩ := hau

  set s : GL n A := Units.map (Matrix.scalar n : A →+* Matrix n n A).toMonoidHom u with hs
  have hs_val : (s : Matrix n n A) = Matrix.scalar n (u : A) := rfl
  have hsinv_val : ((s⁻¹ : GL n A) : Matrix n n A) = Matrix.scalar n ((u⁻¹ : Aˣ) : A) := by
    rw [hs, ← map_inv]; rfl
  refine ⟨s⁻¹ * g, ?_, fun x => ?_⟩
  ·
    have hπu : π (u : A) = abar := ha
    have hπuinv : π ((u⁻¹ : Aˣ) : A) = abar⁻¹ := by
      rw [← hπu]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← map_mul, Units.inv_mul, map_one]
    rw [Units.val_mul, Matrix.map_mul, hsinv_val, ← hgbar_val, habar]
    have e1 : (Matrix.scalar n ((u⁻¹ : Aˣ) : A)).map π = Matrix.diagonal (fun _ : n => abar⁻¹) := by
      rw [Matrix.scalar_apply, Matrix.diagonal_map (map_zero π)]
      simp only [Function.comp_def, hπuinv]
    have e2 : abar • (1 : Matrix n n k) = Matrix.diagonal (fun _ : n => abar) := by
      ext i j
      simp [Matrix.one_apply, Matrix.diagonal_apply]
    rw [e1, e2, Matrix.diagonal_mul_diagonal]
    simp [inv_mul_cancel₀ habar0]
  ·
    have hcen : ∀ M : GL n A, s⁻¹ * M = M * s⁻¹ := by
      intro M
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hsinv_val]
      exact (Matrix.scalar_commute _ (fun r' => (Commute.all _ r')) _).eq
    calc s⁻¹ * g * ρ₁ x * (s⁻¹ * g)⁻¹
        = s⁻¹ * (g * ρ₁ x * g⁻¹) * s⁻¹⁻¹ := by group
      _ = s⁻¹ * ρ₂ x * s := by rw [hg x, inv_inv]
      _ = ρ₂ x * s⁻¹ * s := by rw [hcen]
      _ = ρ₂ x := by rw [inv_mul_cancel_right]

end S_Deformation_exists_residuallyTrivial_conj_of_conj
end P2MW
export P2MW.S_Deformation_exists_residuallyTrivial_conj_of_conj (solution)
