-- Prove2me | solution 1 for DualMirrorAlloc.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:14:38.921205+00:00
-- url     : https://prove2.me/submissions/e1d8b14b-54d4-41f8-9756-1437e3def1b4

import Mathlib
import Definitions.Def_DualMirrorAlloc_Model

open DualMirrorAlloc in
theorem solution {S : Type*} {d m : ℕ}
    (R : Requests S d m) (ρ : Fin m → ℝ) (hmodel : IsModel R ρ)
    (T : ℕ) (γ : Fin T → S) (mu : Fin m → ℝ) (hmu : mu ∈ orthant m)
    (hbdd : ∀ t, BddAbove ((fun x => R.f (γ t) x - mu ⬝ᵥ R.b (γ t) x) '' R.X (γ t))) :
    OPT R ρ γ ≤ dualFn R ρ mu γ := by
  have hmu0 : 0 ≤ mu := hmu
  unfold OPT
  apply csSup_le
  · refine ⟨∑ t, R.f (γ t) ((fun _ => 0) t), fun _ => 0, fun t => hmodel.zero_mem _, ?_, rfl⟩
    simp only [hmodel.b_zero, Finset.sum_const_zero]
    intro j
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (hmodel.rho_pos j).le
  · rintro v ⟨x, hx, hb, rfl⟩
    unfold dualFn
    have h1 : ∀ t, R.f (γ t) (x t) - mu ⬝ᵥ R.b (γ t) (x t) ≤ fstar R (γ t) mu := fun t =>
      le_csSup (hbdd t) (Set.mem_image_of_mem _ (hx t))
    have h2 : mu ⬝ᵥ (∑ t, R.b (γ t) (x t)) ≤ mu ⬝ᵥ ((T : ℝ) • ρ) :=
      dotProduct_le_dotProduct_of_nonneg_left hb hmu0
    rw [dotProduct_sum, dotProduct_smul, smul_eq_mul, dotProduct_comm mu ρ] at h2
    have h3 := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => h1 t)
    rw [Finset.sum_sub_distrib] at h3
    linarith
