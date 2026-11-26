-- Prove2me | solution 1 for FiniteEnergyPlane.flow_add_apply
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-26T21:45:10.530136+00:00
-- url     : https://prove2.me/submissions/61d1548f-3026-47a1-963c-8bc512c95b1a

import Mathlib



/-! Child D of P c5a21fab (via G): `flow_add_apply`. -/

namespace FiniteEnergyPlane

open Set
open scoped ContDiff

theorem flow_add_apply_aux (X : ℂ → ℂ) (hX : ContDiff ℝ ∞ X) (hXK : HasCompactSupport X)
    (ψ : ℝ → ℂ → ℂ) (hψ0 : ∀ y, ψ 0 y = y)
    (hψd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t) (s r : ℝ) (y : ℂ) :
    ψ s (ψ r y) = ψ (s + r) y := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXK hX (by simp)
  have hKs : ∀ t : ℝ, LipschitzOnWith K ((fun _ : ℝ => X) t) ((fun _ : ℝ => (univ : Set ℂ)) t) :=
    fun _ => hK.lipschitzOnWith
  have hf : ∀ t, HasDerivAt (fun s => ψ s (ψ r y)) (X (ψ t (ψ r y))) t := fun t => hψd t _
  have hg : ∀ t, HasDerivAt (fun s => ψ (s + r) y) (X (ψ (t + r) y)) t := fun t =>
    (hψd (t + r) y).comp_add_const t r
  have h0 : ψ 0 (ψ r y) = ψ (0 + r) y := by rw [hψ0, zero_add]
  rcases le_total 0 s with h | h
  · exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => X) (s := fun _ => univ) (K := K)
      (a := 0) (b := s) (f := fun s => ψ s (ψ r y)) (g := fun s => ψ (s + r) y)
      (fun t _ => hKs t) (fun t _ => (hf t).continuousAt.continuousWithinAt)
      (fun t _ => (hf t).hasDerivWithinAt) (fun _ _ => mem_univ _)
      (fun t _ => (hg t).continuousAt.continuousWithinAt)
      (fun t _ => (hg t).hasDerivWithinAt) (fun _ _ => mem_univ _) h0 ⟨h, le_rfl⟩
  · exact ODE_solution_unique_of_mem_Icc_left (v := fun _ => X) (s := fun _ => univ) (K := K)
      (a := s) (b := 0) (f := fun s => ψ s (ψ r y)) (g := fun s => ψ (s + r) y)
      (fun t _ => hKs t) (fun t _ => (hf t).continuousAt.continuousWithinAt)
      (fun t _ => (hf t).hasDerivWithinAt) (fun _ _ => mem_univ _)
      (fun t _ => (hg t).continuousAt.continuousWithinAt)
      (fun t _ => (hg t).hasDerivWithinAt) (fun _ _ => mem_univ _) h0 ⟨le_rfl, h⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open scoped ContDiff

theorem solution (X : ℂ → ℂ) (hX : ContDiff ℝ ∞ X) (hXK : HasCompactSupport X)
    (ψ : ℝ → ℂ → ℂ) (hψ0 : ∀ y, ψ 0 y = y)
    (hψd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t) (s r : ℝ) (y : ℂ) :
    ψ s (ψ r y) = ψ (s + r) y :=
  flow_add_apply_aux X hX hXK ψ hψ0 hψd s r y
