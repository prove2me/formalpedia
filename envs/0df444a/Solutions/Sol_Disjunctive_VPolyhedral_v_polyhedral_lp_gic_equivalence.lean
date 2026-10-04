-- Prove2me | solution 1 for Disjunctive.VPolyhedral.v_polyhedral_lp_gic_equivalence
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:56:30.883244+00:00
-- url     : https://prove2.me/submissions/b96437fe-de19-41f3-a08d-7f2e862cd764

import Mathlib
import Definitions.Def_Disjunctive_VPolyhedral_Basic

set_option autoImplicit false

namespace VPolyCexBB

open Disjunctive.VPolyhedral

/-- One disjunct with no vertices and no rays in `ℝ¹`. -/
abbrev Vi : Unit → Type := fun _ => PEmpty
abbrev Ri : Unit → Type := fun _ => PEmpty

instance instFVi : ∀ h, Fintype (Vi h) := fun _ => (inferInstance : Fintype PEmpty)
instance instFRi : ∀ h, Fintype (Ri h) := fun _ => (inferInstance : Fintype PEmpty)

/-- `Dtil = 0`, `d0til = 1` describes the empty set, as does the vertex-free V-data. -/
theorem desc_empty (vpt : ∀ h, Vi h → Fin 1 → ℝ) (rvec : ∀ h, Ri h → Fin 1 → ℝ) :
    ∀ h : Unit, {x : Fin 1 → ℝ | ∀ i, (fun (_ : Unit) (_ : Fin 1) => (1 : ℝ)) h i ≤
        (((fun _ => 0 : ∀ _ : Unit, Matrix (Fin 1) (Fin 1) ℝ) h).mulVec x) i} =
      {x : Fin 1 → ℝ | ∃ (lam : Vi h → ℝ) (mu : Ri h → ℝ), 0 ≤ lam ∧ 0 ≤ mu ∧
        ∑ p, lam p = 1 ∧ x = (∑ p, lam p • vpt h p) + ∑ r, mu r • rvec h r} := by
  intro h
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx
    have h0 := hx 0
    simp at h0
    linarith
  · rintro ⟨lam, mu, -, -, hs, -⟩
    have h0 : (∑ p : Vi h, lam p) = 0 := by
      rw [Finset.univ_eq_empty, Finset.sum_empty]
    rw [h0] at hs
    exact absurd hs zero_ne_one

end VPolyCexBB

open Disjunctive.VPolyhedral in
theorem solution : ¬ (∀ {n : ℕ} {Q : Type} [Fintype Q] {Rh : Q → ℕ}
    (Vidx Ridx : Q → Type) [∀ h, Fintype (Vidx h)] [∀ h, Fintype (Ridx h)]
    (vpt : ∀ h, Vidx h → Fin n → ℝ) (rvec : ∀ h, Ridx h → Fin n → ℝ)
    (Dtil : ∀ h, Matrix (Fin (Rh h)) (Fin n) ℝ) (d0til : ∀ h, Fin (Rh h) → ℝ)
    (hDesc : ∀ h, {x : Fin n → ℝ | ∀ i, d0til h i ≤ ((Dtil h).mulVec x) i} =
      {x : Fin n → ℝ | ∃ (lam : Vidx h → ℝ) (mu : Ridx h → ℝ), 0 ≤ lam ∧ 0 ≤ mu ∧
        ∑ p, lam p = 1 ∧ x = (∑ p, lam p • vpt h p) + ∑ r, mu r • rvec h r})
    (P : Set (Fin n → ℝ)) (xbar : Fin n → ℝ) (hxbar : xbar ∈ P)
    (alpha : Fin n → ℝ) (beta : ℝ) (hviol : dotProduct alpha xbar < beta),
    IsVPolyhedralValid Vidx Ridx vpt rvec alpha beta ↔
      ∃ (t : ℝ) (u : ∀ h, Fin (Rh h) → ℝ), 0 < t ∧
        IsCGLP129Feasible Dtil d0til (t • alpha) u (t * beta) ∧
        IsGICFromS Dtil d0til P u (t • alpha) (t * beta)) := by
  intro H
  have vpt : ∀ h, VPolyCexBB.Vi h → Fin 1 → ℝ := fun _ i => PEmpty.elim i
  have rvec : ∀ h, VPolyCexBB.Ri h → Fin 1 → ℝ := fun _ i => PEmpty.elim i
  have hv : dotProduct (fun _ : Fin 1 => (1 : ℝ)) (0 : Fin 1 → ℝ) < 1 := by
    simp
  obtain ⟨t, u, ht, hc, -⟩ :=
    (H (n := 1) (Q := Unit) (Rh := fun _ => 1) VPolyCexBB.Vi VPolyCexBB.Ri vpt rvec
      (fun _ => 0) (fun _ _ => 1) (VPolyCexBB.desc_empty vpt rvec) {0} 0 rfl
      (fun _ => 1) 1 hv).mp
      ⟨fun _ p => PEmpty.elim p, fun _ r => PEmpty.elim r⟩
  have h1 := congrFun (hc.1 ()) 0
  simp at h1
  linarith
