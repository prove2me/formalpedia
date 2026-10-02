-- Prove2me | solution 1 for Disjunctive.VPolyhedral.v_polyhedral_validity
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:09:05.467369+00:00
-- url     : https://prove2.me/submissions/f19a2a69-2b20-414d-9da2-229f1440bf81

import Mathlib
import Definitions.Def_Disjunctive_VPolyhedral_Basic

set_option autoImplicit false

namespace VPolyCexCC

open Disjunctive.VPolyhedral

/-- One disjunct with no vertices and one ray `r = 1` in `ℝ¹`. -/
abbrev Vi : Unit → Type := fun _ => PEmpty
abbrev Ri : Unit → Type := fun _ => Unit

instance instFVi : ∀ h, Fintype (Vi h) := fun _ => (inferInstance : Fintype PEmpty)
instance instFRi : ∀ h, Fintype (Ri h) := fun _ => (inferInstance : Fintype Unit)

/-- With no vertices, `∑ lam = 1` is impossible, so the disjunctive set is empty. -/
theorem disj_empty (vpt : ∀ h, Vi h → Fin 1 → ℝ) (rvec : ∀ h, Ri h → Fin 1 → ℝ) :
    ∀ x, x ∉ DisjSet Vi Ri vpt rvec := by
  intro x hx
  simp only [DisjSet, Set.mem_iUnion] at hx
  obtain ⟨h, lam, mu, -, hsum, -, -⟩ := hx
  have h0 : (∑ i : Vi h, lam i) = 0 := by
    rw [Finset.univ_eq_empty, Finset.sum_empty]
  rw [h0] at hsum
  exact zero_ne_one hsum

end VPolyCexCC

open Disjunctive.VPolyhedral in
theorem solution : ¬ (∀ {n : ℕ} {Q : Type} (Vidx Ridx : Q → Type)
    [∀ h, Fintype (Vidx h)] [∀ h, Fintype (Ridx h)] (vpt : ∀ h, Vidx h → Fin n → ℝ)
    (rvec : ∀ h, Ridx h → Fin n → ℝ) (alpha : Fin n → ℝ) (beta : ℝ),
    (∀ x ∈ DisjSet Vidx Ridx vpt rvec, beta ≤ dotProduct alpha x) ↔
      IsVPolyhedralValid Vidx Ridx vpt rvec alpha beta) := by
  intro H
  have key := (H (n := 1) (Q := Unit) VPolyCexCC.Vi VPolyCexCC.Ri
    (fun _ i => PEmpty.elim i) (fun _ _ => fun _ => 1) (fun _ => -1) 0).mp
    (fun x hx => absurd hx (VPolyCexCC.disj_empty _ _ x))
  have h2 := key.2 () ()
  simp [dotProduct] at h2
  linarith
