-- Prove2me | solution 1 for Disjunctive.NormalForms.basic_step_dnf
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T00:34:39.072892+00:00
-- url     : https://prove2.me/submissions/a4b62801-f7d1-4c1d-aded-dbbc3c1c5990

import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

open Disjunctive.NormalForms in
theorem solution {n : ℕ} {Qk Ql : Type*} [Fintype Qk] [Fintype Ql] (mk : Qk → ℕ)
    (Ak : (i : Qk) → Matrix (Fin (mk i)) (Fin n) ℝ) (bk : (i : Qk) → Fin (mk i) → ℝ)
    (ml : Ql → ℕ) (Al : (j : Ql) → Matrix (Fin (ml j)) (Fin n) ℝ) (bl : (j : Ql) → Fin (ml j) → ℝ) :
    (⋃ i : Qk, Poly (Ak i) (bk i)) ∩ (⋃ j : Ql, Poly (Al j) (bl j)) =
      ⋃ p : Qk × Ql, Poly (Ak p.1) (bk p.1) ∩ Poly (Al p.2) (bl p.2) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Prod.exists]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨i, j, hi, hj⟩
  · rintro ⟨i, j, hi, hj⟩
    exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
