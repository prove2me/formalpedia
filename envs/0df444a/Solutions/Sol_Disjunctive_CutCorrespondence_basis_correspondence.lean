-- Prove2me | solution 1 for Disjunctive.CutCorrespondence.basis_correspondence
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T00:11:36.329163+00:00
-- url     : https://prove2.me/submissions/603cb2af-300d-4944-9360-092111aa8914

import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau

set_option autoImplicit false

namespace CexD1a07b02
open Disjunctive.CutCorrespondence

/-- One row `x ≥ 1/2` in `n = 1`. -/
def A : Matrix Unit (Fin 1) ℝ := fun _ _ => 1
noncomputable def b : Unit → ℝ := fun _ => 1 / 2

theorem feas_v0 (α : Fin 1 → ℝ) (u : Unit → ℝ) (u0 : ℝ) (v : Unit → ℝ) (v0 : ℝ) (β : ℝ)
    (h : IsCGLPKFeasible A b 0 α u u0 v v0 β) (hv : v () = 0) :
    (α, u, u0, v, v0, β) =
      ((fun _ => (1/4 : ℝ)), (fun _ => (1/2 : ℝ)), (1/4 : ℝ), (fun _ => (0 : ℝ)), (1/4 : ℝ),
        (1/4 : ℝ)) := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, -⟩ := h
  have e1 := h1 0
  have e2 := h2 0
  simp only [A, b, Finset.univ_unique, Finset.sum_singleton, if_true, mul_one,
    PUnit.default_eq_unit] at e1 e2 h3 h4 h5
  rw [hv] at e2 h4 h5
  have hv0 : v0 = 1/4 := by linarith
  have hu0 : u0 = 1/4 := by linarith
  have hu : u () = 1/2 := by linarith
  have hα : α 0 = 1/4 := by linarith
  have hβ : β = 1/4 := by linarith
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))))
  · funext i; fin_cases i; simpa using hα
  · funext i; simpa using hu
  · simpa using hu0
  · funext i; simpa using hv
  · simpa using hv0
  · simpa using hβ

theorem basic : IsBasicCGLPKSolution A b 0 (fun _ => (1/4 : ℝ)) (fun _ => (1/2 : ℝ)) (1/4 : ℝ)
    (fun _ => (0 : ℝ)) (1/4 : ℝ) (1/4 : ℝ) := by
  unfold IsBasicCGLPKSolution
  rw [mem_extremePoints]
  refine ⟨?_, ?_⟩
  · show IsCGLPKFeasible A b 0 _ _ _ _ _ _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i; simp [A]; norm_num
    · intro i; fin_cases i; simp [A]
    · simp [b]; norm_num
    · simp [b]
    · simp; norm_num
    · intro i; simp
    · intro i; simp
    · norm_num
    · norm_num
  · rintro ⟨α1, u1, u01, v1, v01, β1⟩ hx1 ⟨α2, u2, u02, v2, v02, β2⟩ hx2 ⟨a, c, ha, hc, hac, hseg⟩
    have hf1 : IsCGLPKFeasible A b 0 α1 u1 u01 v1 v01 β1 := hx1
    have hf2 : IsCGLPKFeasible A b 0 α2 u2 u02 v2 v02 β2 := hx2
    have hv := congrArg (fun w => w.2.2.2.1 ()) hseg
    simp only [Prod.smul_mk, Prod.mk_add_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hv
    have p1 : 0 ≤ v1 () := hf1.2.2.2.2.2.2.1 ()
    have p2 : 0 ≤ v2 () := hf2.2.2.2.2.2.2.1 ()
    have q1 : 0 ≤ a * v1 () := mul_nonneg ha.le p1
    have q2 : 0 ≤ c * v2 () := mul_nonneg hc.le p2
    have z1 : v1 () = 0 := by
      have : a * v1 () = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact h
    have z2 : v2 () = 0 := by
      have : c * v2 () = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact h
    exact ⟨feas_v0 _ _ _ _ _ _ hf1 z1, feas_v0 _ _ _ _ _ _ hf2 z2⟩

theorem cex : ¬ (∀ {n : ℕ} {M : Type} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (M1 M2 : Finset M)
    (hbasic : IsBasicCGLPKSolution Atil btil k α u u0 v v0 β) (hu0 : 0 < u0) (hv0 : 0 < v0)
    (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0),
    Disjoint M1 M2 ∧ IsNonsingularSubmatrix Atil (M1 ∪ M2)) := by
  intro h
  have := (h A b 0 _ _ _ _ _ _ Finset.univ Finset.univ basic (by norm_num) (by norm_num)
    (fun ρ hρ => absurd (Finset.mem_univ ρ) hρ) (fun ρ hρ => absurd (Finset.mem_univ ρ) hρ)).1
  rw [disjoint_self, Finset.bot_eq_empty] at this
  exact absurd (this ▸ Finset.mem_univ ()) (Finset.notMem_empty ())

end CexD1a07b02

open Disjunctive.CutCorrespondence in
theorem solution : ¬ (∀ {n : ℕ} {M : Type} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (M1 M2 : Finset M)
    (hbasic : IsBasicCGLPKSolution Atil btil k α u u0 v v0 β) (hu0 : 0 < u0) (hv0 : 0 < v0)
    (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0),
    Disjoint M1 M2 ∧ IsNonsingularSubmatrix Atil (M1 ∪ M2)) := by
  exact CexD1a07b02.cex
