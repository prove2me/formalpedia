-- Prove2me | solution 1 for Disjunctive.VPolyhedral.general_v_polyhedral_validity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T01:31:36.397478+00:00
-- url     : https://prove2.me/submissions/857f15eb-8518-4f6c-be3f-c742ac18a03b

import Mathlib
import Definitions.Def_Disjunctive_VPolyhedral_Basic

set_option autoImplicit false

namespace Disjunctive.VPolyhedral

theorem general_v_polyhedral_validity_aux {n : ℕ} {Q : Type*} (Vidx Ridx : Q → Type*)
    [∀ h, Fintype (Vidx h)] [∀ h, Fintype (Ridx h)] (vpt : ∀ h, Vidx h → Fin n → ℝ)
    (rvec : ∀ h, Ridx h → Fin n → ℝ) (PI : Set (Fin n → ℝ))
    (hPI_sub : PI ⊆ CombinedC Vidx Ridx vpt rvec)
    (alpha : Fin n → ℝ) (beta : ℝ) (hvalid : IsVPolyhedralValid Vidx Ridx vpt rvec alpha beta) :
    ∀ x ∈ PI, beta ≤ dotProduct alpha x := by
  intro x hx
  obtain ⟨p, hp, r, hr, rfl⟩ := hPI_sub hx
  have hlin : IsLinearMap ℝ (fun y : Fin n → ℝ => dotProduct alpha y) :=
    ⟨fun a b => dotProduct_add alpha a b, fun c a => dotProduct_smul c alpha a⟩
  have hconv : Convex ℝ {y : Fin n → ℝ | beta ≤ dotProduct alpha y} :=
    convex_halfSpace_ge hlin beta
  have hsub : (⋃ h, Set.range (vpt h)) ⊆ {y : Fin n → ℝ | beta ≤ dotProduct alpha y} := by
    intro y hy
    simp only [Set.mem_iUnion, Set.mem_range] at hy
    obtain ⟨h, i, rfl⟩ := hy
    exact hvalid.1 h i
  have hp' : beta ≤ dotProduct alpha p := convexHull_min hsub hconv hp
  obtain ⟨k, c, v, hc, hv, rfl⟩ := hr
  have hr' : 0 ≤ dotProduct alpha (∑ i, c i • v i) := by
    rw [dotProduct_sum]
    apply Finset.sum_nonneg
    intro i _
    rw [dotProduct_smul, smul_eq_mul]
    apply mul_nonneg (hc i)
    have := hv i
    simp only [Set.mem_iUnion, Set.mem_range] at this
    obtain ⟨h, j, hj⟩ := this
    rw [← hj]
    exact hvalid.2 h j
  rw [dotProduct_add]
  linarith

end Disjunctive.VPolyhedral

open Disjunctive.VPolyhedral in
theorem solution {n : ℕ} {Q : Type*} (Vidx Ridx : Q → Type*)
    [∀ h, Fintype (Vidx h)] [∀ h, Fintype (Ridx h)] (vpt : ∀ h, Vidx h → Fin n → ℝ)
    (rvec : ∀ h, Ridx h → Fin n → ℝ) (PI : Set (Fin n → ℝ))
    (hPI_sub : PI ⊆ CombinedC Vidx Ridx vpt rvec)
    (alpha : Fin n → ℝ) (beta : ℝ) (hvalid : IsVPolyhedralValid Vidx Ridx vpt rvec alpha beta) :
    ∀ x ∈ PI, beta ≤ dotProduct alpha x := by
  exact general_v_polyhedral_validity_aux Vidx Ridx vpt rvec PI hPI_sub alpha beta hvalid
