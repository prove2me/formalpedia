-- Prove2me | solution 1 for EdmondsMatching65.Polyhedron.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T10:10:46.349682+00:00
-- url     : https://prove2.me/submissions/8e196d7c-e4f5-4352-a588-4faecd665b0f

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_EdmondsMatching65_Polyhedron_MatchingPolyhedron
import Definitions.Def_EdmondsMatching65_Polyhedron_DualProgram

set_option autoImplicit false

open EdmondsMatching65.Polyhedron in
theorem EM65WD_lift_eq_sum {V : Type*} [Fintype V] [DecidableEq V] (y : V → ℝ)
    (s : Sym2 V) (hs : ¬ s.IsDiag) :
    Sym2.lift ⟨fun a b => y a + y b, fun a b => add_comm (y a) (y b)⟩ s =
      ∑ v ∈ Finset.univ.filter (fun v => v ∈ s), y v := by
  induction s using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa using hs
    have : Finset.univ.filter (fun v => v ∈ s(a, b)) = {a, b} := by
      ext v; simp
    rw [this, Finset.sum_pair hab]
    simp

open EdmondsMatching65.Polyhedron in
theorem EM65WD_ysum {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ) (y : V → ℝ) :
    ∑ e, x e * Sym2.lift ⟨fun a b => y a + y b, fun a b => add_comm (y a) (y b)⟩ (G.ends e) =
      ∑ v, y v * degSum G x v := by
  simp_rw [fun e => EM65WD_lift_eq_sum y (G.ends e) (G.loopless e), degSum,
    Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> ring

open EdmondsMatching65.Polyhedron in
theorem EM65WD_zsum {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ) (z : Finset V → ℝ) :
    ∑ e, x e * ∑ S ∈ oddSets.filter (fun S : Finset V => G.ends e ∈ S.sym2), z S =
      ∑ S ∈ (oddSets : Finset (Finset V)), z S * insideSum G x S := by
  simp_rw [insideSum, Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> ring

open EdmondsMatching65.Polyhedron in
theorem solution {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (c x : E → ℝ) (y : V → ℝ) (z : Finset V → ℝ)
    (hx : x ∈ matchingPolyhedron G) (hyz : DualFeasible G c y z) :
    W c x ≤ U y z := by
  obtain ⟨hx0, hdeg, hins⟩ := hx
  obtain ⟨hy0, hz0, hce⟩ := hyz
  have h1 : W c x ≤ ∑ e, x e * edgeDual G y z e := by
    unfold W
    refine Finset.sum_le_sum fun e _ => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hce e) (hx0 e)
  have h2 : ∑ e, x e * edgeDual G y z e =
      ∑ v, y v * degSum G x v + ∑ S ∈ (oddSets : Finset (Finset V)), z S * insideSum G x S := by
    simp only [edgeDual, mul_add, Finset.sum_add_distrib]
    rw [EM65WD_ysum, EM65WD_zsum]
  have h3 : ∑ v, y v * degSum G x v ≤ ∑ v, y v := by
    refine Finset.sum_le_sum fun v _ => ?_
    calc y v * degSum G x v ≤ y v * 1 := mul_le_mul_of_nonneg_left (hdeg v) (hy0 v)
      _ = y v := mul_one _
  have h4 : ∑ S ∈ (oddSets : Finset (Finset V)), z S * insideSum G x S ≤
      ∑ S ∈ (oddSets : Finset (Finset V)), rOf S * z S := by
    refine Finset.sum_le_sum fun S hS => ?_
    have hS' := hS
    simp only [oddSets, Finset.mem_filter, Finset.mem_univ, true_and] at hS'
    obtain ⟨r, hr, hc⟩ := hS'
    have hrof : rOf S = (r : ℝ) := by
      unfold rOf; rw [hc]; push_cast; ring
    rw [hrof, mul_comm (r : ℝ)]
    exact mul_le_mul_of_nonneg_left (hins S r hr hc) (hz0 S hS)
  unfold U
  linarith
