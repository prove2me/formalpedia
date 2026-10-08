-- Prove2me | solution 1 for EdmondsMatching65.Polyhedron.W_eq_U_of_compSlack
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:06:05.047671+00:00
-- url     : https://prove2.me/submissions/a2769632-0f05-4ae0-8353-b794bcf6f940

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_EdmondsMatching65_Polyhedron_MatchingPolyhedron
import Definitions.Def_EdmondsMatching65_Polyhedron_DualProgram

set_option autoImplicit false

open EdmondsMatching65.Polyhedron in
theorem EM65_8d78987d_lift_eq {V : Type*} [Fintype V] [DecidableEq V] (y : V → ℝ)
    (s : Sym2 V) (h : ¬ s.IsDiag) :
    Sym2.lift ⟨fun a b => y a + y b, fun a b => add_comm (y a) (y b)⟩ s =
      ∑ v, if v ∈ s then y v else 0 := by
  induction s using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa using h
    rw [← Finset.sum_filter]
    have : Finset.univ.filter (fun v => v ∈ s(a, b)) = {a, b} := by
      ext v; simp [Sym2.mem_iff]
    rw [this, Finset.sum_pair hab]
    simp

open EdmondsMatching65.Polyhedron in
theorem solution {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (c : E → ℝ) (M : Finset E) (y : V → ℝ)
    (z : Finset V → ℝ) (hM : IsMatching G M) (hyz : DualFeasible G c y z)
    (hcs : CompSlack G c M y z) :
    W c (incidence M) = U y z := by
  obtain ⟨hy0, hz0, hce⟩ := hyz
  obtain ⟨h8, h9, h10⟩ := hcs
  have hW : W c (incidence M) = ∑ e ∈ M, c e := by
    unfold W incidence
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    congr 1
    ext e; simp
  rw [hW, Finset.sum_congr rfl (fun e he => (h9 e he).symm)]
  unfold edgeDual U
  rw [Finset.sum_add_distrib]
  congr 1
  · -- vertex part
    rw [Finset.sum_congr rfl (fun e _ => EM65_8d78987d_lift_eq y (G.ends e) (G.loopless e))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases hv : ∃ e ∈ M, v ∈ G.ends e
    · obtain ⟨e0, he0, hve0⟩ := hv
      rw [Finset.sum_eq_single_of_mem e0 he0]
      · simp [hve0]
      · intro e he hne
        have : v ∉ G.ends e := hM e0 he0 e he (Ne.symm hne) v hve0
        simp [this]
    · push Not at hv
      rw [h8 v hv]
      simp
  · -- odd set part
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rcases (hz0 S hS).lt_or_eq with hpos | hzero
    · rw [h10 S hS hpos]
    · rw [← hzero]; simp
