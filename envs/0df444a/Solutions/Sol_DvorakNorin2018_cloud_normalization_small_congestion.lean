-- Prove2me | solution 1 for DvorakNorin2018.cloud_normalization_small_congestion
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T17:41:09.069431+00:00
-- url     : https://prove2.me/submissions/bb1fa84f-b6ab-4ce3-b162-28d36326b5e7

import Definitions.Def_DvorakNorin2018_CloudNormalization
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Classical BigOperators
namespace StableMSR.Recovery.TameCloud
lemma total_at_sinks {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W : Finset V} {α : ℝ} {p : Data V} (hp : Cloud G W α p) :
    total p = ∑ v ∈ W, congestion p v := by
  have hc : (∑ v ∈ Wᶜ, p.1 v) + (∑ v ∈ Wᶜ, incoming p v) =
      ∑ v ∈ Wᶜ, ∑ u, p.2 (v,u) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v hv => hp.conserve v (Finset.mem_compl.mp hv))
  have hz : (∑ v ∈ W, ∑ u, p.2 (v,u)) = 0 :=
    Finset.sum_eq_zero (fun v hv => Finset.sum_eq_zero (fun u _ => hp.sinks v hv u))
  have hall : (∑ v, incoming p v) = ∑ v, ∑ u, p.2 (v,u) := by
    unfold incoming; exact Finset.sum_comm
  have h₁ := Finset.sum_add_sum_compl W (fun v => p.1 v)
  have h₂ := Finset.sum_add_sum_compl W (incoming p)
  have h₃ := Finset.sum_add_sum_compl W (fun v => ∑ u, p.2 (v,u))
  unfold total congestion
  rw [Finset.sum_add_distrib]
  linarith

/- The whole α≤1 branch of Lemma 6, preserving the supply exactly. -/
theorem normalize_small_congestion {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : Data V) (hp : Cloud G W α p) :
    ∃ q : Data V, Cloud G W α q ∧ Tame W α q ∧ total q = total p := by
  classical
  let q : Data V := (fun v => if v ∈ W then congestion p v else 0, fun _ => 0)
  have hn : ∀ v, 0 ≤ congestion p v := fun v => add_nonneg (hp.supply v).1
    (Finset.sum_nonneg (fun u _ => hp.flow (u,v)))
  have hqc : ∀ v, congestion q v = if v ∈ W then congestion p v else 0 := by
    intro v; simp [congestion,incoming,q]
  have hcloud : Cloud G W α q := by
    refine ⟨?_,fun _ => le_rfl,fun _ _ _ => rfl,fun _ _ _ => rfl,?_,?_⟩
    · intro v
      change 0 ≤ (if v ∈ W then congestion p v else 0) ∧
        (if v ∈ W then congestion p v else 0) ≤ 1
      by_cases hv : v ∈ W <;> simp only [hv,ite_true,ite_false]
      · exact ⟨hn v,(hp.bound v).trans hα1⟩
      · exact ⟨le_rfl,zero_le_one⟩
    · intro v hv; simp [hqc,hv,q]
    · intro v; rw [hqc]; split_ifs
      · exact hp.bound v
      · exact hα
  refine ⟨q,hcloud,?_,?_⟩
  · refine ⟨fun _ _ _ => rfl,?_,?_⟩
    · intro z _ u v _ _ hpos _; exact False.elim ((lt_irrefl 0) hpos)
    · intro _
      refine ⟨fun _ => rfl,?_⟩
      intro v
      by_cases hv : v ∈ W
      · simp only [hv,iff_true]
        by_cases hsat : q.1 v = 1
        · exact Or.inl hsat
        · exact Or.inr ⟨lt_of_le_of_ne (hcloud.supply v).2 hsat,Or.inr hv⟩
      · have hg : q.1 v = 0 := by simp [q,hv]
        simp [Hungry,hg,hqc,hv]
  · unfold total
    simp only [q]
    rw [← Finset.sum_filter]
    have hf : (Finset.univ.filter (fun v => v ∈ W)) = W := by ext v; simp
    rw [hf]
    exact (total_at_sinks hp).symm

end StableMSR.Recovery.TameCloud
open StableMSR.Recovery.TameCloud

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : Data V) (hp : Cloud G W α p) :
    ∃ q : Data V, Cloud G W α q ∧ Tame W α q ∧ total q = total p := by
  exact normalize_small_congestion G W α hα hα1 p hp
