-- Prove2me | solution 1 for CombOpt.Circulation.solution38_implies_Gale_conditions
-- status  : ACCEPTED   (prove)
-- author  : @0xbf
-- created : 2026-11-12T14:07:46.246618+00:00
-- url     : https://prove2.me/submissions/b48cb76b-c350-4bf0-abcb-72d9f2d80f71

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_CombOpt_Circulation_IsSolution38
import Definitions.Def_CombOpt_Circulation_delta

open CombOpt.Circulation

namespace CombOpt.Circulation

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

lemma sum_if_eq_mem (S : Finset V) (a : V) (c : ℝ) :
    (∑ v ∈ S, if a = v then c else 0) = if a ∈ S then c else 0 := by
  classical
  by_cases h : a ∈ S
  · rw [Finset.sum_eq_single a]
    · simp [h]
    · intro b hb hba
      simp [Ne.symm hba]
    · intro hn
      exact (hn h).elim
  · simp only [if_neg h]
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hab : a = b
    · exact (h (by simpa [hab] using hb)).elim
    · simp [hab]

lemma sum_filter_eq_if_mem (S : Finset V) (p : V → Prop) [DecidablePred p]
    (a : V) (ha : ∀ v, p v ↔ a = v) (c : ℝ) :
    (∑ v ∈ S.filter p, c) = if a ∈ S then c else 0 := by
  classical
  rw [Finset.sum_filter]
  simp_rw [ha]
  exact sum_if_eq_mem S a c

lemma sum_excess_on_set_eq_cut (G : MultiDigraph V E) (x : E → ℝ) (A : Finset V) :
    (∑ v ∈ A, excess G x v) = (∑ e ∈ delta G Aᶜ, x e) - (∑ e ∈ delta G A, x e) := by
  classical
  simp only [excess, Finset.sum_sub_distrib]
  have hIn : (∑ v ∈ A, ∑ e ∈ Finset.univ.filter (fun e => G.head e = v), x e) =
      ∑ e ∈ Finset.univ, if G.head e ∈ A then x e else 0 := by
    rw [Finset.sum_comm' (s := A)
      (t := fun v => Finset.univ.filter (fun e => G.head e = v))
      (t' := Finset.univ)
      (s' := fun e => A.filter (fun v => G.head e = v))]
    · apply Finset.sum_congr rfl
      intro e he
      exact sum_filter_eq_if_mem A (fun v => G.head e = v) (G.head e)
        (fun _ => Iff.rfl) (x e)
    · intro v e
      simp
  have hOut : (∑ v ∈ A, ∑ e ∈ Finset.univ.filter (fun e => G.tail e = v), x e) =
      ∑ e ∈ Finset.univ, if G.tail e ∈ A then x e else 0 := by
    rw [Finset.sum_comm' (s := A)
      (t := fun v => Finset.univ.filter (fun e => G.tail e = v))
      (t' := Finset.univ)
      (s' := fun e => A.filter (fun v => G.tail e = v))]
    · apply Finset.sum_congr rfl
      intro e he
      exact sum_filter_eq_if_mem A (fun v => G.tail e = v) (G.tail e)
        (fun _ => Iff.rfl) (x e)
    · intro v e
      simp
  rw [hIn, hOut]
  simp only [delta, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e he
  by_cases ht : G.tail e ∈ A <;> by_cases hh : G.head e ∈ A <;> simp [ht, hh]

theorem gale_conditions_of_solution38 (G : MultiDigraph V E) (u : E → ℝ)
    (b : V → ℝ) (x : E → ℝ) (hx : IsSolution38 G u b x) :
    (∑ v, b v = 0) ∧
      ∀ A : Finset V, ∑ v ∈ A, b v ≤ ∑ e ∈ delta G Aᶜ, u e := by
  classical
  rcases hx with ⟨hxb, hx_bounds⟩
  constructor
  · have htotal : (∑ v, excess G x v) = 0 := by
      have h := sum_excess_on_set_eq_cut G x Finset.univ
      simpa [delta] using h
    calc
      (∑ v, b v) = ∑ v, excess G x v := by
        apply Finset.sum_congr rfl
        intro v hv
        exact (hxb v).symm
      _ = 0 := htotal
  · intro A
    have hcut : (∑ v ∈ A, b v) =
        (∑ e ∈ delta G Aᶜ, x e) - (∑ e ∈ delta G A, x e) := by
      rw [← sum_excess_on_set_eq_cut]
      apply Finset.sum_congr rfl
      intro v hv
      exact (hxb v).symm
    have hnonneg : 0 ≤ ∑ e ∈ delta G A, x e :=
      Finset.sum_nonneg (fun e he => (hx_bounds e).1)
    have hcap : (∑ e ∈ delta G Aᶜ, x e) ≤ ∑ e ∈ delta G Aᶜ, u e :=
      Finset.sum_le_sum (fun e he => (hx_bounds e).2)
    rw [hcut]
    calc
      (∑ e ∈ delta G Aᶜ, x e) - (∑ e ∈ delta G A, x e) ≤
          ∑ e ∈ delta G Aᶜ, x e := sub_le_self _ hnonneg
      _ ≤ ∑ e ∈ delta G Aᶜ, u e := hcap

end CombOpt.Circulation

theorem solution {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : MultiDigraph V E) (u : E → ℝ) (b : V → ℝ) (x : E → ℝ)
    (hx : IsSolution38 G u b x) :
    (∑ v, b v = 0) ∧
      ∀ A : Finset V, ∑ v ∈ A, b v ≤ ∑ e ∈ delta G Aᶜ, u e := by
  exact CombOpt.Circulation.gale_conditions_of_solution38 G u b x hx
