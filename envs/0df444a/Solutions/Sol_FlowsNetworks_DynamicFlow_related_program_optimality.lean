-- Prove2me | solution 1 for FlowsNetworks.DynamicFlow.related_program_optimality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:24:11.109658+00:00
-- url     : https://prove2.me/submissions/97440d7f-db9d-4578-ad9f-4ab370ca29e2

import Mathlib
import Definitions.Def_FlowsNetworks_DynamicFlow_Network

open FlowsNetworks.DynamicFlow

theorem g70fn2_pot {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (f : N → N → ℝ)
    (π : N → ℝ) :
    ∑ x, π x * netOut G f x = ∑ q ∈ G.arcs, f q.1 q.2 * (π q.1 - π q.2) := by
  unfold netOut arcSum
  have h1 : ∀ x, G.arcs.filter (fun q => q.1 ∈ ({x} : Finset N) ∧ q.2 ∈ Finset.univ)
      = G.arcs.filter (fun q => q.1 = x) := fun x => by
    ext q; simp
  have h2 : ∀ x, G.arcs.filter (fun q => q.1 ∈ (Finset.univ : Finset N) ∧ q.2 ∈ ({x} : Finset N))
      = G.arcs.filter (fun q => q.2 = x) := fun x => by
    ext q; simp
  simp only [h1, h2, Finset.sum_filter, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1 <;> exact Finset.sum_congr rfl fun q _ => by ring

theorem g70fn2_flowpot {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (s t : N)
    (hst : s ≠ t) (f : N → N → ℝ) (v : ℝ) (hf : IsStaticFlow G s t f v) (π : N → ℝ) :
    ∑ q ∈ G.arcs, f q.1 q.2 * (π q.2 - π q.1) = (π t - π s) * v := by
  obtain ⟨-, -, h1, h2, h3⟩ := hf
  have := g70fn2_pot G f π
  have e : ∑ x, π x * netOut G f x =
      ∑ x, ((if x = s then π s * v else 0) + (if x = t then -(π t * v) else 0)) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hs : x = s
    · subst hs; simp [h1, hst]
    · by_cases ht : x = t
      · subst ht; simp [h3, hs]
      · simp [h2 x hs ht, hs, ht]
  rw [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq'] at this
  simp only [Finset.mem_univ, if_true] at this
  have h4 : ∑ q ∈ G.arcs, f q.1 q.2 * (π q.2 - π q.1) =
      -∑ q ∈ G.arcs, f q.1 q.2 * (π q.1 - π q.2) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun q _ => by ring
  rw [h4, ← this]; ring

theorem g70fn2_rpo {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t) (p : ℕ)
    (f : N → N → ℝ) (v : ℝ) (hf : IsStaticFlow G s t f v)
    (π : N → ℤ) (hπ : OptimalityProperties G s t p f π) :
    (∀ (f' : N → N → ℝ) (v' : ℝ), IsStaticFlow G s t f' v' →
        (p : ℝ) * v' - totalCost G f' ≤ (p : ℝ) * v - totalCost G f) ∧
    IsDualFeasible G s t p (fun x => (π x : ℝ)) (fun x y => (arcNumber G π x y : ℝ)) ∧
    (∀ (π' : N → ℝ) (γ' : N → N → ℝ), IsDualFeasible G s t p π' γ' →
        dualObjective G (fun x y => (arcNumber G π x y : ℝ)) ≤ dualObjective G γ') ∧
    (p : ℝ) * v - totalCost G f = dualObjective G (fun x y => (arcNumber G π x y : ℝ)) := by
  obtain ⟨hs0, htp, hopt⟩ := hπ
  set πr : N → ℝ := fun x => (π x : ℝ)
  set γ : N → N → ℝ := fun x y => (arcNumber G π x y : ℝ)
  have hγ : ∀ x y, γ x y = max 0 (πr y - πr x - (G.cost x y : ℝ)) := by
    intro x y; simp only [γ, πr, arcNumber]; push_cast; rfl
  -- value identity
  have hval : ∀ f' v', IsStaticFlow G s t f' v' →
      (p : ℝ) * v' - totalCost G f' =
        ∑ q ∈ G.arcs, f' q.1 q.2 * (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ)) := by
    intro f' v' hf'
    have := g70fn2_flowpot G s t hst f' v' hf' πr
    have e2 : ∑ q ∈ G.arcs, f' q.1 q.2 * (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ)) =
        ∑ q ∈ G.arcs, f' q.1 q.2 * (πr q.2 - πr q.1) -
          ∑ q ∈ G.arcs, (G.cost q.1 q.2 : ℝ) * f' q.1 q.2 := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun q _ => by ring
    rw [e2, this]
    unfold totalCost
    simp only [πr, hs0, htp]
    push_cast; ring
  have hcs : ∑ q ∈ G.arcs, f q.1 q.2 * (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ)) =
      dualObjective G γ := by
    unfold dualObjective
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨o1, o2⟩ := hopt q hq
    rw [hγ]
    simp only [πr]
    rcases lt_trichotomy (π q.2 - π q.1) (G.cost q.1 q.2 : ℤ) with h | h | h
    · have hd : ((π q.2 : ℝ) - π q.1 - (G.cost q.1 q.2 : ℝ)) < 0 := by
        have : ((π q.2 - π q.1 : ℤ) : ℝ) < ((G.cost q.1 q.2 : ℤ) : ℝ) := by exact_mod_cast h
        push_cast at this; linarith
      rw [o1 h, max_eq_left hd.le]; ring
    · have hd : ((π q.2 : ℝ) - π q.1 - (G.cost q.1 q.2 : ℝ)) = 0 := by
        have : ((π q.2 - π q.1 : ℤ) : ℝ) = ((G.cost q.1 q.2 : ℤ) : ℝ) := by exact_mod_cast h
        push_cast at this; linarith
      rw [hd]; simp
    · have hd : 0 < ((π q.2 : ℝ) - π q.1 - (G.cost q.1 q.2 : ℝ)) := by
        have : ((G.cost q.1 q.2 : ℤ) : ℝ) < ((π q.2 - π q.1 : ℤ) : ℝ) := by exact_mod_cast h
        push_cast at this; linarith
      rw [o2 h, max_eq_right hd.le]
  have heq : (p : ℝ) * v - totalCost G f = dualObjective G γ := by rw [hval f v hf, hcs]
  refine ⟨?_, ?_, ?_, heq⟩
  · intro f' v' hf'
    rw [heq, hval f' v' hf']
    unfold dualObjective
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨-, hb, -⟩ := hf'
    obtain ⟨n1, n2⟩ := hb q hq
    rw [hγ]
    have g0 : 0 ≤ max 0 (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ)) := le_max_left _ _
    have g1 : πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ) ≤ max 0 (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ)) :=
      le_max_right _ _
    calc f' q.1 q.2 * (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ))
        ≤ f' q.1 q.2 * max 0 (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ)) :=
          mul_le_mul_of_nonneg_left g1 n1
      _ ≤ (G.cap q.1 q.2 : ℝ) * max 0 (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ)) :=
          mul_le_mul_of_nonneg_right n2 g0
  · refine ⟨?_, fun q _ => ⟨?_, ?_⟩⟩
    · show -((π s : ℤ) : ℝ) + ((π t : ℤ) : ℝ) = (p : ℝ)
      rw [hs0, htp]; push_cast; ring
    · have := hγ q.1 q.2
      have g1 := le_max_right 0 (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ))
      simp only [γ, πr] at this g1 ⊢
      linarith
    · show (0:ℝ) ≤ (arcNumber G π q.1 q.2 : ℝ)
      unfold arcNumber; exact_mod_cast le_max_left _ _
  · intro π' γ' ⟨hp', hfe⟩
    rw [← heq, hval f v hf]
    have := g70fn2_flowpot G s t hst f v hf π'
    have hv2 : ∑ q ∈ G.arcs, f q.1 q.2 * (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ)) =
        ∑ q ∈ G.arcs, f q.1 q.2 * (π' q.2 - π' q.1 - (G.cost q.1 q.2 : ℝ)) := by
      have e1 := g70fn2_flowpot G s t hst f v hf πr
      have k : (πr t - πr s) = π' t - π' s := by simp only [πr, hs0, htp]; push_cast; linarith
      have d1 : ∀ ρ : N → ℝ, ∑ q ∈ G.arcs, f q.1 q.2 * (ρ q.2 - ρ q.1 - (G.cost q.1 q.2 : ℝ)) =
          ∑ q ∈ G.arcs, f q.1 q.2 * (ρ q.2 - ρ q.1) -
            ∑ q ∈ G.arcs, f q.1 q.2 * (G.cost q.1 q.2 : ℝ) := fun ρ => by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun q _ => by ring
      rw [d1, d1, e1, this, k]
    rw [hv2]
    unfold dualObjective
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨-, hb, -⟩ := hf
    obtain ⟨n1, n2⟩ := hb q hq
    obtain ⟨d1, d2⟩ := hfe q hq
    calc f q.1 q.2 * (π' q.2 - π' q.1 - (G.cost q.1 q.2 : ℝ)) ≤ f q.1 q.2 * γ' q.1 q.2 :=
          mul_le_mul_of_nonneg_left (by linarith) n1
      _ ≤ (G.cap q.1 q.2 : ℝ) * γ' q.1 q.2 := mul_le_mul_of_nonneg_right n2 d2

theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t) (p : ℕ)
    (f : N → N → ℝ) (v : ℝ) (hf : IsStaticFlow G s t f v) (hint : IsIntegral f)
    (π : N → ℤ) (hπ : OptimalityProperties G s t p f π) :
    (∀ (f' : N → N → ℝ) (v' : ℝ), IsStaticFlow G s t f' v' →
        (p : ℝ) * v' - totalCost G f' ≤ (p : ℝ) * v - totalCost G f) ∧
    IsDualFeasible G s t p (fun x => (π x : ℝ)) (fun x y => (arcNumber G π x y : ℝ)) ∧
    (∀ (π' : N → ℝ) (γ' : N → N → ℝ), IsDualFeasible G s t p π' γ' →
        dualObjective G (fun x y => (arcNumber G π x y : ℝ)) ≤ dualObjective G γ') ∧
    (p : ℝ) * v - totalCost G f = dualObjective G (fun x y => (arcNumber G π x y : ℝ)) :=
  g70fn2_rpo G s t hst p f v hf π hπ
