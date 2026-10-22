-- Prove2me | solution 1 for FlowsNetworks.DynamicFlow.chain_length_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:27:42.11186+00:00
-- url     : https://prove2.me/submissions/43eb244e-2ed7-48af-9eb5-58311c9ee658

import Mathlib
import Definitions.Def_FlowsNetworks_DynamicFlow_Network

open FlowsNetworks.DynamicFlow

theorem g70fn2_cs_cons {N : Type} (g : N → N → ℤ) (a b : N) (rest : List N) :
    chainSum g (a :: b :: rest) = g a b + chainSum g (b :: rest) := by
  simp [chainSum]

theorem g70fn2_cs_le {N : Type} (g h : N → N → ℤ) :
    ∀ l : List N, (∀ (i : ℕ) (hi : i + 1 < l.length), g l[i] l[i + 1] ≤ h l[i] l[i + 1]) →
      chainSum g l ≤ chainSum h l
  | [], _ => by simp [chainSum]
  | [a], _ => by simp [chainSum]
  | a :: b :: rest, H => by
    rw [g70fn2_cs_cons, g70fn2_cs_cons]
    have h0 := H 0 (by simp)
    have ih := g70fn2_cs_le g h (b :: rest) (fun i hi => by
      have := H (i + 1) (by simp at hi ⊢; omega)
      simpa using this)
    simp at h0
    omega

theorem g70fn2_cs_tele {N : Type} (φ : N → ℤ) :
    ∀ (l : List N) (a b : N), l.head? = some a → l.getLast? = some b →
      chainSum (fun x y => φ y - φ x) l = φ b - φ a
  | [], _, _, h, _ => by simp at h
  | [x], a, b, h1, h2 => by
    simp at h1 h2; subst h1; subst h2; simp [chainSum]
  | x :: y :: rest, a, b, h1, h2 => by
    rw [g70fn2_cs_cons]
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    have h2' : (y :: rest).getLast? = some b := by
      rw [List.getLast?_cons_cons] at h2; exact h2
    rw [g70fn2_cs_tele φ (y :: rest) y b rfl h2']
    ring

theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t) (p : ℕ)
    (f : N → N → ℝ) (v : ℝ) (hf : IsStaticFlow G s t f v) (hint : IsIntegral f)
    (π : N → ℤ) (hπ : OptimalityProperties G s t p f π)
    (l : List N) (hl : IsChainFromTo G s t l) :
    (p : ℤ) ≤ chainSum (fun x y => (G.cost x y : ℤ) + arcNumber G π x y) l ∧
    ((∀ (i : ℕ) (h : i + 1 < l.length), 0 < f l[i] l[i + 1]) →
      chainSum (fun x y => (G.cost x y : ℤ) + arcNumber G π x y) l = (p : ℤ)) ∧
    (1 ≤ p → ∀ π' : N → ℤ, OptimalityProperties G s t (p - 1) f π' →
      (∀ (i : ℕ) (h : i + 1 < l.length), 0 < f l[i] l[i + 1]) →
      ∃ (i : ℕ) (h : i + 1 < l.length), 0 < arcNumber G π l[i] l[i + 1]) := by
  obtain ⟨hlen, -, hhead, hlast, harcs⟩ := hl
  -- generic facts for any optimal potential
  have lower : ∀ (ρ : N → ℤ) (q : ℕ), OptimalityProperties G s t q f ρ →
      (q : ℤ) ≤ chainSum (fun x y => (G.cost x y : ℤ) + arcNumber G ρ x y) l := by
    rintro ρ q ⟨h0, h1, -⟩
    have := g70fn2_cs_tele ρ l s t hhead hlast
    rw [h0, h1, sub_zero] at this
    rw [← this]
    apply g70fn2_cs_le
    intro i hi
    unfold arcNumber
    have := le_max_right 0 (ρ l[i + 1] - ρ l[i] - (G.cost l[i] l[i + 1] : ℤ))
    linarith
  have hexa : ∀ (ρ : N → ℤ) (q : ℕ), OptimalityProperties G s t q f ρ →
      (∀ (i : ℕ) (h : i + 1 < l.length), 0 < f l[i] l[i + 1]) →
      chainSum (fun x y => (G.cost x y : ℤ) + arcNumber G ρ x y) l = (q : ℤ) := by
    intro ρ q hρ hpos
    obtain ⟨h0, h1, hopt⟩ := hρ
    have := g70fn2_cs_tele ρ l s t hhead hlast
    rw [h0, h1, sub_zero] at this
    rw [← this]
    apply le_antisymm
    · apply g70fn2_cs_le
      intro i hi
      have hq := (hopt _ (harcs i hi)).1
      have hnot : ¬ (ρ l[i + 1] - ρ l[i] < (G.cost l[i] l[i + 1] : ℤ)) := by
        intro hlt; have := hq hlt; have := hpos i hi; simp only at *; linarith
      unfold arcNumber
      rw [max_eq_right (by omega)]
      omega
    · exact (this ▸ lower ρ q ⟨h0, h1, hopt⟩ : _)
  refine ⟨lower π p hπ, hexa π p hπ, ?_⟩
  intro hp π' hπ' hpos
  by_contra hcon
  push_neg at hcon
  have e1 := hexa π p hπ hpos
  have e2 := hexa π' (p - 1) hπ' hpos
  have e3 : chainSum (fun x y => (G.cost x y : ℤ) + arcNumber G π x y) l ≤
      chainSum (fun x y => (G.cost x y : ℤ) + arcNumber G π' x y) l := by
    apply g70fn2_cs_le
    intro i hi
    have := hcon i hi
    have h2 : 0 ≤ arcNumber G π' l[i] l[i + 1] := le_max_left _ _
    linarith
  rw [e1, e2] at e3
  omega
