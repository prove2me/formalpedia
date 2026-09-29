-- Prove2me | solution 1 for CalibratedCE.Generic.example_CE_not_limit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:57:39.553033+00:00
-- url     : https://prove2.me/submissions/2dcb6f95-66e8-41c8-9934-f8f29dc73c0a

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Generic_LimitSet
import Definitions.Def_CalibratedCE_Generic_Example

namespace CalibratedCE.Generic

open Filter Topology

theorem aux_exCE_u1_col0 (x : Fin 3) : exU₁ x 0 = 2 := by
  fin_cases x <;> simp [exU₁]

theorem aux_exCE_u2_sum (c : Fin 3) : exU₂ 0 c + exU₂ 1 c = 4 := by
  fin_cases c <;> simp [exU₂] <;> norm_num

theorem aux_exCE_mem : exD₀ ∈ CESet exU₁ exU₂ := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro a b
    unfold exD₀
    split_ifs <;> norm_num
  · simp [Fin.sum_univ_three, exD₀]
    norm_num
  · intro Φ
    simp only [Fin.sum_univ_three, exD₀]
    simp [aux_exCE_u1_col0]
  · intro Φ
    simp only [Fin.sum_univ_three, exD₀]
    have h1 := aux_exCE_u2_sum (Φ 0)
    have h2 := aux_exCE_u2_sum 0
    simp
    linarith

theorem aux_exCE_forecast {p : Fin 3 → ℝ} (hp : IsDist p) {R₁ : (Fin 3 → ℝ) → Fin 3}
    (hR₁ : IsBestReply₁ exU₁ R₁) (h2 : R₁ p ≠ 2) : p = ![1, 0, 0] := by
  have h := hR₁ p hp 2
  obtain ⟨hnn, hsum⟩ := hp
  have hsum' := hsum
  simp only [Fin.sum_univ_three] at h hsum'
  have e : exU₁ (R₁ p) 1 = 0 ∧ exU₁ (R₁ p) 2 = 0 := by
    generalize R₁ p = a at h2
    fin_cases a <;> simp_all [exU₁]
  rw [aux_exCE_u1_col0 (R₁ p), e.1, e.2] at h
  simp [exU₁] at h
  have h0 := hnn 0
  have h1 := hnn 1
  have h2' := hnn 2
  have hp1 : p 1 = 0 := by linarith
  have hp2 : p 2 = 0 := by linarith
  have hp0 : p 0 = 1 := by linarith
  funext i
  fin_cases i <;> simp [hp0, hp1, hp2]

theorem aux_exCE_empDist_zero {x : ℕ → Fin 3} {y : ℕ → Fin 3} {a : Fin 3} (b : Fin 3)
    (hx : ∀ s, x s ≠ a) (t : ℕ) : empDist x y t a b = 0 := by
  unfold empDist
  have : (Finset.range t).filter (fun s => x s = a ∧ y s = b) = ∅ := by
    apply Finset.filter_false_of_mem
    intro s _ hs
    exact hx s hs.1
  simp [this]

theorem aux_exCE_not_limit : exD₀ ∉ LimitSet exU₁ exU₂ := by
  rintro ⟨R₁, R₂, π₁, π₂, hR₁, hR₂, hπ₁, hπ₂, hc₁, hc₂, hlim⟩
  have key : ∀ t, play₁ R₁ R₂ π₁ π₂ t ≠ 2 → play₁ R₁ R₂ π₁ π₂ t = R₁ ![1, 0, 0] := by
    intro t ht
    have hf : forecast₁ R₁ R₂ π₁ π₂ t = ![1, 0, 0] :=
      aux_exCE_forecast (hπ₁ _) hR₁ ht
    unfold play₁ at ht ⊢
    rw [hf]
  have lim0 : ∀ a b, (∀ s, play₁ R₁ R₂ π₁ π₂ s ≠ a) → exD₀ a b = 0 := by
    intro a b hx
    have hfun : (fun t => empDist (play₁ R₁ R₂ π₁ π₂) (play₂ R₁ R₂ π₁ π₂) t a b)
        = fun _ => (0 : ℝ) := funext (aux_exCE_empDist_zero b hx)
    have := hlim a b
    rw [hfun] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  by_cases ha : R₁ ![1, 0, 0] = 0
  · have hx : ∀ s, play₁ R₁ R₂ π₁ π₂ s ≠ 1 := by
      intro s hs
      have := key s (by rw [hs]; decide)
      rw [hs, ha] at this
      exact absurd this (by decide)
    have := lim0 1 0 hx
    simp [exD₀] at this
  · have hx : ∀ s, play₁ R₁ R₂ π₁ π₂ s ≠ 0 := by
      intro s hs
      have := key s (by rw [hs]; decide)
      rw [hs] at this
      exact ha this.symm
    have := lim0 0 0 hx
    simp [exD₀] at this

end CalibratedCE.Generic

open CalibratedCE.Generic

theorem solution :
    exD₀ ∈ CESet exU₁ exU₂ ∧ exD₀ ∉ LimitSet exU₁ exU₂ :=
  ⟨aux_exCE_mem, aux_exCE_not_limit⟩
