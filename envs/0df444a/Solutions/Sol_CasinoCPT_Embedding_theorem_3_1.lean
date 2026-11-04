-- Prove2me | solution 1 for CasinoCPT.Embedding.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T06:51:18.468563+00:00
-- url     : https://prove2.me/submissions/b2694beb-c780-4c69-91e6-a2f0a5bee53f

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model
import Theorems.Thm_CasinoCPT_Embedding_proposition_A_3
import Theorems.Thm_CasinoCPT_Embedding_cond8_iff_evol_eq_potential

open MeasureTheory ProbabilityTheory CasinoCPT.Embedding

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℕ mΩ) (S : ℕ → Ω → ℤ) (ξ : Ω → ℝ) (hS : IsCasinoSpace P F S ξ)
    (T : ℕ) (hT : 1 ≤ T) (μ : Measure ℤ) (hμ : InP0Z μ)
    (hsupp : μ (Set.Icc (-(T : ℤ)) T) = 1) :
    ((∃ τ : Ω → ℕ∞, IsAdmissible F T τ ∧ P.map (stoppedValue S τ) = μ) ↔ Cond8 μ T) ∧
      (Cond8 μ T → ∃ (b : ℤ → ℕ) (r : ℤ → ℝ) (coin : ℕ → ℤ → Ω → Bool),
        IsRootBarrier b r ∧ IsRootCoins P F b r coin ∧
          IsAdmissible F T (rootTime S b coin) ∧
          P.map (stoppedValue S (rootTime S b coin)) = μ) := by
  have hA := (proposition_A_3 P F S ξ hS T hT μ hμ hsupp).1
  have hC := cond8_iff_evol_eq_potential T hT μ hμ hsupp
  have h13 : (∀ x : ℤ, evol μ T x = potential μ (x : ℝ)) ↔
      ∃ τ : Ω → ℕ∞, IsAdmissible F T τ ∧ P.map (stoppedValue S τ) = μ :=
    hA.out 0 2
  have h12 := hA.out 0 1
  refine ⟨h13.symm.trans hC.symm, fun h8 => ?_⟩
  obtain ⟨b, r, coin, hb, hc, hst, hle, -, hlaw⟩ := h12.mp (hC.mp h8)
  exact ⟨b, r, coin, hb, hc, ⟨hst, hle⟩, hlaw⟩
