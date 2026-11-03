-- Prove2me | solution 1 for CompoundSMM.Conv.descent_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:40:36.341548+00:00
-- url     : https://prove2.me/submissions/34c077e6-d0ad-42da-9204-a2d61441e9d7

import Mathlib
import Definitions.Def_CompoundSMM_Conv_Setting
open CompoundSMM.Conv

theorem solution {n ℓG ℓF ℓφ : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : CompoundSP n ℓG ℓF ℓφ Ξ) (𝒢 : E n → Ξ → Set (E n → E ℓG))
    (ℱ : E n → Ξ → Set (E n → E ℓF)) (Lψ Lφ : ℝ) (hA2 : A2 P Lψ Lφ)
    (hA3G : SurrogateFamily P.X P.μ P.G 𝒢) (hA3F : SurrogateFamily P.X P.μ P.F ℱ)
    (ρ : ℝ) (hρ : 0 < ρ) (N : ℕ) (hN : 0 < N) (ξs ηs : ℕ → Ξ) (x' : E n) (hx' : x' ∈ P.X)
    (gs : ℕ → E n → E ℓG) (fs : ℕ → E n → E ℓF)
    (hgs : ∀ t < N, gs t ∈ 𝒢 x' (ξs t)) (hfs : ∀ s < N, fs s ∈ ℱ x' (ηs s))
    (xnew : E n) (hxnew : xnew ∈ P.X)
    (hmin : ∀ y ∈ P.X, VN P N gs fs xnew + ‖xnew - x'‖ ^ 2 / (2 * ρ)
      ≤ VN P N gs fs y + ‖y - x'‖ ^ 2 / (2 * ρ)) :
    Θbar P N N ξs ηs xnew + ‖xnew - x'‖ ^ 2 / (2 * ρ)
        ≤ VN P N gs fs xnew + ‖xnew - x'‖ ^ 2 / (2 * ρ) ∧
      VN P N gs fs xnew + ‖xnew - x'‖ ^ 2 / (2 * ρ) ≤ VN P N gs fs x' ∧
      VN P N gs fs x' = Θbar P N N ξs ηs x' := by
  obtain ⟨-, -, hψ, hφ, -⟩ := hA2
  have hNpos : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · gcongr ?_ + _
    unfold Θbar VN
    apply hψ
    intro i
    simp only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ hNpos
    apply Finset.sum_le_sum
    intro t ht
    have ht' : t < N := Finset.mem_range.mp ht
    apply hφ
    · intro j; exact hA3G.2.2.1 x' hx' _ _ (hgs t ht') xnew hxnew j
    · intro j
      simp only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
      apply mul_le_mul_of_nonneg_left _ hNpos
      apply Finset.sum_le_sum
      intro s hs
      exact hA3F.2.2.1 x' hx' _ _ (hfs s (Finset.mem_range.mp hs)) xnew hxnew j
  · have := hmin x' hx'
    simpa using this
  · unfold Θbar VN
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    rw [hA3G.2.1 x' hx' _ _ (hgs t (Finset.mem_range.mp ht))]
    congr 2
    apply Finset.sum_congr rfl
    intro s hs
    rw [hA3F.2.1 x' hx' _ _ (hfs s (Finset.mem_range.mp hs))]

