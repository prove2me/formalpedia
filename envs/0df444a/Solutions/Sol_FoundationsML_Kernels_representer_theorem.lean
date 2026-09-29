-- Prove2me | solution 1 for FoundationsML.Kernels.representer_theorem
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:10:03.900701+00:00
-- url     : https://prove2.me/submissions/0dd80ecb-1d84-439d-8dab-74327b9cd470

import Mathlib
import Definitions.Def_FoundationsML_Kernels_IsPDS
import Definitions.Def_FoundationsML_Kernels_IsRKHSOf
import Definitions.Def_FoundationsML_Kernels_IsMinimizer

namespace FoundationsML.Kernels

theorem aux_rep_pds : IsPDS (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) := by
  refine ⟨fun _ _ => rfl, fun S c => ?_⟩
  have h : ∑ i ∈ S, ∑ j ∈ S, c i * c j * (1 : ℝ) = (∑ i ∈ S, c i) * (∑ i ∈ S, c i) := by
    rw [Finset.sum_mul_sum]
    simp
  rw [h]
  exact mul_self_nonneg _

theorem aux_rep_rkhs :
    IsRKHSOf (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) (fun _ => (1 : ℝ)) (fun h _ => h) := by
  refine ⟨fun _ _ => ?_, fun h _ => ?_⟩ <;> simp

end FoundationsML.Kernels

open FoundationsML.Kernels

theorem solution : ¬ (∀ {X H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : X → X → ℝ) (hK : IsPDS K) (Φ : X → H) (ev : H → X → ℝ)
    (hRKHS : IsRKHSOf K Φ ev)
    (m : ℕ) (x : Fin m → X)
    (G : ℝ → ℝ) (hG : Monotone G)
    (L : (Fin m → ℝ) → WithTop ℝ)
    (F : H → WithTop ℝ) (hF : ∀ h : H, F h = (G ‖h‖ : WithTop ℝ) + L (fun i => ev h (x i)))
    (hne : ∃ h₀ : H, F h₀ ≠ ⊤),
    (∃ α : Fin m → ℝ, IsMinimizer F (∑ i, α i • Φ (x i))) ∧
    (StrictMono G →
      ∀ h : H, IsMinimizer F h → ∃ α : Fin m → ℝ, h = ∑ i, α i • Φ (x i))) := by
  intro hall
  have key := (hall (X := Unit) (H := ℝ) (fun _ _ => (1 : ℝ)) aux_rep_pds (fun _ => (1 : ℝ))
    (fun h _ => h) aux_rep_rkhs 1 (fun _ => ()) (fun _ => (0 : ℝ)) (fun _ _ _ => le_refl _)
    (fun v => ((v 0 : ℝ) : WithTop ℝ)) (fun h => ((h : ℝ) : WithTop ℝ))
    (fun h => by simp) ⟨0, by simp⟩).1
  obtain ⟨α, hα⟩ := key
  have h1 := hα ((∑ i, α i • (1 : ℝ)) - 1)
  have h2 : ((∑ i, α i • (1 : ℝ) : ℝ) : WithTop ℝ) ≤ (((∑ i, α i • (1 : ℝ)) - 1 : ℝ) : WithTop ℝ) := h1
  rw [WithTop.coe_le_coe] at h2
  linarith
