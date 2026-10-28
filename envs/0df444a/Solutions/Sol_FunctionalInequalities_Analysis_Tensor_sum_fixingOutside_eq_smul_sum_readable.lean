-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.sum_fixingOutside_eq_smul_sum_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:30:30.098217+00:00
-- url     : https://prove2.me/submissions/5d1d444d-2d48-4266-85ef-3aee753d19c8

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_card_fiber_eq_readable
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_image_mem_powersetCard_of_mem_fixingOutside_readable

noncomputable section
open Finset
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
/-- `fixingOutside` is monotone. -/
theorem FunctionalInequalities.Analysis.Tensor.fixingOutside_mono {s t : Finset Ω} (hst : s ⊆ t) : fixingOutside s ⊆ fixingOutside t := by
    intro σ hσ
    have hσ' : ∀ x, x ∉ s → σ x = x := by
      simpa [fixingOutside] using hσ
    have h : ∀ x, x ∉ t → σ x = x := by
      intro x hx
      apply hσ' x
      intro hxs
      exact hx (hst hxs)
    simpa [fixingOutside] using h
/-- Grouping a block sum by the image of `A`: if `ρ σ v = T (A.image σ)` for every `σ` fixing
everything outside `A ∪ B`, then for `A ⊆ Q ⊆ A ∪ B`,
`∑_{σ ∈ fixingOutside Q} ρ σ v = (#fixingOutside Q / C(|Q|, |A|)) • ∑_{F ⊆ Q, |F| = |A|} T F`. -/
theorem solution (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V)) {A B Q : Finset Ω}
    (hAQ : A ⊆ Q) (hQ : Q ⊆ A ∪ B) (v : V) (T : Finset Ω → V)
    (hT : ∀ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside (A ∪ B), ρ σ v = T (A.image σ)) :
    ∑ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside Q, ρ σ v =
      (((FunctionalInequalities.Analysis.Tensor.fixingOutside Q).card : ℝ) / (Q.card.choose A.card : ℝ)) •
        ∑ F ∈ Q.powersetCard A.card, T F := by
    have hA : A ∈ Q.powersetCard A.card := by
      simp [hAQ]
    let M : ℕ :=
      ((FunctionalInequalities.Analysis.Tensor.fixingOutside Q).filter fun σ : Equiv.Perm Ω => A.image σ = A).card
    have hfiber :
        ∀ F ∈ Q.powersetCard A.card,
          ((FunctionalInequalities.Analysis.Tensor.fixingOutside Q).filter fun σ : Equiv.Perm Ω => A.image σ = F).card = M := by
      intro F hF
      exact FunctionalInequalities.Analysis.Tensor.card_fiber_eq_readable hF hA
    have hmap :
        ∀ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside Q,
          A.image σ ∈ Q.powersetCard A.card :=
      fun σ hσ => FunctionalInequalities.Analysis.Tensor.image_mem_powersetCard_of_mem_fixingOutside_readable hAQ hσ
    have hinner :
        ∀ F ∈ Q.powersetCard A.card,
          ∑ σ ∈ (FunctionalInequalities.Analysis.Tensor.fixingOutside Q).filter
              (fun σ : Equiv.Perm Ω => A.image σ = F), T (A.image σ) =
            M • T F := by
      intro F hF
      calc
        ∑ σ ∈ (FunctionalInequalities.Analysis.Tensor.fixingOutside Q).filter
            (fun σ : Equiv.Perm Ω => A.image σ = F), T (A.image σ) =
            ∑ σ ∈ (FunctionalInequalities.Analysis.Tensor.fixingOutside Q).filter
              (fun σ : Equiv.Perm Ω => A.image σ = F), T F := by
                apply Finset.sum_congr rfl
                intro σ hσ
                simp only [Finset.mem_filter] at hσ
                exact congrArg T hσ.2
        _ = M • T F := by
          simp [M, hfiber F hF]
    have hsum :
        (∑ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside Q, ρ σ v) =
          M • ∑ F ∈ Q.powersetCard A.card, T F := by
      calc
        ∑ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside Q, ρ σ v =
            ∑ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside Q, T (A.image σ) := by
              apply Finset.sum_congr rfl
              intro σ hσ
              exact hT σ (FunctionalInequalities.Analysis.Tensor.fixingOutside_mono hQ hσ)
        _ = ∑ F ∈ Q.powersetCard A.card,
              ∑ σ ∈ (FunctionalInequalities.Analysis.Tensor.fixingOutside Q).filter
                (fun σ : Equiv.Perm Ω => A.image σ = F), T (A.image σ) := by
              rw [Finset.sum_fiberwise_of_maps_to hmap]
        _ = ∑ F ∈ Q.powersetCard A.card, M • T F := by
              apply Finset.sum_congr rfl
              intro F hF
              exact hinner F hF
        _ = M • ∑ F ∈ Q.powersetCard A.card, T F := by
              simp [Finset.smul_sum]
    have hcard :
        (FunctionalInequalities.Analysis.Tensor.fixingOutside Q).card =
          Q.card.choose A.card * M := by
      calc
        (FunctionalInequalities.Analysis.Tensor.fixingOutside Q).card =
            ∑ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside Q, (1 : ℕ) := by simp
        _ = ∑ F ∈ Q.powersetCard A.card,
              ∑ σ ∈ (FunctionalInequalities.Analysis.Tensor.fixingOutside Q).filter
                (fun σ : Equiv.Perm Ω => A.image σ = F), (1 : ℕ) := by
              rw [Finset.sum_fiberwise_of_maps_to hmap]
        _ = ∑ F ∈ Q.powersetCard A.card,
              ((FunctionalInequalities.Analysis.Tensor.fixingOutside Q).filter
                (fun σ : Equiv.Perm Ω => A.image σ = F)).card := by
              simp
        _ = ∑ F ∈ Q.powersetCard A.card, M := by
              apply Finset.sum_congr rfl
              intro F hF
              exact hfiber F hF
        _ = (Q.powersetCard A.card).card * M := by
              simp
        _ = Q.card.choose A.card * M := by
              rw [Finset.card_powersetCard]
    have hchoose : 0 < Q.card.choose A.card :=
      Nat.choose_pos (Finset.card_le_card hAQ)
    have hM :
        (M : ℝ) =
          ((FunctionalInequalities.Analysis.Tensor.fixingOutside Q).card : ℝ) / (Q.card.choose A.card : ℝ) := by
      have hc : (Q.card.choose A.card : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hchoose)
      apply (eq_div_iff hc).2
      rw [show ((FunctionalInequalities.Analysis.Tensor.fixingOutside Q).card : ℝ) =
          (Q.card.choose A.card : ℝ) * (M : ℝ) by
            exact_mod_cast hcard]
      ring
    calc
      ∑ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside Q, ρ σ v =
          M • ∑ F ∈ Q.powersetCard A.card, T F := hsum
      _ = (M : ℝ) • ∑ F ∈ Q.powersetCard A.card, T F := by
        simp only [Nat.cast_smul_eq_nsmul]
      _ = (((FunctionalInequalities.Analysis.Tensor.fixingOutside Q).card : ℝ) / (Q.card.choose A.card : ℝ)) •
            ∑ F ∈ Q.powersetCard A.card, T F := by
        rw [hM]
