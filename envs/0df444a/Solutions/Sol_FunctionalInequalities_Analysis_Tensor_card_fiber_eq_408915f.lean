-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.card_fiber_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:59:23.728008+00:00
-- url     : https://prove2.me/submissions/c8d02298-fc43-46c5-af6d-991e6b61c620

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_exists_mem_fixingOutside_image_eq_408915f

noncomputable section
open Finset
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Tensor
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
private lemma FunctionalInequalities.Analysis.Tensor.mul_mem_fixingOutside {s : Finset Ω} {σ τ : Equiv.Perm Ω}
    (hσ : σ ∈ fixingOutside s) (hτ : τ ∈ fixingOutside s) :
    σ * τ ∈ fixingOutside s := by
  simp only [fixingOutside, mem_filter, mem_univ, true_and] at hσ hτ ⊢
  intro x hx
  simp [Equiv.Perm.coe_mul, hσ x hx, hτ x hx]
private lemma FunctionalInequalities.Analysis.Tensor.inv_mem_fixingOutside {s : Finset Ω} {σ : Equiv.Perm Ω}
    (hσ : σ ∈ fixingOutside s) :
    (σ⁻¹ : Equiv.Perm Ω) ∈ fixingOutside s := by
  simp only [fixingOutside, mem_filter, mem_univ, true_and] at hσ ⊢
  intro x hx
  have h := congrArg (fun y => σ⁻¹ y) (hσ x hx)
  simpa using h.symm
omit [Fintype Ω] in
private lemma FunctionalInequalities.Analysis.Tensor.image_mul_perm (S : Finset Ω) (σ τ : Equiv.Perm Ω) :
    S.image (σ * τ) = (S.image τ).image σ := by
  simp [Finset.image_image, Equiv.Perm.coe_mul]
omit [Fintype Ω] in
private lemma FunctionalInequalities.Analysis.Tensor.image_inv_image_perm (S : Finset Ω) (σ : Equiv.Perm Ω) :
    (S.image σ).image (σ⁻¹ : Equiv.Perm Ω) = S := by
  simp [Finset.image_image]
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Analysis.Tensor in
/-- All fibers of `σ ↦ A.image σ` on `fixingOutside Q` over the `|A|`-subsets of `Q` have the same
size. -/
theorem solution {A Q : Finset Ω} {F F' : Finset Ω}
    (hF : F ∈ Q.powersetCard A.card) (hF' : F' ∈ Q.powersetCard A.card) :
    ((FunctionalInequalities.Analysis.Tensor.fixingOutside Q).filter fun σ : Equiv.Perm Ω => A.image σ = F).card =
      ((FunctionalInequalities.Analysis.Tensor.fixingOutside Q).filter fun σ : Equiv.Perm Ω => A.image σ = F').card := by
    have hFsub : F ⊆ Q := (Finset.mem_powersetCard.mp hF).1
    have hF'sub : F' ⊆ Q := (Finset.mem_powersetCard.mp hF').1
    have hcards : F.card = F'.card :=
      (Finset.mem_powersetCard.mp hF).2.trans
        (Finset.mem_powersetCard.mp hF').2.symm
    obtain ⟨g, hg, hgf⟩ :=
      FunctionalInequalities.Analysis.Tensor.exists_mem_fixingOutside_image_eq_408915f hFsub hF'sub hcards
    have hgf_inv : F'.image (g⁻¹ : Equiv.Perm Ω) = F := by
      calc
        F'.image (g⁻¹ : Equiv.Perm Ω) =
            (F.image g).image (g⁻¹ : Equiv.Perm Ω) := by
              rw [hgf]
        _ = F := image_inv_image_perm F g
    refine Finset.card_bij'
      (s := (FunctionalInequalities.Analysis.Tensor.fixingOutside Q).filter
        (fun σ : Equiv.Perm Ω => A.image σ = F))
      (t := (FunctionalInequalities.Analysis.Tensor.fixingOutside Q).filter
        (fun σ : Equiv.Perm Ω => A.image σ = F'))
      (fun σ _ => g * σ) (fun τ _ => g⁻¹ * τ) ?_ ?_ ?_ ?_
    · intro σ hσ
      refine mem_filter.mpr ⟨mul_mem_fixingOutside hg (mem_filter.mp hσ).1, ?_⟩
      rw [image_mul_perm, (mem_filter.mp hσ).2, hgf]
    · intro τ hτ
      refine mem_filter.mpr
        ⟨mul_mem_fixingOutside (inv_mem_fixingOutside hg) (mem_filter.mp hτ).1, ?_⟩
      rw [image_mul_perm, (mem_filter.mp hτ).2, hgf_inv]
    · intro σ hσ
      exact inv_mul_cancel_left g σ
    · intro τ hτ
      exact mul_inv_cancel_left g τ
