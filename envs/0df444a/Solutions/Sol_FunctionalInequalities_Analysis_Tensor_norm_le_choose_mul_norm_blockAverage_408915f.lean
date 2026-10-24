-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.norm_le_choose_mul_norm_blockAverage_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:02:44.923728+00:00
-- url     : https://prove2.me/submissions/e8a91a51-1b4a-49c7-bab3-91f26aadbedd

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_apply_eq_of_image_eq_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_exists_mem_fixingOutside_image_eq_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_fixingOutside_eq_smul_sum_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_norm_sq_le_sum_norm_sq_sum_subset_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_powersetCard_image_eq_408915f

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
private lemma FunctionalInequalities.Analysis.Tensor.inv_mem_fixingOutside {s : Finset Ω} {σ : Equiv.Perm Ω}
    (hσ : σ ∈ fixingOutside s) :
    (σ⁻¹ : Equiv.Perm Ω) ∈ fixingOutside s := by
  simp only [fixingOutside, mem_filter, mem_univ, true_and] at hσ ⊢
  intro x hx
  have h := congrArg (fun y => σ⁻¹ y) (hσ x hx)
  simpa using h.symm
omit [Fintype Ω] in
private lemma FunctionalInequalities.Analysis.Tensor.image_image_perm (A : Finset Ω) (g τ : Equiv.Perm Ω) :
    (A.image τ).image g = A.image (g * τ) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    exact Finset.mem_image.mpr ⟨z, hz, by simp [Equiv.Perm.mul_apply]⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
    exact Finset.mem_image.mpr
      ⟨τ z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, by simp [Equiv.Perm.mul_apply]⟩
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Analysis.Tensor in
/-- **BKL Lemma 2.2** (orthogonal-representation form, with the stronger binomial factor `C(2d, d)`). -/
theorem solution (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V))
    {A B Q : Finset Ω} {d : ℕ} (hA : A.card = d) (hB : B.card = 2 * d) (hAB : Disjoint A B)
    (hAQ : A ⊆ Q) (hQ : Q ⊆ A ∪ B) (hQc : Q.card = 2 * d) (v : V)
    (hvA : ∀ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside A, ρ σ v = v) (hvB : ∀ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside B, ρ σ v = v) :
    ‖v‖ ≤ ((2 * d).choose d : ℝ) * ‖FunctionalInequalities.Analysis.Tensor.blockAverage ρ Q v‖ := by
    classical
    let W := A ∪ B
    let T : Finset Ω → V := fun F =>
      if h : ∃ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside W, A.image σ = F then
        ρ (Classical.choose h) v
      else 0
    have hAW : A ⊆ W := by
      intro x hx
      exact mem_union_left B hx
    have hWQ : Q ⊆ W := by
      simpa [W] using hQ
    have hWcard : W.card = 3 * d := by
      dsimp [W]
      rw [card_union_of_disjoint hAB, hA, hB]
      omega
    have hT : ∀ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside W, ρ σ v = T (A.image σ) := by
      intro σ hσ
      let hh : ∃ τ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside W, A.image τ = A.image σ := ⟨σ, hσ, rfl⟩
      have hc := Classical.choose_spec hh
      have heq : ρ σ v = ρ (Classical.choose hh) v := by
        apply FunctionalInequalities.Analysis.Tensor.apply_eq_of_image_eq_408915f ρ v hvA hvB
        · exact hσ
        · exact hc.1
        · exact hc.2.symm
      simpa [T, hh] using heq
    have hprod :
        ∀ {g τ : Equiv.Perm Ω}, g ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside W →
          τ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside W → g * τ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside W := by
      intro g τ hg hτ
      simp only [FunctionalInequalities.Analysis.Tensor.fixingOutside, mem_filter, mem_univ, true_and] at hg hτ ⊢
      intro x hx
      simp [Equiv.Perm.mul_apply, hg x hx, hτ x hx]
    have hTinvariant :
        ∀ g ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside W, ∀ F, ρ g (T F) = T (F.image g) := by
      intro g hg F
      by_cases hF : ∃ τ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside W, A.image τ = F
      · rcases hF with ⟨τ, hτ, rfl⟩
        have hgt : g * τ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside W := hprod hg hτ
        have him := image_image_perm A g τ
        calc
          ρ g (T (A.image τ)) = ρ g (ρ τ v) := by rw [hT τ hτ]
          _ = ρ (g * τ) v := by
            simp
          _ = T (A.image (g * τ)) := hT (g * τ) hgt
          _ = T ((A.image τ).image g) := by rw [him]
      · have hF' : ¬ ∃ τ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside W, A.image τ = F.image g := by
          intro h'
          rcases h' with ⟨τ, hτ, hτim⟩
          have hgi : (g⁻¹ : Equiv.Perm Ω) ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside W :=
            inv_mem_fixingOutside hg
          have hgt : (g⁻¹ : Equiv.Perm Ω) * τ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside W :=
            hprod hgi hτ
          have him : A.image ((g⁻¹ : Equiv.Perm Ω) * τ) = F := by
            calc
              A.image ((g⁻¹ : Equiv.Perm Ω) * τ) =
                  (A.image τ).image (g⁻¹ : Equiv.Perm Ω) := by
                    rw [image_image_perm]
              _ = (F.image g).image (g⁻¹ : Equiv.Perm Ω) := by rw [hτim]
              _ = F := by
                ext x
                simp
          exact hF ⟨(g⁻¹ : Equiv.Perm Ω) * τ, hgt, him⟩
        simp [T, hF, hF', map_zero]
    have hTnorm : ∀ F ∈ W.powersetCard d, ‖T F‖ = ‖v‖ := by
      intro F hF
      have hFsub : F ⊆ W := (mem_powersetCard.mp hF).1
      have hFcard : F.card = d := (mem_powersetCard.mp hF).2
      obtain ⟨σ, hσ, hσim⟩ :=
        FunctionalInequalities.Analysis.Tensor.exists_mem_fixingOutside_image_eq_408915f hAW hFsub (by simp [hA, hFcard])
      have hTF : T F = ρ σ v := by
        rw [← hσim]
        exact (hT σ hσ).symm
      rw [hTF, (ρ σ).norm_map]
    have hsum :
        ∑ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside Q, ρ σ v =
          (((FunctionalInequalities.Analysis.Tensor.fixingOutside Q).card : ℝ) / ((2 * d).choose d : ℝ)) •
            ∑ F ∈ Q.powersetCard d, T F := by
      simpa [hA, hQc] using
        (FunctionalInequalities.Analysis.Tensor.sum_fixingOutside_eq_smul_sum_408915f ρ (A := A) (B := B) (Q := Q)
          hAQ hQ v T hT)
    have hS :
        (∑ F ∈ Q.powersetCard d, T F) =
          ((2 * d).choose d : ℝ) • FunctionalInequalities.Analysis.Tensor.blockAverage ρ Q v := by
      rw [FunctionalInequalities.Analysis.Tensor.blockAverage, hsum]
      have hN : (FunctionalInequalities.Analysis.Tensor.fixingOutside Q).card ≠ 0 := by
        apply Finset.card_ne_zero.mpr
        exact ⟨1, by simp [FunctionalInequalities.Analysis.Tensor.fixingOutside]⟩
      have hC : (2 * d).choose d ≠ 0 := by
        have hp : 0 < (2 * d).choose d := by
          apply Nat.choose_pos
          omega
        omega
      simp only [smul_smul]
      field_simp [hN, hC]
      simp
    have hinner :
        ∀ E ∈ W.powersetCard (2 * d),
          ‖∑ F ∈ E.powersetCard d, T F‖ =
            ((2 * d).choose d : ℝ) * ‖FunctionalInequalities.Analysis.Tensor.blockAverage ρ Q v‖ := by
      intro E hE
      have hEsub : E ⊆ W := (mem_powersetCard.mp hE).1
      have hEcard : E.card = 2 * d := (mem_powersetCard.mp hE).2
      obtain ⟨g, hg, hgim⟩ :=
        FunctionalInequalities.Analysis.Tensor.exists_mem_fixingOutside_image_eq_408915f hWQ hEsub (by simp [hQc, hEcard])
      have hs := FunctionalInequalities.Analysis.Tensor.sum_powersetCard_image_eq_408915f ρ g T
        (fun F => hTinvariant g hg F) Q d
      have hsumE :
          ∑ F ∈ E.powersetCard d, T F =
            ρ g (∑ F ∈ Q.powersetCard d, T F) := by
        rw [← hgim]
        exact hs
      rw [hsumE, (ρ g).norm_map, hS, norm_smul]
      congr 1
      exact abs_of_nonneg (by positivity)
    have hineq :=
      FunctionalInequalities.Analysis.Tensor.sum_norm_sq_le_sum_norm_sq_sum_subset_408915f W (d := d) hWcard T
    have hleft :
        ∑ F ∈ W.powersetCard d, ‖T F‖ ^ 2 =
          ((3 * d).choose d : ℝ) * ‖v‖ ^ 2 := by
      calc
        ∑ F ∈ W.powersetCard d, ‖T F‖ ^ 2 =
            ∑ F ∈ W.powersetCard d, ‖v‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro F hF
              rw [hTnorm F hF]
        _ = ((W.powersetCard d).card : ℝ) * ‖v‖ ^ 2 := by simp
        _ = ((3 * d).choose d : ℝ) * ‖v‖ ^ 2 := by
          rw [card_powersetCard, hWcard]
    have hright :
        ∑ E ∈ W.powersetCard (2 * d),
            ‖∑ F ∈ E.powersetCard d, T F‖ ^ 2 =
          ((3 * d).choose (2 * d) : ℝ) *
            (((2 * d).choose d : ℝ) * ‖FunctionalInequalities.Analysis.Tensor.blockAverage ρ Q v‖) ^ 2 := by
      calc
        ∑ E ∈ W.powersetCard (2 * d),
            ‖∑ F ∈ E.powersetCard d, T F‖ ^ 2 =
            ∑ E ∈ W.powersetCard (2 * d),
              (((2 * d).choose d : ℝ) * ‖FunctionalInequalities.Analysis.Tensor.blockAverage ρ Q v‖) ^ 2 := by
                apply Finset.sum_congr rfl
                intro E hE
                rw [hinner E hE]
        _ = ((W.powersetCard (2 * d)).card : ℝ) *
            (((2 * d).choose d : ℝ) * ‖FunctionalInequalities.Analysis.Tensor.blockAverage ρ Q v‖) ^ 2 := by simp
        _ = ((3 * d).choose (2 * d) : ℝ) *
            (((2 * d).choose d : ℝ) * ‖FunctionalInequalities.Analysis.Tensor.blockAverage ρ Q v‖) ^ 2 := by
          rw [card_powersetCard, hWcard]
    rw [hleft, hright] at hineq
    have hchoose : (3 * d).choose d = (3 * d).choose (2 * d) := by
      have h := Nat.choose_symm (by omega : d ≤ 3 * d)
      have hd : 3 * d - d = 2 * d := by omega
      simpa [hd] using h.symm
    have hc : 0 < ((3 * d).choose d : ℝ) := by
      have hp : 0 < (3 * d).choose d := by
        apply Nat.choose_pos
        omega
      exact_mod_cast hp
    have hsq :
        ‖v‖ ^ 2 ≤
          (((2 * d).choose d : ℝ) * ‖FunctionalInequalities.Analysis.Tensor.blockAverage ρ Q v‖) ^ 2 := by
      rw [← hchoose] at hineq
      exact le_of_mul_le_mul_left hineq hc
    exact (pow_le_pow_iff_left₀ (norm_nonneg v) (by positivity) two_ne_zero).1 hsq
