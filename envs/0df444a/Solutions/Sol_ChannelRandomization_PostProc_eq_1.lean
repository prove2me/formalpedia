-- Prove2me | solution 1 for ChannelRandomization.PostProc.eq_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:17:11.566087+00:00
-- url     : https://prove2.me/submissions/506f1437-9e49-445b-a54d-d3ad892c600b

import Mathlib
import Definitions.Def_ChannelRandomization_PostProc_Setting

namespace Aux_CRPP1
open ChannelRandomization.PostProc

lemma expand {h k : ℕ} (φ : Map h k) (ψ : Map k h) :
    ∑ i, ∑ j, (ψ ∘ₗ φ) (Matrix.single i j 1) i j
      = ∑ i, ∑ j, ∑ a, ∑ b, φ (Matrix.single i j 1) a b * ψ (Matrix.single a b 1) i j := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.comp_apply]
  conv_lhs => rw [Matrix.matrix_eq_sum_single (φ (Matrix.single i j 1))]
  have e : ∀ a b, Matrix.single a b (φ (Matrix.single i j 1) a b)
      = φ (Matrix.single i j 1) a b • (Matrix.single a b 1 : Mat k) := by
    intro a b; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  simp only [e, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

lemma cyc {h k : ℕ} (φ : Map h k) (ψ : Map k h) : s (ψ ∘ₗ φ) = s (φ ∘ₗ ψ) := by
  have sw : ∀ (f : Fin h → Fin h → Fin k → Fin k → ℂ),
      ∑ i, ∑ j, ∑ a, ∑ b, f i j a b = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
    intro f
    calc _ = ∑ i, ∑ a, ∑ j, ∑ b, f i j a b := Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b, ∑ j, f i j a b :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ a, ∑ i, ∑ b, ∑ j, f i j a b := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_comm
  unfold s
  rw [Aux_CRPP1.expand, Aux_CRPP1.expand]
  congr 1
  refine (sw (fun i j a b => φ (Matrix.single i j 1) a b * ψ (Matrix.single a b 1) i j)).trans ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Aux_CRPP1

open ChannelRandomization.PostProc in
theorem solution {h k l : ℕ} (β : Map h k) (α : Map k l) (ψ : Map l h) (φ : Map h l) (χ : Map l h) :
    pair φ χ = pair χ φ ∧
      pair (α ∘ₗ β) ψ = s (α ∘ₗ β ∘ₗ ψ) ∧
      s (α ∘ₗ β ∘ₗ ψ) = pair β (ψ ∘ₗ α) ∧
      pair β (ψ ∘ₗ α) = pair α (β ∘ₗ ψ) := by
  have h3 : s (α ∘ₗ β ∘ₗ ψ) = pair β (ψ ∘ₗ α) := by
    unfold pair
    rw [Aux_CRPP1.cyc (β ∘ₗ ψ) α, LinearMap.comp_assoc]
  refine ⟨Aux_CRPP1.cyc χ φ, ?_, h3, ?_⟩
  · unfold pair; rw [LinearMap.comp_assoc]
  · rw [← h3]; rfl
