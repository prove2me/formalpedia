-- Prove2me | solution 1 for ChannelRandomization.PostProc.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:14:53.29639+00:00
-- url     : https://prove2.me/submissions/9a29a1df-ff35-4fc7-a446-d4a5af8fa008

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

end Aux_CRPP1

open ChannelRandomization.PostProc in
theorem solution {h k : ℕ} (φ : Map h k) (ψ : Map k h) : s (ψ ∘ₗ φ) = s (φ ∘ₗ ψ) := by
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
