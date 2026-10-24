-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.sum_perm_inner_init_last_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:51:52.183237+00:00
-- url     : https://prove2.me/submissions/51c3797b-4bf8-4421-bc0a-68abd049b2b0

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Data.Fintype.Perm
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_card_filter_perm_apply_last_eq_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_exists_perm_init_comp_eq_408915f

noncomputable section
open scoped RealInnerProductSpace
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Analysis.Tensor in
/-- Symmetrizing `⟪Φ (h₀, …, h_{d-1}), h_d⟫` for a symmetric `Φ`: the sum over permutations is
`d!` times the sum over the position of the last argument. -/
theorem solution {d : ℕ} (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) E)
    (hΦ : ∀ (τ : Equiv.Perm (Fin d)) (v : Fin d → E), Φ (v ∘ τ) = Φ v) (h : Fin (d + 1) → E) :
    ∑ σ : Equiv.Perm (Fin (d + 1)), ⟪Φ (Fin.init (h ∘ σ)), h (σ (Fin.last d))⟫ =
      (d.factorial : ℝ) * ∑ k : Fin (d + 1), ⟪Φ (k.removeNth h), h k⟫ := by
    let F : Equiv.Perm (Fin (d + 1)) → ℝ :=
      fun σ => ⟪Φ (Fin.init (h ∘ σ)), h (σ (Fin.last d))⟫
    change Finset.sum Finset.univ F =
      (d.factorial : ℝ) *
        Finset.sum Finset.univ (fun k : Fin (d + 1) =>
          ⟪Φ (k.removeNth h), h k⟫)
    calc
      Finset.sum Finset.univ F =
          Finset.sum Finset.univ (fun k : Fin (d + 1) =>
            Finset.sum
              (Finset.univ.filter
                (fun σ : Equiv.Perm (Fin (d + 1)) =>
                  σ (Fin.last d) = k))
              F) := by
        simpa using
          (Finset.sum_fiberwise Finset.univ
            (fun σ : Equiv.Perm (Fin (d + 1)) => σ (Fin.last d)) F).symm
      _ = Finset.sum Finset.univ (fun k : Fin (d + 1) =>
            (d.factorial : ℝ) * ⟪Φ (k.removeNth h), h k⟫) := by
        apply Finset.sum_congr rfl
        intro k hk
        calc
          Finset.sum
              (Finset.univ.filter
                (fun σ : Equiv.Perm (Fin (d + 1)) =>
                  σ (Fin.last d) = k))
              F =
              Finset.sum
                (Finset.univ.filter
                  (fun σ : Equiv.Perm (Fin (d + 1)) =>
                    σ (Fin.last d) = k))
                (fun _ => ⟪Φ (k.removeNth h), h k⟫) := by
            apply Finset.sum_congr rfl
            intro σ hσ
            have hkσ : σ (Fin.last d) = k :=
              (Finset.mem_filter.mp hσ).2
            obtain ⟨τ, hτ⟩ :=
              FunctionalInequalities.Analysis.Tensor.exists_perm_init_comp_eq_408915f h σ hkσ
            have hΦσ :
                Φ (Fin.init (h ∘ σ)) = Φ (k.removeNth h) := by
              calc
                Φ (Fin.init (h ∘ σ)) =
                    Φ (k.removeNth h ∘ τ) := by rw [hτ]
                _ = Φ (k.removeNth h) := hΦ τ _
            dsimp [F]
            rw [hΦσ, hkσ]
          _ =
              ((Finset.univ.filter
                  (fun σ : Equiv.Perm (Fin (d + 1)) =>
                    σ (Fin.last d) = k)).card : ℝ) *
                ⟪Φ (k.removeNth h), h k⟫ := by
            simp [nsmul_eq_mul]
          _ = (d.factorial : ℝ) * ⟪Φ (k.removeNth h), h k⟫ := by
            rw [FunctionalInequalities.Analysis.Tensor.card_filter_perm_apply_last_eq_408915f]
      _ = (d.factorial : ℝ) *
          Finset.sum Finset.univ (fun k : Fin (d + 1) =>
            ⟪Φ (k.removeNth h), h k⟫) := by
        rw [Finset.mul_sum]
