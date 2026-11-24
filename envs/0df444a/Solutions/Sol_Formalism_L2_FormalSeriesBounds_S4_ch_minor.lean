-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.S4.ch_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:24:51.907281+00:00
-- url     : https://prove2.me/submissions/f7573749-b90e-46ca-a66c-69572a50bb9d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_exists_strictMono_minor
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_lenCoker_mul_le
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_detOp_pow_apply_eigen
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_derivation_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4
variable {R : Type*} [CommRing R]
namespace Formalism.L2.FormalSeriesBounds.S4
theorem _root_.solution (v : AddValuation R (WithTop ℝ)) (hv : ∀ x, 0 ≤ v x) {n p h : ℕ}
    (S : Matrix (Fin n) (Fin p) R) (W : Matrix (Fin p) (Fin n) R) (hSW : S * W = 1)
    (α : Matrix (Fin p) (Fin h) R) (x : ℝ) (hx : lenCoker v α ≤ (x : WithTop ℝ)) :
    ∃ f : Fin n → Fin h, StrictMono f ∧
      v (Matrix.of fun k c => (S * α) c (f k)).det ≤ lenCoker v α ∧
      ∀ (F : Type) [CommRing F] [Algebra R F] (D : Fin n → Fin n → Derivation R F F)
        (χ : Fin n → F) (ev : F →ₐ[R] R),
        (∀ ρ c σ, D ρ c (χ σ) = (if σ = ρ then (S * α) c (f ρ) else 0) • χ σ) →
        (∀ σ, ev (χ σ) = 1) →
        ∀ y : ℕ,
          ev (((detOp fun ρ c => (D ρ c : F →ₗ[R] F)) ^ y) (∏ σ, χ σ)) =
              (Matrix.of fun k c => (S * α) c (f k)).det ^ y ∧
            v ((Matrix.of fun k c => (S * α) c (f k)).det ^ y) ≤
              (((y : ℝ) * x : ℝ) : WithTop ℝ) := by
  have h1 := lenCoker_mul_le v hv S W hSW α
  have hxt : lenCoker v α ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hx
  have hSt : lenCoker v (S * α) ≠ ⊤ := ne_top_of_le_ne_top hxt h1
  rcases isEmpty_or_nonempty (Fin n → Fin h) with hE | hE
  · exact absurd (by simp [lenCoker, Finset.univ_eq_empty]) hSt
  obtain ⟨g, -, hg⟩ := Finset.exists_mem_eq_inf Finset.univ Finset.univ_nonempty
    (fun g : Fin n → Fin h => v ((S * α).submatrix id g).det)
  have hgv : v ((S * α).submatrix id g).det = lenCoker v (S * α) := hg.symm
  have hdet : ((S * α).submatrix id g).det ≠ 0 := by
    intro h0
    apply hSt
    rw [← hgv, h0, AddValuation.map_zero]
  obtain ⟨f, hf, hfv⟩ := exists_strictMono_minor v (S * α) g hdet
  have htr : (Matrix.of fun k c => (S * α) c (f k)) = ((S * α).submatrix id f)ᵀ := by
    ext k c
    rfl
  have hmain : v (Matrix.of fun k c => (S * α) c (f k)).det ≤ lenCoker v α := by
    rw [htr, Matrix.det_transpose, hfv, hgv]
    exact h1
  refine ⟨f, hf, hmain, ?_⟩
  intro F _ _ D χ ev hD hev y
  set a : Matrix (Fin n) (Fin n) R := Matrix.of fun k c => (S * α) c (f k) with ha
  have hDa : ∀ ρ c, (D ρ c : F →ₗ[R] F) (∏ σ, χ σ) = a ρ c • ∏ σ, χ σ := by
    intro ρ c
    have := derivation_prod (D ρ c) χ (fun σ => if σ = ρ then (S * α) c (f ρ) else 0)
      (fun σ => hD ρ c σ) Finset.univ
    rw [Finset.sum_ite_eq'] at this
    simpa [ha] using this
  refine ⟨?_, ?_⟩
  · rw [detOp_pow_apply_eigen _ a _ hDa y, map_smul, map_prod]
    simp [hev]
  · have hvd : v a.det ≤ (x : WithTop ℝ) := le_trans hmain hx
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hvd)
    have htx : t ≤ x := by
      rw [← ht] at hvd
      exact WithTop.coe_le_coe.mp hvd
    rw [AddValuation.map_pow, ← ht, ← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left htx (Nat.cast_nonneg y)
end Formalism.L2.FormalSeriesBounds.S4
