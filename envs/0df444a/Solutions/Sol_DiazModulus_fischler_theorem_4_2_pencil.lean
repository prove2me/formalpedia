-- Prove2me | solution 1 for DiazModulus.fischler_theorem_4_2_pencil
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-21T08:58:03.473555+00:00
-- url     : https://prove2.me/submissions/22e5e6aa-a2dd-4496-8670-b03a4f4a05c7

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_fischler_prop_3_2_pencil
import Theorems.Thm_DiazModulus_fischler_rational_hull
import Theorems.Thm_DiazModulus_rational_common_kernel

open Complex ComplexConjugate

/-! # Fischler 2001, Theorem 4.2 in pencil form

Write `M_α` for the `d × l` matrix with columns `F_a α` and `r = rk M_x`, with `2r < d`. Write
`x = Σ c_b w_b` with the `c_b` free over `Q̄` and the `w_b` algebraic, and let `E₀` be the complex span of the
`w_b`. It is defined over `Q̄` and contains `x`. It lies in every subspace `E` defined over `Q̄` that contains
`x`: such an `E` is the common kernel of algebraic linear forms, these vanish at `x`, hence at every `w_b`.
So `E₀` lies in the least such subspace, and the pencil form of Proposition 3.2 gives `S ⊂ ℂˡ`, `T ⊂ ℂᵈ` of
codimensions `l₁` and `d₁ ≥ 1` with `(d − r)l₁ ≤ rd₁` and `M_α s = (Σ s_a F_a)α ∈ T` for `s ∈ S`, `α ∈ E₀`.
If `rk M_α = d` for some `α ∈ E₀`, rank–nullity on `M_α` restricted to `S` (split `ℂˡ = S ⊕ S'`, so
`Im M_α ⊂ M_α(S) + M_α(S')`) gives `d ≤ dim T + l₁`, i.e. `d₁ ≤ l₁`. Then `(d − r)l₁ ≤ rd₁ ≤ rl₁` with `l₁ ≥ 1`
gives `d − r ≤ r`, against `2r < d`. So `rk M_α < d` on `E₀`. -/

namespace RC10_Th42P
open DiazModulus

/-- The columns of `M_α` are the `F_a α`, so `M_α s = (Σ s_a F_a) α`. -/
theorem pencil_mulVec {d l : ℕ} (F : Fin l → Matrix (Fin d) (Fin d) ℂ) (α : Fin d → ℂ)
    (s : Fin l → ℂ) :
    (Matrix.of fun i a => ((F a).mulVec α) i).mulVec s = (∑ a, s a • F a).mulVec α := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring

/-- Rank–nullity for a matrix mapping `S` into `T`: `dim S + rk M ≤ dim T + l`. -/
theorem finrank_add_rank_le {d l : ℕ} (M : Matrix (Fin d) (Fin l) ℂ)
    (S : Submodule ℂ (Fin l → ℂ)) (T : Submodule ℂ (Fin d → ℂ))
    (h : ∀ s ∈ S, M.mulVec s ∈ T) :
    Module.finrank ℂ S + M.rank ≤ Module.finrank ℂ T + l := by
  obtain ⟨S', hS'⟩ := Submodule.exists_isCompl S
  have hc := Submodule.finrank_add_eq_of_isCompl hS'
  have hrange : LinearMap.range M.mulVecLin = S.map M.mulVecLin ⊔ S'.map M.mulVecLin := by
    rw [LinearMap.range_eq_map, ← Submodule.map_sup, hS'.sup_eq_top]
  have h1 : Module.finrank ℂ (S.map M.mulVecLin) ≤ Module.finrank ℂ T :=
    Submodule.finrank_mono (Submodule.map_le_iff_le_comap.2 fun s hs => h s hs)
  have h2 := Submodule.finrank_map_le M.mulVecLin S'
  have h3 := Submodule.finrank_add_le_finrank_add_finrank (S.map M.mulVecLin) (S'.map M.mulVecLin)
  have hl : Module.finrank ℂ (Fin l → ℂ) = l := Module.finrank_fin_fun ℂ
  rw [Matrix.rank, hrange]
  omega

end RC10_Th42P

open DiazModulus RC10_Th42P in
theorem solution {d l : ℕ} (F : Fin l → Matrix (Fin d) (Fin d) ℂ)
    (hF : ∀ a i j, F a i j ∈ Qbar) (x : Fin d → ℂ) (hx : ∀ i, x i ∈ LogAlgTilde)
    (hr : 2 * (Matrix.of fun i a => ((F a).mulVec x) i).rank < d) :
    ∃ E : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ E ∧ ∀ i, v i ∈ Qbar} = E ∧ x ∈ E ∧
      ∀ α ∈ E, (Matrix.of fun i a => ((F a).mulVec α) i).rank < d := by
  have hd : 0 < d := by omega
  obtain ⟨n, c, w, -, -, -, hw, hxw, hψ⟩ := DiazModulus.fischler_rational_hull x
  obtain ⟨S, T, hT1, hineq, hST⟩ := DiazModulus.fischler_prop_3_2_pencil hd F hF x hx
  set E₀ : Submodule ℂ (Fin d → ℂ) := Submodule.span ℂ (Set.range w) with hE₀
  have hwE : ∀ b, w b ∈ E₀ := fun b => Submodule.subset_span ⟨b, rfl⟩
  have hxE : x ∈ E₀ := by
    rw [hxw]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hwE b)
  have hrat : Submodule.span ℂ {v : Fin d → ℂ | v ∈ E₀ ∧ ∀ i, v i ∈ Qbar} = E₀ := by
    apply le_antisymm
    · exact Submodule.span_le.2 fun v hv => hv.1
    · exact Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact Submodule.subset_span ⟨hwE b, hw b⟩)
  have hmin : E₀ ≤ sInf {E : Submodule ℂ (Fin d → ℂ) |
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ E ∧ ∀ i, v i ∈ Qbar} = E ∧ x ∈ E} := by
    refine le_sInf ?_
    rintro E ⟨hErat, hxE'⟩
    obtain ⟨ψ, hψalg, hψE⟩ := DiazModulus.rational_common_kernel E hErat
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, rfl⟩
    exact (hψE _).2 fun i => hψ (ψ i) (hψalg i) ((hψE x).1 hxE' i) b
  refine ⟨E₀, hrat, hxE, fun α hα => ?_⟩
  refine lt_of_not_ge fun hcon => ?_
  have hle := Matrix.rank_le_card_height (Matrix.of fun i a => ((F a).mulVec α) i)
  simp only [Fintype.card_fin] at hle
  have key := finrank_add_rank_le (Matrix.of fun i a => ((F a).mulVec α) i) S T
    (fun s hs => by rw [pencil_mulVec]; exact hST s hs α (hmin hα))
  have hS : Module.finrank ℂ S ≤ l := by
    simpa using Submodule.finrank_le S
  have hT : Module.finrank ℂ T ≤ d := by
    simpa using Submodule.finrank_le T
  generalize (Matrix.of fun i a => ((F a).mulVec x) i).rank = r at hr hineq
  generalize hl₁ : l - Module.finrank ℂ S = l₁ at hineq
  generalize hd₁ : d - Module.finrank ℂ T = d₁ at hineq hT1
  have hdl : d₁ ≤ l₁ := by omega
  have h1 : (d - r) * l₁ ≤ r * l₁ := hineq.trans (Nat.mul_le_mul_left r hdl)
  have h2 : d - r ≤ r := Nat.le_of_mul_le_mul_right h1 (by omega)
  omega
