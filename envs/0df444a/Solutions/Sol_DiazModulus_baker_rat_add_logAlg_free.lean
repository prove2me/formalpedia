-- Prove2me | solution 1 for DiazModulus.baker_rat_add_logAlg_free
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T14:10:19.485287+00:00
-- url     : https://prove2.me/submissions/a4e96816-7d8d-469d-9f93-ea76aece1c62

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_Schanuel_baker_linear_forms_in_logarithms
import Theorems.Thm_DiazModulus_logAlg_exists_rat_basis

open Complex ComplexConjugate

/-! # Baker's theorem for `ℚ + ℒ`: rationally free elements are algebraically free

Write `e_k = q_k + λ_k` with `q_k ∈ ℚ` and `λ_k ∈ ℒ`. Among the `λ_k` choose a `ℚ`-basis
`μ₁, …, μ_s` of their `ℚ`-span, so that `μ` is `ℚ`-free, every `μ_t` lies in `ℒ` and
`λ_k = Σ_t c_{kt} μ_t` with `c_{kt} ∈ ℚ`. A relation `Σ_k a_k e_k = 0` with algebraic `a_k` reads
`b₀ + Σ_t b_t μ_t = 0` with `b₀ = Σ_k a_k q_k` and `b_t = Σ_k a_k c_{kt}` algebraic, so Baker's
theorem gives `b₀ = 0` and `b_t = 0` for all `t`. The rational vectors `R_k = (q_k, c_{k1}, …, c_{ks})`
are `ℚ`-free, because a rational relation among them is a rational relation among the `e_k`.
Rationally free vectors of `ℚ^{1+s}` stay free over the algebraic numbers, and the vanishing of
`b₀, b₁, …, b_s` says exactly that `Σ_k a_k R_k = 0`; hence `a = 0`. -/

namespace RC4_BRL
open DiazModulus

/-- Expanding a linear combination of `e_k = q_k + Σ_t c_{kt} μ_t`. -/
theorem expand {m s : ℕ} (e : Fin m → ℂ) (q : Fin m → ℚ) (c : Fin m → Fin s → ℚ) (μ : Fin s → ℂ)
    (he : ∀ k, e k = (q k : ℂ) + ∑ t, (c k t : ℂ) * μ t) (a : Fin m → ℂ) :
    ∑ k, a k * e k = ∑ k, a k * (q k : ℂ) + ∑ t, (∑ k, a k * (c k t : ℂ)) * μ t := by
  simp_rw [he, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun k _ => by ring

end RC4_BRL

open DiazModulus RC4_BRL in
theorem solution {m : ℕ} (e : Fin m → ℂ) (he : LinearIndependent ℚ e)
    (heL : ∀ k, ∃ q : ℚ, e k - q ∈ LogAlg) : LinearIndependent (↥Qbar) e := by
  classical
  choose q hq using heL
  obtain ⟨s, μ, c, hμind, hμL, hc⟩ :=
    DiazModulus.logAlg_exists_rat_basis (fun k => e k - q k) hq
  have he' : ∀ k, e k = (q k : ℂ) + ∑ t, (c k t : ℂ) * μ t := fun k => by
    rw [← hc k]; ring
  -- the rational vectors `R_k = (q_k, c_{k1}, …, c_{ks})` are `ℚ`-free
  let R : Fin m → Option (Fin s) → ℚ := fun k o => o.elim (q k) (c k)
  have hR : LinearIndependent ℚ R := by
    rw [Fintype.linearIndependent_iff]
    intro β hβ
    apply (Fintype.linearIndependent_iff.mp he) β
    have h0 : ∑ k, β k * q k = 0 := by simpa [R] using congrFun hβ none
    have ht : ∀ t, ∑ k, β k * c k t = 0 := fun t => by simpa [R] using congrFun hβ (some t)
    simp only [Rat.smul_def]
    rw [expand e q c μ he' (fun k => (β k : ℂ))]
    have h0' : ∑ k, (β k : ℂ) * (q k : ℂ) = 0 := by exact_mod_cast h0
    have ht' : ∀ t, ∑ k, (β k : ℂ) * (c k t : ℂ) = 0 := fun t => by exact_mod_cast ht t
    simp [h0', ht']
  -- base change `ℚ → Q̄`
  have hRQ : LinearIndependent (↥Qbar) (fun k => algebraMap ℚ (↥Qbar) ∘ R k) :=
    (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ↥Qbar)).mpr hR
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hrel : ∑ k, (g k : ℂ) * (q k : ℂ) + ∑ t, (∑ k, (g k : ℂ) * (c k t : ℂ)) * μ t = 0 := by
    rw [← expand e q c μ he' (fun k => (g k : ℂ))]
    simpa [Subfield.smul_def] using hg
  -- Baker's theorem
  have hBK : ∑ k, (g k : ℂ) * (q k : ℂ) = 0 ∧ ∀ t, ∑ k, (g k : ℂ) * (c k t : ℂ) = 0 := by
    by_contra hne
    have hnz : ∑ k, (g k : ℂ) * (q k : ℂ) ≠ 0 ∨ ∃ t, ∑ k, (g k : ℂ) * (c k t : ℂ) ≠ 0 := by
      by_contra h
      push Not at h
      exact hne h
    have hb₀ : IsAlgebraic ℚ (∑ k, (g k : ℂ) * (q k : ℂ)) :=
      mem_Qbar_iff.mp (Qbar.sum_mem fun k _ => Qbar.mul_mem (g k).2 (SubfieldClass.ratCast_mem Qbar _))
    have hb : ∀ t, IsAlgebraic ℚ (∑ k, (g k : ℂ) * (c k t : ℂ)) := fun t =>
      mem_Qbar_iff.mp (Qbar.sum_mem fun k _ => Qbar.mul_mem (g k).2 (SubfieldClass.ratCast_mem Qbar _))
    exact Schanuel.baker_linear_forms_in_logarithms s μ hμind hμL _ _ hb₀ hb hnz hrel
  apply (Fintype.linearIndependent_iff.mp hRQ) g
  funext o
  apply Subtype.ext
  rcases o with _ | t
  · simpa [R, Subfield.smul_def] using hBK.1
  · simpa [R, Subfield.smul_def] using hBK.2 t
