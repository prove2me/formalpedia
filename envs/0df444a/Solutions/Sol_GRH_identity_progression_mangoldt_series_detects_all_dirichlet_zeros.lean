-- Prove2me | solution 1 for GRH.identity_progression_mangoldt_series_detects_all_dirichlet_zeros
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T01:45:29.541597+00:00
-- url     : https://prove2.me/submissions/68c098a6-2b18-472f-920c-3e5e9d292719

import Definitions.Def_GRH_SplitPrimeLower
import Mathlib.Tactic.FieldSimp

open Complex Finset DirichletCharacter ArithmeticFunction GRH.SplitPrimeLower
open scoped Classical

theorem solution (q : ℕ) [NeZero q] :
    Differentiable ℂ (regularProduct q) ∧
    (∀ s : ℂ, 1 ≤ s.re → regularProduct q s ≠ 0) ∧
    (∀ (χ : DirichletCharacter ℂ q) (s : ℂ), ¬ (χ = 1 ∧ s = 1) →
      regularProduct q s ≠ 0 → χ.LFunction s ≠ 0) ∧
    ∀ s : ℂ, 1 < s.re →
      (q.totient:ℂ) * LSeries (fun n => (vonMangoldt.residueClass (1:ZMod q) n:ℂ)) s =
        1/(s-1) - logDeriv (regularProduct q) s := by
  classical
  let S := ({1}ᶜ : Finset (DirichletCharacter ℂ q))
  have ntr {χ : DirichletCharacter ℂ q} (hχ : χ ∈ S) : χ ≠ 1 := by simpa [S] using hχ
  have prodD (s : ℂ) : DifferentiableAt ℂ (fun z => ∏ χ ∈ S, χ.LFunction z) s :=
    .fun_finsetProd fun χ hχ => differentiable_LFunction (ntr hχ) s
  have nonvan (s : ℂ) (hs : 1 ≤ s.re) (χ : DirichletCharacter ℂ q) (hχ : χ ∈ S) :
      χ.LFunction s ≠ 0 := χ.LFunction_ne_zero_of_one_le_re (.inl (ntr hχ)) hs
  have reg (s : ℂ) (hs : 1 ≤ s.re) : LFunctionTrivChar₁ q s ≠ 0 := by
    rcases eq_or_ne s 1 with he | he
    · simpa only [he] using LFunctionTrivChar₁_apply_one_ne_zero q
    · rw [LFunctionTrivChar₁, Function.update_of_ne he]
      exact mul_ne_zero (sub_ne_zero.mpr he) ((1:DirichletCharacter ℂ q).LFunction_ne_zero_of_one_le_re (.inr he) hs)
  refine ⟨fun s => (differentiable_LFunctionTrivChar₁ q s).mul (prodD s),
    fun s hs => mul_ne_zero (reg s hs) (prod_ne_zero_iff.mpr (nonvan s hs)),?_,?_⟩
  · intro χ s pole h
    obtain ⟨hr,hp⟩ := mul_ne_zero_iff.mp h
    by_cases hχ : χ = 1
    · subst χ
      have hs : s ≠ 1 := fun e => pole ⟨rfl,e⟩
      rw [LFunctionTrivChar₁, Function.update_of_ne hs] at hr
      exact (mul_ne_zero_iff.mp hr).2
    · exact prod_ne_zero_iff.mp hp χ (by simpa using hχ)
  · intro s hs
    have he := vonMangoldt.eqOn_LFunctionResidueClassAux (a:=(1:ZMod q)) isUnit_one
      (show 1 < s.re from hs)
    have hQ : (q.totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
    have hr := reg s hs.le
    have hp := prod_ne_zero_iff.mpr (nonvan s hs.le)
    have hl : logDeriv (regularProduct q) s = logDeriv (LFunctionTrivChar₁ q) s +
        ∑ χ ∈ S, logDeriv χ.LFunction s := by
      unfold regularProduct
      rw [logDeriv_mul s hr hp (differentiable_LFunctionTrivChar₁ q s) (prodD s),
        logDeriv_prod (nonvan s hs.le) (fun χ hχ => differentiable_LFunction (ntr hχ) s)]
    simp only [vonMangoldt.LFunctionResidueClassAux,ZMod.inv_one,map_one,one_mul] at he
    rw [hl]
    simp only [logDeriv_apply]
    change _*( -deriv (LFunctionTrivChar₁ q) s / LFunctionTrivChar₁ q s -
      ∑ χ ∈ S, deriv χ.LFunction s / χ.LFunction s) = _ at he
    have hx : s-1 ≠ 0 := sub_ne_zero.mpr fun e => by simp [e] at hs
    linear_combination (norm := (field_simp; ring)) -(q.totient:ℂ)*he
