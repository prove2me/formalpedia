-- Prove2me | solution 1 for DiazModulus.fv_finite_approx
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T14:13:06.338203+00:00
-- url     : https://prove2.me/submissions/6f0f1557-a565-45e7-aeee-00d84d5de0be

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_fv_rho_excess
import Theorems.Thm_DiazModulus_fv_rho_sInf

open Complex ComplexConjugate

/-! # One finite-dimensional Q̄-subspace that approximates Y for every ℂ-subspace at once

Write `ρ_Z(V) = dim Z − dim (Z ∩ V)` for finite-dimensional `Z ⊆ Y`. For such `Z` let `I(Z)` be the
intersection of all `ℂ`-subspaces `V` with `ρ_Z(V) < B`; the bound for intersections of families gives
`ρ_Z(I(Z)) ≤ n·B`. With `M = n·B + 1` the number `N(Z) = M·dim I(Z) + ρ_Z(I(Z))` is at most `M·n + n·B`,
so it has a largest value, attained at some finite-dimensional `Y₀ ⊆ Y`. Monotonicity of `ρ` in `Z`
(the excess inequality at `V' = ℂⁿ`) makes `I` monotone. For `Z' = Y₀ + Y₁` maximality of `N(Y₀)` forces
`dim I(Z') = dim I(Y₀)`, hence `I(Z') = I(Y₀) =: I`, and then `ρ_{Z'}(I) ≤ ρ_{Y₀}(I)`. If `I ⊄ V` then
`ρ_{Y₀}(V) ≥ B` by the definition of `I`. If `I ⊆ V`, the excess inequality for `Y₀ ⊆ Z'` and `I ⊆ V`
gives `ρ_{Z'}(V) ≤ ρ_{Y₀}(V)`, and monotonicity gives `ρ_{Y₁}(V) ≤ ρ_{Z'}(V)`. In both cases
`min (ρ_{Y₁}(V), B) ≤ ρ_{Y₀}(V)`. -/

namespace RC4_FA
open DiazModulus

/-- `dim Z − dim (Z ∩ W)`, the codimension of `Z ∩ W` in `Z`. -/
noncomputable def faRho {n : ℕ} (Z : Submodule (↥Qbar) (Fin n → ℂ)) (W : Submodule ℂ (Fin n → ℂ)) :
    ℕ :=
  Module.finrank (↥Qbar) ↥Z - Module.finrank (↥Qbar) ↥(Z ⊓ W.restrictScalars (↥Qbar))

theorem faRho_top {n : ℕ} (Z : Submodule (↥Qbar) (Fin n → ℂ)) : faRho Z ⊤ = 0 := by
  unfold faRho
  rw [Submodule.restrictScalars_top]
  have : Z ⊓ (⊤ : Submodule (↥Qbar) (Fin n → ℂ)) = Z := inf_top_eq Z
  rw [this, Nat.sub_self]

theorem faRho_mono {n : ℕ} (Z Z' : Submodule (↥Qbar) (Fin n → ℂ)) [FiniteDimensional (↥Qbar) ↥Z']
    (h : Z ≤ Z') (V : Submodule ℂ (Fin n → ℂ)) : faRho Z V ≤ faRho Z' V := by
  have e : faRho Z' ⊤ + faRho Z V ≤ faRho Z ⊤ + faRho Z' V :=
    DiazModulus.fv_rho_excess Z Z' h V ⊤ le_top
  rw [faRho_top, faRho_top] at e
  omega

end RC4_FA

open DiazModulus RC4_FA in
theorem solution {n : ℕ} (Y : Submodule (↥Qbar) (Fin n → ℂ)) (B : ℕ) :
    ∃ Y₀ : Submodule (↥Qbar) (Fin n → ℂ), Y₀ ≤ Y ∧ FiniteDimensional (↥Qbar) ↥Y₀ ∧
      ∀ (V : Submodule ℂ (Fin n → ℂ)) (Y₁ : Submodule (↥Qbar) (Fin n → ℂ)),
        Y₁ ≤ Y → FiniteDimensional (↥Qbar) ↥Y₁ →
        min (Module.finrank (↥Qbar) ↥Y₁ -
              Module.finrank (↥Qbar) ↥(Y₁ ⊓ V.restrictScalars (↥Qbar))) B ≤
          Module.finrank (↥Qbar) ↥Y₀ -
            Module.finrank (↥Qbar) ↥(Y₀ ⊓ V.restrictScalars (↥Qbar)) := by
  classical
  let I : Submodule (↥Qbar) (Fin n → ℂ) → Submodule ℂ (Fin n → ℂ) :=
    fun Z => sInf {V | faRho Z V < B}
  let Nf : Submodule (↥Qbar) (Fin n → ℂ) → ℕ :=
    fun Z => (n * B + 1) * Module.finrank ℂ ↥(I Z) + faRho Z (I Z)
  have hIb : ∀ Z : Submodule (↥Qbar) (Fin n → ℂ), FiniteDimensional (↥Qbar) ↥Z →
      faRho Z (I Z) ≤ n * B := by
    intro Z hf
    exact DiazModulus.fv_rho_sInf Z {V | faRho Z V < B} B (fun V hV => le_of_lt hV)
  have hdim : ∀ Z : Submodule (↥Qbar) (Fin n → ℂ), Module.finrank ℂ ↥(I Z) ≤ n := by
    intro Z
    have := Submodule.finrank_le (I Z)
    simpa [Module.finrank_fin_fun] using this
  have hNb : ∀ Z : Submodule (↥Qbar) (Fin n → ℂ), FiniteDimensional (↥Qbar) ↥Z →
      Nf Z ≤ (n * B + 1) * n + n * B := by
    intro Z hf
    have h1 := hIb Z hf
    have h2 := Nat.mul_le_mul_left (n * B + 1) (hdim Z)
    show (n * B + 1) * Module.finrank ℂ ↥(I Z) + faRho Z (I Z) ≤ _
    omega
  have Imono : ∀ Z Z' : Submodule (↥Qbar) (Fin n → ℂ), FiniteDimensional (↥Qbar) ↥Z' →
      Z ≤ Z' → I Z ≤ I Z' := by
    intro Z Z' hf h
    apply sInf_le_sInf
    intro V hV
    exact lt_of_le_of_lt (faRho_mono Z Z' h V) hV
  let S : Set ℕ := {k | ∃ Z, Z ≤ Y ∧ FiniteDimensional (↥Qbar) ↥Z ∧ Nf Z = k}
  have hne : S.Nonempty := ⟨Nf ⊥, ⊥, bot_le, inferInstance, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨(n * B + 1) * n + n * B, ?_⟩
    rintro k ⟨Z, -, hf, rfl⟩
    exact hNb Z hf
  obtain ⟨Y₀, hY₀Y, hf₀, hY₀N⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ Z, Z ≤ Y → FiniteDimensional (↥Qbar) ↥Z → Nf Z ≤ Nf Y₀ := by
    intro Z hZ hf
    rw [hY₀N]
    exact le_csSup hbdd ⟨Z, hZ, hf, rfl⟩
  refine ⟨Y₀, hY₀Y, hf₀, ?_⟩
  intro V Y₁ hY₁ hf₁
  change min (faRho Y₁ V) B ≤ faRho Y₀ V
  have hfZ' : FiniteDimensional (↥Qbar) ↥(Y₀ ⊔ Y₁) := Submodule.finiteDimensional_sup _ _
  have hZ'Y : Y₀ ⊔ Y₁ ≤ Y := sup_le hY₀Y hY₁
  have hIle : I Y₀ ≤ I (Y₀ ⊔ Y₁) := Imono _ _ hfZ' le_sup_left
  have hmZ := hmax _ hZ'Y hfZ'
  have hr0 := hIb Y₀ hf₀
  have hdle : Module.finrank ℂ ↥(I Y₀) ≤ Module.finrank ℂ ↥(I (Y₀ ⊔ Y₁)) :=
    Submodule.finrank_mono hIle
  have hdge : Module.finrank ℂ ↥(I (Y₀ ⊔ Y₁)) ≤ Module.finrank ℂ ↥(I Y₀) := by
    by_contra hcon
    push Not at hcon
    have hm := Nat.mul_le_mul_left (n * B + 1) (Nat.succ_le_of_lt hcon)
    rw [Nat.mul_succ] at hm
    change (n * B + 1) * Module.finrank ℂ ↥(I (Y₀ ⊔ Y₁)) + faRho (Y₀ ⊔ Y₁) (I (Y₀ ⊔ Y₁)) ≤
      (n * B + 1) * Module.finrank ℂ ↥(I Y₀) + faRho Y₀ (I Y₀) at hmZ
    omega
  have hIeq : I Y₀ = I (Y₀ ⊔ Y₁) := Submodule.eq_of_le_of_finrank_le hIle hdge
  have hreq : faRho (Y₀ ⊔ Y₁) (I Y₀) ≤ faRho Y₀ (I Y₀) := by
    change (n * B + 1) * Module.finrank ℂ ↥(I (Y₀ ⊔ Y₁)) + faRho (Y₀ ⊔ Y₁) (I (Y₀ ⊔ Y₁)) ≤
      (n * B + 1) * Module.finrank ℂ ↥(I Y₀) + faRho Y₀ (I Y₀) at hmZ
    rw [← hIeq] at hmZ
    omega
  by_cases hIV : I Y₀ ≤ V
  · have e1 : faRho (Y₀ ⊔ Y₁) V + faRho Y₀ (I Y₀) ≤ faRho Y₀ V + faRho (Y₀ ⊔ Y₁) (I Y₀) :=
      DiazModulus.fv_rho_excess Y₀ (Y₀ ⊔ Y₁) le_sup_left (I Y₀) V hIV
    have e2 := faRho_mono Y₁ (Y₀ ⊔ Y₁) le_sup_right V
    have e3 := min_le_left (faRho Y₁ V) B
    omega
  · have hB : B ≤ faRho Y₀ V := by
      by_contra h
      push Not at h
      exact hIV (sInf_le h)
    exact (min_le_right _ _).trans hB
