-- Prove2me | solution 1 for DiazModulus.linear_subgroup_transcendence
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:10:32.304984+00:00
-- url     : https://prove2.me/submissions/f2cf282b-92a9-4328-95ac-74f98784752e

import Mathlib
import Definitions.Def_DiazModulus
import Definitions.Def_MultiplicityEstimateElem
import Theorems.Thm_DiazModulus_interp_kernel
import Theorems.Thm_DiazModulus_obstruction_1123
import Theorems.Thm_DiazModulus_params_1122_eventually
import Theorems.Thm_DiazModulus_params_exponents

open Complex ComplexConjugate

/-! # DALAG Th. 11.21 (case `d₀ ≤ n < d`): the linear subgroup theorem from a multiplicity estimate

Let `d₀ = |ι₀|`, `d₁ = |ι₁|`, `n = dim V`. `interp_kernel` (A12) gives a constant `C`. Fix
`ν = (d₀+n)/(d−n) + 1` and the curve `S₀ = ⌊S₁^{d₁/(d−n)}(log S₁)^ν⌋`, `T₀ = ⌊S₀/log S₁⌋`,
`T₁ = ⌊S₀/S₁⌋`. For all large `S₁`, `params_1122_eventually` (P1) gives `T₀, T₁ ≥ 2` and A12's
constraint at `(N₀, N₁) = (S₀, S₁)`, so A12 yields a non-zero `c` whose vanishing covers the premise
of `obstruction_1123` (O2) at the rescaled `(⌊S₀/d⌋, ⌊S₁/d⌋)`. O2 returns `(V′, φ, L₁, ℓ)` with
`(⌊S₀/d⌋+1)^ℓ (2⌊S₁/d⌋+1)^{λ′} T₀^{dim V′} T₁^{dim L₁} ≤ ℓ!·K·T₀^{d₀}T₁^{d₁}`; cancelling
`T₀^{dim V′}T₁^{dim L₁}` gives (11.23) with exponents `(ℓ, λ′, d₀′, d₁′)`, and the dimension formula for
`span w ⊓ (V′ × L₁)` gives `ℓ ≤ d₀′ + d₁′`. These four numbers range over a finite box, so one tuple
occurs for frequently many `S₁` (pigeonhole via `Filter.eventually_all_finset`). `params_exponents`
(P2) applied to that tuple gives `ℓ < d′` and `(λ′+d₁′)(d−n) ≤ d₁(d′−ℓ)`; any `S₁` of the class
supplies the witnesses. -/

namespace C14_P3
open DiazModulus Filter

theorem finrank_prod_ge {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [FiniteDimensional ℂ A] [FiniteDimensional ℂ B] (p : Submodule ℂ A) (q : Submodule ℂ B) :
    Module.finrank ℂ p + Module.finrank ℂ q ≤ Module.finrank ℂ (p.prod q) := by
  rw [← Module.finrank_prod]
  refine LinearMap.finrank_le_finrank_of_injective
    (f := LinearMap.codRestrict (p.prod q) (p.subtype.prodMap q.subtype) (fun x => ⟨x.1.2, x.2.2⟩)) ?_
  intro x y hxy
  have h1 := congrArg (fun z : ↥(p.prod q) => (z : A × B).1) hxy
  have h2 := congrArg (fun z : ↥(p.prod q) => (z : A × B).2) hxy
  exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)

theorem ell_le {ι₀ ι₁ κ₀ : Type} [Fintype ι₀] [Fintype ι₁] (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ))
    (V' : Submodule ℂ (ι₀ → ℂ)) (L₁ : Submodule ℂ (ι₁ → ℂ)) (ℓ : ℕ)
    (hℓ : ℓ + Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w) ⊓ V'.prod L₁)
      = Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w))) :
    ℓ + Module.finrank ℂ ↥V' + Module.finrank ℂ ↥L₁ ≤ Fintype.card ι₀ + Fintype.card ι₁ := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span ℂ (Set.range w)) (V'.prod L₁)
  have h2 := Submodule.finrank_le (Submodule.span ℂ (Set.range w) ⊔ V'.prod L₁)
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card] at h2
  have h3 := finrank_prod_ge V' L₁
  omega

theorem pigeon {α β : Type} {l : Filter α} [l.NeBot] (s : Finset β) (P : α → β → Prop)
    (h : ∀ᶠ x in l, ∃ t ∈ s, P x t) : ∃ t ∈ s, ∃ᶠ x in l, P x t := by
  by_contra hne
  push Not at hne
  have h2 : ∀ᶠ x in l, ∀ t ∈ s, ¬ P x t :=
    (Filter.eventually_all_finset s).2 hne
  obtain ⟨x, ⟨t, ht, hP⟩, hx⟩ := (h.and h2).exists
  exact hx t ht hP

end C14_P3

open DiazModulus C14_P3 in
theorem solution (hME : DiazModulus.MultiplicityEstimateElem)
    {ι₀ ι₁ κ₀ κ₁ : Type} [Fintype ι₀] [Fintype ι₁] [Fintype κ₀] [Fintype κ₁]
    [DecidableEq ι₀] [DecidableEq ι₁]
    (V : Submodule ℂ ((ι₀ → ℂ) × (ι₁ → ℂ))) (hV1 : 1 ≤ Module.finrank ℂ ↥V)
    (hVd : Module.finrank ℂ ↥V < Fintype.card ι₀ + Fintype.card ι₁)
    (hd0 : Fintype.card ι₀ ≤ Module.finrank ℂ ↥V)
    (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (hwV : ∀ k, w k ∈ V) (hwalg : ∀ k, (∀ h, (w k).1 h ∈ Qbar) ∧ ∀ i, (w k).2 i ∈ Qbar)
    (η : κ₁ → (ι₀ → ℂ) × (ι₁ → ℂ)) (hηV : ∀ j, η j ∈ V) (hηalg : ∀ j, (∀ h, (η j).1 h ∈ Qbar) ∧ ∀ i, (η j).2 i ∈ LogAlg) :
    ∃ (V' : Submodule ℂ (ι₀ → ℂ)) (q : ℕ) (φ : Fin q → ι₁ → ℤ) (L₁ : Submodule ℂ (ι₁ → ℂ)) (ℓ : ℕ),
      (∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0) ∧
      ℓ + Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w) ⊓ V'.prod L₁)
        = Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w)) ∧
      ℓ < (Fintype.card ι₀ - Module.finrank ℂ ↥V' + (Fintype.card ι₁ - Module.finrank ℂ ↥L₁)) ∧
      (Fintype.card κ₁ - Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : κ₁ → ℤ => fun j => (s j : ℚ)) ''
          {s : κ₁ → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
            ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1}))
          + (Fintype.card ι₁ - Module.finrank ℂ ↥L₁)) * (Fintype.card ι₀ + Fintype.card ι₁ - Module.finrank ℂ ↥V)
        ≤ Fintype.card ι₁ * ((Fintype.card ι₀ - Module.finrank ℂ ↥V' + (Fintype.card ι₁ - Module.finrank ℂ ↥L₁)) - ℓ) := by
  classical
  obtain ⟨C, hC, hA12⟩ := DiazModulus.interp_kernel V hV1 w hwV hwalg η hηV hηalg
  set d0 := Fintype.card ι₀ with hd0def
  set d1 := Fintype.card ι₁ with hd1def
  set n := Module.finrank ℂ ↥V with hndef
  have hD : (0 : ℝ) < d0 + d1 - n := by
    have : (n : ℝ) < d0 + d1 := by exact_mod_cast hVd
    linarith
  set ν : ℝ := ((d0 : ℝ) + n) / ((d0 : ℝ) + d1 - n) + 1 with hνdef
  have hν : ((d0 : ℝ) + n) / ((d0 : ℝ) + d1 - n) < ν := by rw [hνdef]; linarith
  have hν0 : 0 < ν := by
    have : 0 ≤ ((d0 : ℝ) + n) / ((d0 : ℝ) + d1 - n) := div_nonneg (by positivity) hD.le
    linarith
  have hP1 := DiazModulus.params_1122_eventually hV1 hVd hd0 C hC ν hν
  set K : ℕ := 2 ^ ((d0 + d1) * (d0 + d1 + 1) / 2) * (d0 + d1).factorial * 2 ^ d1 * d0 ^ d0
    with hK
  set Box : Finset (ℕ × ℕ × ℕ × ℕ) := Finset.range (Module.finrank ℂ
      ↥(Submodule.span ℂ (Set.range w)) + 1) ×ˢ Finset.range (Fintype.card κ₁ + 1) ×ˢ
      Finset.range (d0 + 1) ×ˢ Finset.range (d1 + 1) with hBox
  have step : ∀ᶠ S₁ : ℕ in Filter.atTop, ∃ t ∈ Box,
      (((⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ / (d0 + d1) : ℕ) : ℝ) ^ t.1 *
          ((S₁ / (d0 + d1) : ℕ) : ℝ) ^ t.2.1
        ≤ ((t.1.factorial * K : ℕ) : ℝ) * ((⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / Real.log S₁⌋₊ : ℕ) : ℝ) ^ (d0 - t.2.2.1) * ((⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / S₁⌋₊ : ℕ) : ℝ) ^ (d1 - t.2.2.2))
      ∧ t.1 + t.2.2.1 + t.2.2.2 ≤ d0 + d1 ∧ t.2.2.1 + t.2.2.2 < d0 + d1
      ∧ t.2.2.1 ≤ d0 ∧ t.2.2.2 ≤ d1
      ∧ ∃ (V' : Submodule ℂ (ι₀ → ℂ)) (q : ℕ) (φ : Fin q → ι₁ → ℤ) (L₁ : Submodule ℂ (ι₁ → ℂ)) (ℓ : ℕ),
        (∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0) ∧
        ℓ + Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w) ⊓ V'.prod L₁)
          = Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w)) ∧
        ℓ = t.1 ∧
        Fintype.card κ₁ - Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : κ₁ → ℤ => fun j => (s j : ℚ)) ''
          {s : κ₁ → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
            ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1})) = t.2.1 ∧
        Module.finrank ℂ ↥V' = t.2.2.1 ∧ Module.finrank ℂ ↥L₁ = t.2.2.2 := by
    filter_upwards [hP1] with S hS
    generalize hS0 : ⌊(S : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S ^ ν⌋₊ = S0 at hS ⊢
    generalize hT0 : ⌊(S0 : ℝ) / Real.log S⌋₊ = T0 at hS ⊢
    generalize hT1 : ⌊(S0 : ℝ) / S⌋₊ = T1 at hS ⊢
    obtain ⟨h2T0, h2T1, hcon⟩ := hS
    obtain ⟨c, hc, hvan⟩ := hA12 T0 T1 S0 S (by omega) (by omega) hcon
    have hvan' : ∀ (rₑ : ℕ) (kₑ : Fin rₑ → κ₀) (sₑ : κ₁ → ℤ),
        rₑ ≤ (d0 + d1) * (S0 / (d0 + d1)) →
        (∀ j, |sₑ j| ≤ (((d0 + d1) * (S / (d0 + d1)) : ℕ) : ℤ)) → _ :=
      fun r k s hr hs => hvan r k s (hr.trans (Nat.mul_div_le _ _))
        (fun j => (hs j).trans (by exact_mod_cast Nat.mul_div_le _ _))
    obtain ⟨V', q, φ, L₁, ℓ, hL, hℓ, hdim, hineq⟩ :=
      DiazModulus.obstruction_1123 hME w (fun j => (η j).1) (fun j i => Complex.exp ((η j).2 i))
        T0 T1 (S0 / (d0 + d1)) (S / (d0 + d1)) c (by omega) (by omega)
        (fun j i => Complex.exp_ne_zero _) hc hvan'
    have hsum := ell_le w V' L₁ ℓ hℓ
    have ha0 : Module.finrank ℂ ↥V' ≤ d0 :=
      (Submodule.finrank_le V').trans (Module.finrank_fintype_fun_eq_card ℂ).le
    have ha1 : Module.finrank ℂ ↥L₁ ≤ d1 :=
      (Submodule.finrank_le L₁).trans (Module.finrank_fintype_fun_eq_card ℂ).le
    have hpos : 0 < T0 ^ Module.finrank ℂ ↥V' * T1 ^ Module.finrank ℂ ↥L₁ :=
      Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _)
    refine ⟨(ℓ, Fintype.card κ₁ - Module.finrank ℚ ↥(Submodule.span ℚ
        ((fun s : κ₁ → ℤ => fun j => (s j : ℚ)) ''
          {s : κ₁ → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
            ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1})),
        Module.finrank ℂ ↥V', Module.finrank ℂ ↥L₁), ?_, ?_, hsum, hdim, ha0, ha1,
        V', q, φ, L₁, ℓ, hL, hℓ, rfl, rfl, rfl, rfl⟩
    · simp only [hBox, Finset.mem_product, Finset.mem_range]
      refine ⟨by omega, by omega, by omega, by omega⟩
    · dsimp only
      have hnat : (S0 / (d0 + d1)) ^ ℓ * (S / (d0 + d1)) ^ (Fintype.card κ₁ - Module.finrank ℚ
          ↥(Submodule.span ℚ ((fun s : κ₁ → ℤ => fun j => (s j : ℚ)) ''
          {s : κ₁ → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
            ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1})))
          ≤ ℓ.factorial * K * T0 ^ (d0 - Module.finrank ℂ ↥V') * T1 ^ (d1 - Module.finrank ℂ ↥L₁) := by
        refine Nat.le_of_mul_le_mul_right ?_ hpos
        calc _ ≤ (S0 / (d0 + d1) + 1) ^ ℓ * (2 * (S / (d0 + d1)) + 1) ^ (Fintype.card κ₁ -
              Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : κ₁ → ℤ => fun j => (s j : ℚ)) ''
              {s : κ₁ → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
                ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1})))
              * T0 ^ Module.finrank ℂ ↥V' * T1 ^ Module.finrank ℂ ↥L₁ := by
              rw [← mul_assoc]; gcongr <;> omega
          _ ≤ _ := hineq
          _ = _ := by rw [← pow_sub_mul_pow T0 ha0, ← pow_sub_mul_pow T1 ha1]; ring
      exact_mod_cast hnat
  obtain ⟨t, ht, H⟩ := pigeon Box _ step
  obtain ⟨S, -, hsum, hdim, ha0, ha1, V', q, φ, L₁, ℓ, hL, hℓ, hℓt, hlam, hdV, hdL⟩ := H.exists
  have hfreq := H.mono fun S hS => hS.1
  obtain ⟨hlt, hle⟩ := DiazModulus.params_exponents hVd hd0 ν hν0
    ((t.1.factorial * K : ℕ) : ℝ) t.1 t.2.1 (d0 - t.2.2.1) (d1 - t.2.2.2) (by omega) (by omega) hfreq
  refine ⟨V', q, φ, L₁, ℓ, hL, hℓ, ?_, ?_⟩
  · rw [hdV, hdL, hℓt]; exact hlt
  · rw [hlam, hdV, hdL, hℓt]; exact hle
