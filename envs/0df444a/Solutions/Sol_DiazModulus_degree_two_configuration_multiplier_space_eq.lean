-- Prove2me | solution 1 for DiazModulus.degree_two_configuration_multiplier_space_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T11:55:53.930058+00:00
-- url     : https://prove2.me/submissions/57502ae4-6354-4c7b-a4bd-d4c1d2e2b6f9

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_quadratic_pencil_wronskian_span
import Theorems.Thm_DiazModulus_quadratic_ratio_pole_fractions_independent

open Complex ComplexConjugate

/-! # The `h`-multiplier space of a degree-two configuration is `x₀ · span y`

Let `W ⊇ H₀ = span(1, u, u⁻¹)` have dimension 5 and carry a configuration `(x, y)` with
`x₁ q(u) = x₀ p(u)`, so `h = p(u)/q(u) = x₁/x₀`. Write `Z = W ∩ h⁻¹W`, `y′ⱼ = x₀ yⱼ`,
`J = p′q − pq′` and `g_λ(α, β) = q(αq + βJ)/(u(p − λq))` at `u`. Then `y′` is free, `y′ ⊆ W` and
`h y′ = x₁ y ⊆ W`, so `span y′ ≤ Z`. **Step 1** (as in `degree_two_configuration_multiplier_complement`):
by `quadratic_ratio_pole_fractions_independent`, some `λ ∈ {0, 1, 2}` admits no non-zero `g_λ(α, β)` in
`W`. Put `E = p(u) − λq(u)`, `k₀ = q(u)/E` and `N′ = W ∩ k₀⁻¹W`. **Step 2:** if `f ∈ H₀` and `k₀ f ∈ W`,
write `u f = c + au + bu² = a′q + b′p + c′J` at `u` (`quadratic_pencil_wronskian_span`); then
`k₀ f − b′ q(u)/u = g_λ(a′ + λb′, c′) ∈ W`, so `a′ + λb′ = c′ = 0` and `f = b′E/u`. So
`N′ ∩ H₀ ⊆ Q̄·E/u`, and `dim N′ ≤ 5 + 1 − 3 = 3`. **Step 3:** `V = (E/q(u))·span y′ = (h − λ)·span y′`
is 3-dimensional and `V ≤ N′`, so `V = N′`. For `f ∈ Z`, `(h − λ) f ∈ N′ = V`; cancelling `h − λ ≠ 0`
gives `f ∈ span y′`. So `Z = span y′`, of dimension 3. -/

namespace R21a_U

open DiazModulus Polynomial

theorem tr_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem smul_def' (c : ↥Qbar) (z : ℂ) : c • z = (c : ℂ) * z := rfl

theorem aeval_ne_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (hP : P ≠ 0) : aeval u P ≠ 0 :=
  fun h => hP (transcendental_iff.1 (tr_of_not_mem hu) P h)

theorem u_ne_zero {u : ℂ} (hu : u ∉ Qbar) : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)

theorem q_ne_zero {p q : (↥Qbar)[X]} (hcop : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 2) : q ≠ 0 := by
  rintro rfl
  have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hcop)
  simp at hdeg
  omega

theorem pencil_ne_zero {p q : (↥Qbar)[X]} (hcop : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 2) (l : ↥Qbar) : p - C l * q ≠ 0 := by
  intro h
  have e : p = C l * q := sub_eq_zero.1 h
  rw [e] at hcop hdeg
  have h0 := natDegree_eq_zero_of_isUnit (isCoprime_self.1 (IsCoprime.mul_left_iff.1 hcop).2)
  have h1 := natDegree_C_mul_le l q
  omega

/-- `1, u, u⁻¹` are free over `Q̄`. -/
theorem lin3 {u : ℂ} (hu : u ∉ Qbar) {a b c : ↥Qbar} (h : (a : ℂ) + b * u + c * u⁻¹ = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hu0 := u_ne_zero hu
  have hP := transcendental_iff.1 (tr_of_not_mem hu) (C c + C a * X + C b * X ^ 2) (by
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]
    field_simp at h
    linear_combination h)
  exact ⟨by simpa using congrArg (coeff · 1) hP, by simpa using congrArg (coeff · 2) hP,
    by simpa using congrArg (coeff · 0) hP⟩

theorem H_coeffs {u w : ℂ} (hw : w ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ)) :
    ∃ a b c : ↥Qbar, w = (a : ℂ) + b * u + c * u⁻¹ := by
  obtain ⟨c₁, w₁, hw₁, rfl⟩ := Submodule.mem_span_insert.1 hw
  obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
  obtain ⟨c₃, rfl⟩ := Submodule.mem_span_singleton.1 hw₂
  exact ⟨c₁, c₂, c₃, by simp only [smul_def']; ring⟩

/-- `R(u)/u ∈ H₀` when `deg R ≤ 2`. -/
theorem quad_div_mem {u : ℂ} (hu0 : u ≠ 0) {R : (↥Qbar)[X]} (hR : R.natDegree ≤ 2) :
    aeval u R / u ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) := by
  have e : aeval u R / u = (R.coeff 1 : ℂ) + (R.coeff 2 : ℂ) * u + (R.coeff 0 : ℂ) * u⁻¹ := by
    rw [aeval_eq_sum_range' (n := 3) (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, smul_def']
    field_simp
    ring
  have hs : ∀ x ∈ ({1, u, u⁻¹} : Set ℂ), x ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) :=
    fun x hx => Submodule.subset_span hx
  have := add_mem (add_mem (Submodule.smul_mem _ (R.coeff 1) (hs 1 (by simp)))
    (Submodule.smul_mem _ (R.coeff 2) (hs u (by simp))))
    (Submodule.smul_mem _ (R.coeff 0) (hs u⁻¹ (by simp)))
  rw [e]
  simpa only [smul_def', mul_one] using this

/-- Step 1: some `λ ∈ {0, 1, 2}` admits no non-zero pole fraction in `W`. -/
theorem step1 {u : ℂ} (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) [FiniteDimensional (↥Qbar) W]
    (hW : Module.finrank (↥Qbar) W = 5) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (p q : (↥Qbar)[X]) (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 2) :
    ∃ lam : ↥Qbar, (lam = 0 ∨ lam = 1 ∨ lam = 2) ∧ ∀ α β : ↥Qbar,
      aeval u q * ((α : ℂ) * aeval u q + (β : ℂ) * aeval u (derivative p * q - p * derivative q)) /
        (u * (aeval u p - (lam : ℂ) * aeval u q)) ∈ W → α = 0 ∧ β = 0 := by
  by_contra! hc
  obtain ⟨α0, β0, hm0, hab0⟩ := hc 0 (Or.inl rfl)
  obtain ⟨α1, β1, hm1, hab1⟩ := hc 1 (Or.inr (Or.inl rfl))
  obtain ⟨α2, β2, hm2, hab2⟩ := hc 2 (Or.inr (Or.inr rfl))
  have hinj : Function.Injective (![0, 1, 2] : Fin 3 → ↥Qbar) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  set J := derivative p * q - p * derivative q with hJ
  set g0 := aeval u q * ((α0 : ℂ) * aeval u q + (β0 : ℂ) * aeval u J) /
    (u * (aeval u p - ((0 : ↥Qbar) : ℂ) * aeval u q)) with hg0
  set g1 := aeval u q * ((α1 : ℂ) * aeval u q + (β1 : ℂ) * aeval u J) /
    (u * (aeval u p - ((1 : ↥Qbar) : ℂ) * aeval u q)) with hg1
  set g2 := aeval u q * ((α2 : ℂ) * aeval u q + (β2 : ℂ) * aeval u J) /
    (u * (aeval u p - ((2 : ↥Qbar) : ℂ) * aeval u q)) with hg2
  have hv : LinearIndependent (↥Qbar) ![1, u, u⁻¹, g0, g1, g2] := by
    rw [Fintype.linearIndependent_iff]
    intro s hs
    simp only [Fin.sum_univ_six, smul_def'] at hs
    obtain ⟨ha, hb, hc, hd⟩ := DiazModulus.quadratic_ratio_pole_fractions_independent u hu p q hcop
      hdeg ![0, 1, 2] ![α0, α1, α2] ![β0, β1, β2] hinj
      (by intro i; fin_cases i <;> simp <;> tauto) (s 0) (s 1) (s 2) ![s 3, s 4, s 5] (by
        rw [← hJ, Fin.sum_univ_three]
        simp only [hg0, hg1, hg2] at hs
        simp at hs ⊢
        linear_combination hs)
    intro i
    fin_cases i
    exacts [ha, hb, hc, by simpa using congrFun hd 0, by simpa using congrFun hd 1,
      by simpa using congrFun hd 2]
  have hvW : ∀ i, (![1, u, u⁻¹, g0, g1, g2] : Fin 6 → ℂ) i ∈ W := by intro i; fin_cases i <;> assumption
  have h6 := (LinearIndependent.of_comp W.subtype
    (v := fun i => (⟨_, hvW i⟩ : W)) hv).fintype_card_le_finrank
  simp [hW] at h6

/-- `c + au + bu² = a′q(u) + b′p(u) + c′J(u)` (`quadratic_pencil_wronskian_span` at `u`). -/
theorem wr_at (u : ℂ) {p q : (↥Qbar)[X]} (hcop : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 2) (a b c : ↥Qbar) : ∃ a' b' c' : ↥Qbar,
    (c : ℂ) + a * u + b * u ^ 2 = a' * aeval u q + b' * aeval u p +
      c' * aeval u (derivative p * q - p * derivative q) := by
  obtain ⟨a', b', c', hR⟩ := DiazModulus.quadratic_pencil_wronskian_span p q hcop hdeg
    (C c + C a * X + C b * X ^ 2) (by compute_degree!)
  exact ⟨a', b', c', by
    simpa only [map_add, map_mul, map_pow, aeval_C, aeval_X, am] using congrArg (aeval u) hR⟩

/-- Step 2 on all of `N′`: if `f ∈ H₀` and `k₀ f ∈ W`, then `f ∈ Q̄·E/u`. -/
theorem hint {u : ℂ} (hu : u ∉ Qbar) {W : Submodule (↥Qbar) ℂ}
    (hHW : Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ≤ W) {p q : (↥Qbar)[X]} (hcop : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 2) (lam : ↥Qbar) (hS : ∀ α β : ↥Qbar,
      aeval u q * ((α : ℂ) * aeval u q + (β : ℂ) * aeval u (derivative p * q - p * derivative q)) /
        (u * (aeval u p - (lam : ℂ) * aeval u q)) ∈ W → α = 0 ∧ β = 0)
    {f : ℂ} (hfH : f ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ))
    (hkf : aeval u q / (aeval u p - (lam : ℂ) * aeval u q) * f ∈ W) :
    f ∈ Submodule.span Qbar {(aeval u p - (lam : ℂ) * aeval u q) / u} := by
  have hu0 := u_ne_zero hu
  have hq0 : aeval u q ≠ 0 := aeval_ne_zero hu (q_ne_zero hcop hdeg)
  have hE0 : aeval u p - (lam : ℂ) * aeval u q ≠ 0 := by
    simpa [am] using aeval_ne_zero hu (pencil_ne_zero hcop hdeg lam)
  have hQH : aeval u q / u ∈ W := hHW (quad_div_mem hu0 (hdeg ▸ le_max_right _ _))
  obtain ⟨a, b, c, rfl⟩ := H_coeffs hfH
  obtain ⟨a', b', c', hRu⟩ := wr_at u hcop hdeg a b c
  set Ju := aeval u (derivative p * q - p * derivative q) with hJu
  set Pu := aeval u p with hPu
  set Qu := aeval u q with hQu
  set E := Pu - (lam : ℂ) * Qu with hE
  have hg : Qu * (((a' + lam * b' : ↥Qbar) : ℂ) * Qu + (c' : ℂ) * Ju) / (u * E) ∈ W := by
    have e : Qu * (((a' + lam * b' : ↥Qbar) : ℂ) * Qu + (c' : ℂ) * Ju) / (u * E) =
        Qu / E * ((a : ℂ) + b * u + c * u⁻¹) - b' • (Qu / u) := by
      rw [smul_def']
      push_cast
      linear_combination (norm := skip) (-(Qu / (u * E))) * hRu
      field_simp
      rw [hE]
      ring
    rw [e]
    exact W.sub_mem hkf (W.smul_mem _ hQH)
  obtain ⟨h1', h2'⟩ := hS _ _ hg
  have h1'' : (a' : ℂ) + lam * b' = 0 := by exact_mod_cast h1'
  have h2'' : (c' : ℂ) = 0 := by exact_mod_cast h2'
  refine Submodule.mem_span_singleton.2 ⟨b', ?_⟩
  rw [smul_def']
  linear_combination (norm := skip) (-(Qu / u)) * h1'' - (Ju / u) * h2'' - (1 / u) * hRu
  field_simp
  rw [hE]
  ring

/-- `dim H₀ ≥ 3`. -/
theorem H_three {u : ℂ} (hu : u ∉ Qbar) {W : Submodule (↥Qbar) ℂ} [FiniteDimensional (↥Qbar) W]
    (hHW : Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ≤ W) :
    3 ≤ Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ)) := by
  set H := Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) with hH
  have : FiniteDimensional (↥Qbar) H := Submodule.finiteDimensional_of_le hHW
  have hm : ∀ i, (![1, u, u⁻¹] : Fin 3 → ℂ) i ∈ H := fun i => by
    fin_cases i <;> exact Submodule.subset_span (by simp)
  have hH3 := (LinearIndependent.of_comp H.subtype (v := fun i => (⟨_, hm i⟩ : H)) (by
    rw [Fintype.linearIndependent_iff]
    intro s hs
    simp only [Fin.sum_univ_three, smul_def'] at hs
    obtain ⟨h0, h1, h2⟩ := lin3 hu (a := s 0) (b := s 1) (c := s 2) (by simpa using hs)
    intro i
    fin_cases i <;> assumption)).fintype_card_le_finrank
  simpa only [Fintype.card_fin] using hH3

/-- Step 2's count: `N′ ∩ H₀` is at most a line, so `dim N′ ≤ 5 + 1 − 3`. -/
theorem N_finrank_le {u : ℂ} (hu : u ∉ Qbar) {W : Submodule (↥Qbar) ℂ} [FiniteDimensional (↥Qbar) W]
    (hW : Module.finrank (↥Qbar) W = 5) (hHW : Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ≤ W)
    {k e : ℂ} (he : e ≠ 0) (hint : ∀ f ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ),
      k * f ∈ W → f ∈ Submodule.span Qbar {e}) :
    Module.finrank (↥Qbar) ↥(W ⊓ W.comap (LinearMap.mulLeft (↥Qbar) k)) ≤ 3 := by
  have hH3 := H_three hu hHW
  set H := Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) with hH
  have hNW : W ⊓ W.comap (LinearMap.mulLeft (↥Qbar) k) ≤ W := inf_le_left
  have : FiniteDimensional (↥Qbar) ↥(W ⊓ W.comap (LinearMap.mulLeft (↥Qbar) k)) :=
    Submodule.finiteDimensional_of_le hNW
  have : FiniteDimensional (↥Qbar) H := Submodule.finiteDimensional_of_le hHW
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (W ⊓ W.comap (LinearMap.mulLeft (↥Qbar) k)) H
  have hsup : Module.finrank (↥Qbar) ↥(W ⊓ W.comap (LinearMap.mulLeft (↥Qbar) k) ⊔ H) ≤ 5 :=
    hW ▸ Submodule.finrank_mono (sup_le hNW hHW)
  have hNH : W ⊓ W.comap (LinearMap.mulLeft (↥Qbar) k) ⊓ H ≤ Submodule.span Qbar {e} := by
    rintro f ⟨⟨-, hkf⟩, hfH⟩
    exact hint f hfH hkf
  have hinf : Module.finrank (↥Qbar) ↥(W ⊓ W.comap (LinearMap.mulLeft (↥Qbar) k) ⊓ H) ≤ 1 :=
    (Submodule.finrank_mono hNH).trans (finrank_span_singleton he).le
  omega

end R21a_U

open DiazModulus R21a_U in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) [FiniteDimensional (↥Qbar) W]
    (hW : Module.finrank (↥Qbar) W = 5) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y) (hxy : ∀ i j, x i * y j ∈ W)
    (p q : (↥Qbar)[X]) (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 2)
    (hpq : x 1 * aeval u q = x 0 * aeval u p) :
    (∀ f : ℂ, (f ∈ W ∧ aeval u p / aeval u q * f ∈ W) ↔
      f ∈ Submodule.span Qbar (Set.range fun j => x 0 * y j)) ∧
    Module.finrank (↥Qbar) ↥(W ⊓ W.comap (LinearMap.mulLeft (↥Qbar) (aeval u p / aeval u q))) = 3 := by
  -- Step 1: a good `λ`; Step 2: `dim N′ ≤ 3` for `N′ = W ∩ k₀⁻¹W`
  obtain ⟨lam, -, hS⟩ := step1 hu W hW h1 hu1 hui p q hcop hdeg
  have hu0 := u_ne_zero hu
  have hq0 : aeval u q ≠ 0 := aeval_ne_zero hu (q_ne_zero hcop hdeg)
  have hE0 : aeval u p - (lam : ℂ) * aeval u q ≠ 0 := by
    simpa [am] using aeval_ne_zero hu (pencil_ne_zero hcop hdeg lam)
  have hHW : Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ≤ W := Submodule.span_le.2
    (Set.insert_subset_iff.2 ⟨h1, Set.insert_subset_iff.2 ⟨hu1, Set.singleton_subset_iff.2 hui⟩⟩)
  have hN3 := N_finrank_le hu hW hHW (div_ne_zero hE0 hu0)
    (k := aeval u q / (aeval u p - (lam : ℂ) * aeval u q))
    (fun f hf hkf => hint hu hHW hcop hdeg lam hS hf hkf)
  set Pu := aeval u p with hPu
  set Qu := aeval u q with hQu
  set E := Pu - (lam : ℂ) * Qu with hE
  -- the column `y′ = x₀ y` and its image `V = (h − λ) span y′`
  have hy'li : LinearIndependent (↥Qbar) (fun j => x 0 * y j) :=
    hy.map' (LinearMap.mulLeft (↥Qbar) (x 0))
      (LinearMap.ker_eq_bot.2 (mul_right_injective₀ (hx.ne_zero 0)))
  have hy'h : ∀ j, Pu / Qu * (x 0 * y j) = x 1 * y j := fun j => by
    rw [div_mul_eq_mul_div, div_eq_iff hq0]
    linear_combination (-(y j)) * hpq
  have hYli : LinearIndependent (↥Qbar) (fun j => E / Qu * (x 0 * y j)) :=
    hy'li.map' (LinearMap.mulLeft (↥Qbar) (E / Qu))
      (LinearMap.ker_eq_bot.2 (mul_right_injective₀ (div_ne_zero hE0 hq0)))
  -- membership in `N′` of `(h − λ) g` for `g ∈ W` with `h g ∈ W`
  have hmemN : ∀ g : ℂ, g ∈ W → Pu / Qu * g ∈ W →
      E / Qu * g ∈ W ⊓ W.comap (LinearMap.mulLeft (↥Qbar) (Qu / E)) := by
    intro g hgW hhg
    refine Submodule.mem_inf.2 ⟨?_, Submodule.mem_comap.2 ?_⟩
    · have e : E / Qu * g = Pu / Qu * g - lam • g := by
        rw [smul_def', hE, sub_div, mul_div_assoc, div_self hq0]
        ring
      rw [e]; exact W.sub_mem hhg (W.smul_mem _ hgW)
    · have e : Qu / E * (E / Qu * g) = g := by field_simp
      rw [LinearMap.mulLeft_apply, e]; exact hgW
  -- Step 3: `V = N′`
  have hVN : Submodule.span Qbar (Set.range fun j => E / Qu * (x 0 * y j)) ≤
      W ⊓ W.comap (LinearMap.mulLeft (↥Qbar) (Qu / E)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact hmemN _ (hxy 0 j) (by rw [hy'h j]; exact hxy 1 j)
  have : FiniteDimensional (↥Qbar) ↥(W ⊓ W.comap (LinearMap.mulLeft (↥Qbar) (Qu / E))) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have hVeq := Submodule.eq_of_le_of_finrank_le hVN
    (by rw [finrank_span_eq_card hYli, Fintype.card_fin]; exact hN3)
  -- `Z = span y′`
  have hZ : W ⊓ W.comap (LinearMap.mulLeft (↥Qbar) (Pu / Qu)) =
      Submodule.span Qbar (Set.range fun j => x 0 * y j) := by
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rintro f ⟨hfW, hhf⟩
      have hg := hmemN f hfW hhf
      rw [← hVeq] at hg
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hg
      refine (Submodule.mem_span_range_iff_exists_fun _).2
        ⟨c, mul_left_cancel₀ (div_ne_zero hE0 hq0) ?_⟩
      rw [← hc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [smul_def']; ring
    · rintro _ ⟨j, rfl⟩
      exact Submodule.mem_inf.2 ⟨hxy 0 j, Submodule.mem_comap.2
        (by show Pu / Qu * (x 0 * y j) ∈ W; rw [hy'h j]; exact hxy 1 j)⟩
  refine ⟨fun f => ?_, ?_⟩
  · rw [← hZ, Submodule.mem_inf, Submodule.mem_comap, LinearMap.mulLeft_apply]
  · rw [hZ, finrank_span_eq_card hy'li, Fintype.card_fin]
