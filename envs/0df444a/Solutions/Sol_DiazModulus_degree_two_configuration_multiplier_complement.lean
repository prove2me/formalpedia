-- Prove2me | solution 1 for DiazModulus.degree_two_configuration_multiplier_complement
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:29:37.131373+00:00
-- url     : https://prove2.me/submissions/c5d5878d-689b-4e10-ae51-16c7e8843839

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_quadratic_pencil_wronskian_span
import Theorems.Thm_DiazModulus_quadratic_ratio_pole_fractions_independent

open Complex ComplexConjugate

/-! # A multiplier complement of `H₀` in a degree-two configuration space

Write `H₀ = span(1, u, u⁻¹)`, `J = p′q − pq′` and `g_λ(α, β) = q(αq + βJ)/(u(p − λq))` at `u`.
**Step 1.** If each `λ ∈ {0, 1, 2}` had some `(α, β) ≠ 0` with `g_λ(α, β) ∈ W`, then
`quadratic_ratio_pole_fractions_independent` would make `1, u, u⁻¹` and the three `g_λ` six
independent vectors of the 5-dimensional `W`. So fix `λ ∈ {0, 1, 2}` with no such pair, and put
`E = p(u) − λq(u)`, `k₀ = q(u)/E`. **Step 2.** `Yⱼ = (E/q(u))·yⱼ = h yⱼ − λ yⱼ` lie in `W`,
are independent, and `k₀ Yⱼ = yⱼ ∈ W`, so `k₀ V ⊆ W` for `V = span Y`. If `f ∈ V ∩ H₀`, then
`u f = c + au + bu²`, and `quadratic_pencil_wronskian_span` writes this as `a′q + b′p + c′J` at `u`.
Then `k₀ f − b′ q(u)/u = g_λ(a′ + λb′, c′) ∈ W`, so `a′ + λb′ = c′ = 0` and `f = b′·E/u`: hence
`V ∩ H₀ ⊆ Q̄·E/u`. **Step 3.** `dim (V + H₀) = 3 + 3 − dim (V ∩ H₀) ≥ 5 = dim W`, so
`V + H₀ = W` and `V ∩ H₀ ≠ 0`. A non-zero `f = Σ cⱼYⱼ ∈ V ∩ H₀` has some `cⱼ ≠ 0`; the other two
`Yᵢ` are `g₁, g₂`: `Yⱼ ∈ span(f, g₁, g₂)`, so `W = span(1, u, u⁻¹, g₁, g₂)`, and `k₀ gᵢ ∈ W`. -/

namespace R20_mult

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

theorem third_mem {S : Submodule (↥Qbar) ℂ} {f x y z : ℂ} {a b c : ↥Qbar} (hc : c ≠ 0)
    (hf : f ∈ S) (hx : x ∈ S) (hy : y ∈ S) (he : f = a * x + b * y + c * z) : z ∈ S := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have e : z = c⁻¹ • (f - a • x - b • y) := by
    subst he
    simp only [smul_def']
    push_cast
    field_simp
    ring
  rw [e]
  exact S.smul_mem _ (S.sub_mem (S.sub_mem hf (S.smul_mem _ hx)) (S.smul_mem _ hy))

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
  have hvW : ∀ i, (![1, u, u⁻¹, g0, g1, g2] : Fin 6 → ℂ) i ∈ W := by
    intro i
    fin_cases i <;> assumption
  have h6 := (LinearIndependent.of_comp W.subtype
    (v := fun i => (⟨_, hvW i⟩ : W)) hv).fintype_card_le_finrank
  simp [hW] at h6

/-- Step 3, last move: drop the `Yⱼ` with `cⱼ ≠ 0`. -/
theorem final {u k f : ℂ} {W : Submodule (↥Qbar) ℂ} {Y : Fin 3 → ℂ} (hkY : ∀ m, k * Y m ∈ W)
    (hHW : Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ≤ W)
    (hVH : Submodule.span Qbar (Set.range Y) ⊔ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) = W)
    (hfH : f ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ)) (i₁ i₂ j : Fin 3)
    (hcov : ∀ m, m = i₁ ∨ m = i₂ ∨ m = j) {a b c : ↥Qbar} (hc : c ≠ 0)
    (he : f = a * Y i₁ + b * Y i₂ + c * Y j) :
    ∃ g₁ g₂ : ℂ, W = Submodule.span Qbar ({1, u, u⁻¹, g₁, g₂} : Set ℂ) ∧ k * g₁ ∈ W ∧
      k * g₂ ∈ W := by
  have hYW : ∀ m, Y m ∈ W := fun m => hVH ▸ Submodule.mem_sup_left (Submodule.subset_span ⟨m, rfl⟩)
  refine ⟨Y i₁, Y i₂, le_antisymm ?_ ?_, hkY _, hkY _⟩
  · have hHS : Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ≤
        Submodule.span Qbar ({1, u, u⁻¹, Y i₁, Y i₂} : Set ℂ) :=
      Submodule.span_mono fun x hx => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto
    have h₁ : Y i₁ ∈ Submodule.span Qbar ({1, u, u⁻¹, Y i₁, Y i₂} : Set ℂ) :=
      Submodule.subset_span (by simp)
    have h₂ : Y i₂ ∈ Submodule.span Qbar ({1, u, u⁻¹, Y i₁, Y i₂} : Set ℂ) :=
      Submodule.subset_span (by simp)
    have h₃ := third_mem hc (hHS hfH) h₁ h₂ he
    rw [← hVH]
    refine sup_le (Submodule.span_le.2 ?_) hHS
    rintro _ ⟨m, rfl⟩
    rcases hcov m with rfl | rfl | rfl <;> assumption
  · refine Submodule.span_le.2 fun x hx => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      first | exact hYW _ | exact hHW (Submodule.subset_span (by simp))

end R20_mult

open DiazModulus R20_mult in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) [FiniteDimensional (↥Qbar) W]
    (hW : Module.finrank (↥Qbar) W = 5) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (p q : (↥Qbar)[X]) (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 2)
    (y : Fin 3 → ℂ) (hy : LinearIndependent (↥Qbar) y) (hyW : ∀ j, y j ∈ W)
    (hyh : ∀ j, aeval u p / aeval u q * y j ∈ W) :
    ∃ lam : ↥Qbar, (lam = 0 ∨ lam = 1 ∨ lam = 2) ∧ ∃ g₁ g₂ : ℂ,
      W = Submodule.span Qbar ({1, u, u⁻¹, g₁, g₂} : Set ℂ) ∧
      aeval u q / (aeval u p - (lam : ℂ) * aeval u q) * g₁ ∈ W ∧
      aeval u q / (aeval u p - (lam : ℂ) * aeval u q) * g₂ ∈ W := by
  -- Step 1: a good `λ`
  obtain ⟨lam, hlam, hS⟩ := step1 hu W hW h1 hu1 hui p q hcop hdeg
  refine ⟨lam, hlam, ?_⟩
  -- Step 2: `V = span Y` with `k₀ V ⊆ W`, and `V ∩ H₀ ⊆ Q̄·E/u`
  have hu0 := u_ne_zero hu
  have hq0 : aeval u q ≠ 0 := aeval_ne_zero hu (q_ne_zero hcop hdeg)
  have hE0 : aeval u p - (lam : ℂ) * aeval u q ≠ 0 := by
    simpa [am] using aeval_ne_zero hu (pencil_ne_zero hcop hdeg lam)
  have hq2 : q.natDegree ≤ 2 := hdeg ▸ le_max_right _ _
  set J := derivative p * q - p * derivative q with hJ
  set Pu := aeval u p with hPu
  set Qu := aeval u q with hQu
  set Ju := aeval u J with hJu
  set E := Pu - (lam : ℂ) * Qu with hE
  set k₀ := Qu / E with hk₀
  set H := Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) with hH
  have hHW : H ≤ W := Submodule.span_le.2 (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption)
  set Y : Fin 3 → ℂ := fun j => E / Qu * y j with hY
  have hYW : ∀ j, Y j ∈ W := fun j => by
    have e : Y j = Pu / Qu * y j - lam • y j := by
      simp only [hY, smul_def', hE]
      field_simp
    rw [e]
    exact W.sub_mem (hyh j) (W.smul_mem _ (hyW j))
  have hkY : ∀ j, k₀ * Y j = y j := fun j => by
    simp only [hY, hk₀]
    field_simp
  have hYli : LinearIndependent (↥Qbar) Y :=
    hy.map' (LinearMap.mulLeft (↥Qbar) (E / Qu))
      (LinearMap.ker_eq_bot.2 (mul_right_injective₀ (div_ne_zero hE0 hq0)))
  set V := Submodule.span Qbar (Set.range Y) with hV
  have hVW : V ≤ W := Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hYW j)
  have hkV : ∀ f ∈ V, k₀ * f ∈ W := by
    intro f hf
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hf
    rw [Finset.mul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_def', mul_left_comm, hkY, ← smul_def']
    exact W.smul_mem (c j) (hyW j)
  have hint : V ⊓ H ≤ Submodule.span Qbar {E / u} := by
    rintro f ⟨hfV, hfH⟩
    obtain ⟨a, b, c, rfl⟩ := H_coeffs hfH
    obtain ⟨a', b', c', hR⟩ := DiazModulus.quadratic_pencil_wronskian_span p q hcop hdeg
      (C c + C a * X + C b * X ^ 2) (by compute_degree!)
    rw [← hJ] at hR
    have hRu : (c : ℂ) + a * u + b * u ^ 2 = a' * Qu + b' * Pu + c' * Ju := by
      simpa only [map_add, map_mul, map_pow, aeval_C, aeval_X, am] using congrArg (aeval u) hR
    have hQH : Qu / u ∈ W := hHW (quad_div_mem hu0 hq2)
    have hg : Qu * (((a' + lam * b' : ↥Qbar) : ℂ) * Qu + (c' : ℂ) * Ju) / (u * E) ∈ W := by
      have e : Qu * (((a' + lam * b' : ↥Qbar) : ℂ) * Qu + (c' : ℂ) * Ju) / (u * E) =
          k₀ * ((a : ℂ) + b * u + c * u⁻¹) - b' • (Qu / u) := by
        rw [smul_def']
        push_cast
        linear_combination (norm := skip) (-(Qu / (u * E))) * hRu
        rw [hk₀]
        field_simp
        rw [hE]
        ring
      rw [e]
      exact W.sub_mem (hkV _ hfV) (W.smul_mem _ hQH)
    obtain ⟨h1', h2'⟩ := hS _ _ hg
    have h1'' : (a' : ℂ) + lam * b' = 0 := by exact_mod_cast h1'
    have h2'' : (c' : ℂ) = 0 := by exact_mod_cast h2'
    refine Submodule.mem_span_singleton.2 ⟨b', ?_⟩
    rw [smul_def']
    linear_combination (norm := skip) (-(Qu / u)) * h1'' - (Ju / u) * h2'' - (1 / u) * hRu
    field_simp
    rw [hE]
    ring
  -- Step 3: the dimension count
  have : FiniteDimensional (↥Qbar) V := Submodule.finiteDimensional_of_le hVW
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
  simp only [Fintype.card_fin] at hH3
  have hV3 : Module.finrank (↥Qbar) V = 3 := by
    rw [hV, finrank_span_eq_card hYli]
    simp
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq V H
  have hsup : Module.finrank (↥Qbar) ↥(V ⊔ H) ≤ 5 := hW ▸ Submodule.finrank_mono (sup_le hVW hHW)
  have hinf : Module.finrank (↥Qbar) ↥(V ⊓ H) ≤ 1 :=
    (Submodule.finrank_mono hint).trans
      (finrank_span_singleton (div_ne_zero hE0 hu0)).le
  have hVH : V ⊔ H = W := Submodule.eq_of_le_of_finrank_le (sup_le hVW hHW) (by omega)
  have hne : V ⊓ H ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hsum
    omega
  obtain ⟨f, ⟨hfV, hfH⟩, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hfV
  rw [Fin.sum_univ_three] at hc
  simp only [smul_def'] at hc
  have hkW : ∀ m, k₀ * Y m ∈ W := fun m => by rw [hkY m]; exact hyW m
  have hc' : c 0 ≠ 0 ∨ c 1 ≠ 0 ∨ c 2 ≠ 0 := by
    by_contra hn
    simp only [not_or, not_not] at hn
    apply hf0
    rw [← hc, hn.1, hn.2.1, hn.2.2]
    simp
  rcases hc' with h | h | h
  · exact final hkW hHW hVH hfH 1 2 0 (by decide) (a := c 1) (b := c 2) h (by rw [← hc]; ring)
  · exact final hkW hHW hVH hfH 0 2 1 (by decide) (a := c 0) (b := c 2) h (by rw [← hc]; ring)
  · exact final hkW hHW hVH hfH 0 1 2 (by decide) (a := c 0) (b := c 1) h hc.symm

