-- Prove2me | solution 1 for DiazModulus.power_hull_strong_six_exp_configuration_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T12:35:36.315901+00:00
-- url     : https://prove2.me/submissions/173fff46-06cb-4498-8931-34451c778839

import Mathlib
import Definitions.Def_DiazModulus

/-!
# Strong six exponentials configurations in the power hull

For `u ∉ Q̄` and `k ≥ 1`, let `V_k = Q̄u⁻ᵏ + Q̄u⁻¹ + Q̄ + Q̄u + Q̄uᵏ`. Free `x ∈ ℂ²`, `y ∈ ℂ³`
(over `Q̄`) with all six products `xᵢyⱼ ∈ V_k` exist exactly when `k = 2` or `k = 3`. At a
candidate `u`, this is why Roy's strong six exponentials theorem, fed with the candidate's own data,
excludes `u²` and `u³` from `ℒ̃` and no higher power.

* **Existence.** `k = 2`: `x = (1, u)`, `y = (u⁻¹, 1, u)`. `k = 3`: `x = (u, u⁻¹)`,
  `y = (1, u⁻², u²)`. Freeness: `u` is transcendental over `Q̄` (`three_terms`).
* **Non-existence for `k = 1` and `k ≥ 4`.** Multiplying by `uᵏ` turns `V_k` into the
  polynomials supported on `E = {0, k-1, k, k+1, 2k}` (`hull_poly`). Write `uᵏx₁yⱼ = Aⱼ(u)`,
  `uᵏx₂yⱼ = Bⱼ(u)`. For `F = Σ cⱼAⱼ` and `G = Σ cⱼBⱼ`, the order at `0` satisfies
  `ord G(c) = ord F(c) + δ` with `δ` independent of `c`, and `δ ≠ 0` after replacing `B` by
  `B - lA` (`core`). So `ord F(c) ∈ {t ∈ E : t + δ ∈ E}`, a set of at most two exponents
  (`comb`); a non-zero `c` killing the coefficients of `F(c)` at both of them
  (`exists_kill`, three unknowns against two equations) is a contradiction.
-/

open Complex ComplexConjugate Polynomial

namespace D6_power_hull

open DiazModulus

/-! ## Polynomials supported on an exponent set -/

section supp

variable {K : Type*} [Field K]

/-- The polynomials whose exponents all lie in `S`. -/
def supp (S : Set ℕ) : Submodule K K[X] where
  carrier := {P | ∀ n ∉ S, P.coeff n = 0}
  add_mem' ha hb n hn := by rw [coeff_add, ha n hn, hb n hn, add_zero]
  zero_mem' n _ := coeff_zero n
  smul_mem' c P hP n hn := by rw [coeff_smul, hP n hn, smul_zero]

theorem X_pow_mem_supp {S : Set ℕ} {m : ℕ} (hm : m ∈ S) : (X ^ m : K[X]) ∈ supp S := by
  intro n hn
  rw [coeff_X_pow, if_neg]
  rintro rfl
  exact hn hm

/-- The order at `0` of a non-zero polynomial supported on `S` lies in `S`. -/
theorem natTrailingDegree_mem {S : Set ℕ} {P : K[X]} (hP : P ∈ supp S) (h0 : P ≠ 0) :
    P.natTrailingDegree ∈ S := by
  by_contra h
  exact trailingCoeff_nonzero_iff_nonzero.2 h0 (hP _ h)

/-- Three against two: a non-zero combination of three polynomials kills two given
coefficients. -/
theorem exists_kill (A : Fin 3 → K[X]) (a b : ℕ) :
    ∃ c : Fin 3 → K, c ≠ 0 ∧ (∑ j, c j • A j).coeff a = 0 ∧ (∑ j, c j • A j).coeff b = 0 := by
  let v : Fin 3 → Fin 2 → K := fun j => ![(A j).coeff a, (A j).coeff b]
  have hv : ¬ LinearIndependent K v := fun h => by
    have := h.fintype_card_le_finrank
    simp at this
  obtain ⟨c, hc, j, hj⟩ := Fintype.not_linearIndependent_iff.1 hv
  refine ⟨c, fun h => hj (by simp [h]), ?_, ?_⟩
  · simpa [v, finsetSum_coeff] using congrFun hc 0
  · simpa [v, finsetSum_coeff] using congrFun hc 1

end supp

/-! ## The exponent set and the finite check -/

/-- The exponents of `uᵏ · (Q̄u⁻ᵏ + Q̄u⁻¹ + Q̄ + Q̄u + Q̄uᵏ)`. -/
def E (k : ℕ) : Set ℕ := {0, k - 1, k, k + 1, 2 * k}

/-- For `k = 1` or `k ≥ 4` and a non-zero shift `s - t₀`, at most two exponents `t ∈ E` have
`t + s - t₀ ∈ E`. -/
theorem comb {k s t0 : ℕ} (hk : k = 1 ∨ 4 ≤ k) (hs : s ≠ t0) :
    ∃ a b : ℕ, ∀ t t', t ∈ E k → t' ∈ E k → t + s = t' + t0 → t = a ∨ t = b := by
  simp only [E, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hk with rfl | hk <;> rcases lt_or_gt_of_ne hs with h | h
  · exact ⟨1, 2, fun t t' ht ht' e => by omega⟩
  · exact ⟨0, 1, fun t t' ht ht' e => by omega⟩
  · by_cases h2 : t0 ≤ s + 2
    · exact ⟨k, k + 1, fun t t' ht ht' e => by omega⟩
    · exact ⟨2 * k, t0 - s, fun t t' ht ht' e => by omega⟩
  · by_cases h2 : s ≤ t0 + 2
    · exact ⟨k - 1, k, fun t t' ht ht' e => by omega⟩
    · exact ⟨0, 2 * k - (s - t0), fun t t' ht ht' e => by omega⟩

/-! ## The core: orders at `0` -/

section core

variable {K : Type*} [Field K]

/-- The order argument. `A`, `B` are three polynomials each, supported on `E k`; the
combinations `F c = Σ cⱼAⱼ` are non-zero for `c ≠ 0`, so are `G c - l F c` with
`G c = Σ cⱼBⱼ`, and `F c · G d = G c · F d`. This is impossible for `k = 1` or `k ≥ 4`. -/
theorem core {k : ℕ} (hk : k = 1 ∨ 4 ≤ k) (A B : Fin 3 → K[X])
    (hA : ∀ j, A j ∈ supp (E k)) (hB : ∀ j, B j ∈ supp (E k))
    (hA0 : ∀ c : Fin 3 → K, c ≠ 0 → ∑ j, c j • A j ≠ 0)
    (hBA0 : ∀ (l : K) (c : Fin 3 → K), c ≠ 0 → ∑ j, c j • B j - C l * ∑ j, c j • A j ≠ 0)
    (hcross : ∀ c d : Fin 3 → K,
      (∑ j, c j • A j) * ∑ j, d j • B j = (∑ j, c j • B j) * ∑ j, d j • A j) :
    False := by
  have hFmem : ∀ c : Fin 3 → K, ∑ j, c j • A j ∈ supp (E k) := fun c =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hA j)
  have hGmem : ∀ c : Fin 3 → K, ∑ j, c j • B j ∈ supp (E k) := fun c =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hB j)
  -- a reference vector `d`, and `t₀ = ord (F d)`
  let d : Fin 3 → K := fun _ => 1
  have hd : d ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  have hFd := hA0 d hd
  obtain ⟨t0, ht0⟩ : ∃ t0, (∑ j, d j • A j).natTrailingDegree = t0 := ⟨_, rfl⟩
  have htc : (∑ j, d j • A j).coeff t0 ≠ 0 := by
    rw [← ht0]; exact trailingCoeff_nonzero_iff_nonzero.2 hFd
  -- shift `B` by `l A` so that the partner of `F d` has no term in degree `t₀`
  obtain ⟨l, hl⟩ : ∃ l, l = (∑ j, d j • B j).coeff t0 / (∑ j, d j • A j).coeff t0 := ⟨_, rfl⟩
  let H : (Fin 3 → K) → K[X] := fun c => ∑ j, c j • B j - C l * ∑ j, c j • A j
  have hHmem : ∀ c, H c ∈ supp (E k) := fun c =>
    Submodule.sub_mem _ (hGmem c) (by rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (hFmem c))
  have hH0 : ∀ c, c ≠ 0 → H c ≠ 0 := hBA0 l
  have hHd : (H d).coeff t0 = 0 := by
    simp only [H, coeff_sub, coeff_C_mul, hl]
    rw [div_mul_cancel₀ _ htc, sub_self]
  have hs : (H d).natTrailingDegree ≠ t0 := fun h =>
    trailingCoeff_nonzero_iff_nonzero.2 (hH0 d hd) (by rw [trailingCoeff, h, hHd])
  -- `ord (F c) + ord (H d) = ord (H c) + ord (F d)`
  have hord : ∀ c, c ≠ 0 →
      (∑ j, c j • A j).natTrailingDegree + (H d).natTrailingDegree =
        (H c).natTrailingDegree + t0 := by
    intro c hc
    have e : (∑ j, c j • A j) * H d = H c * ∑ j, d j • A j := by
      simp only [H]
      rw [mul_sub, sub_mul, hcross c d]
      ring
    have := congrArg natTrailingDegree e
    rwa [natTrailingDegree_mul (hA0 c hc) (hH0 d hd), natTrailingDegree_mul (hH0 c hc) hFd,
      ht0] at this
  obtain ⟨a, b, hab⟩ := comb hk hs
  obtain ⟨c, hc, hca, hcb⟩ := exists_kill A a b
  have hne := trailingCoeff_nonzero_iff_nonzero.2 (hA0 c hc)
  rcases hab _ _ (natTrailingDegree_mem (hFmem c) (hA0 c hc))
      (natTrailingDegree_mem (hHmem c) (hH0 c hc)) (hord c hc) with h | h
  · exact hne (by rw [trailingCoeff, h]; exact hca)
  · exact hne (by rw [trailingCoeff, h]; exact hcb)

end core

/-! ## Transcendence and the hull -/

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes: `u` is transcendental over `ℚ`,
hence over `Q̄`, which is algebraic over `ℚ`. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem ne_zero_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : u ≠ 0 :=
  fun h => hu (h ▸ Subfield.zero_mem _)

/-- Multiplying the hull by `uᵏ` lands in the polynomials supported on `E k`. -/
theorem hull_poly {u : ℂ} (hu0 : u ≠ 0) {k : ℕ} (hk : 1 ≤ k) {v : ℂ}
    (hv : v ∈ Submodule.span Qbar ({(u ^ k)⁻¹, u⁻¹, 1, u, u ^ k} : Set ℂ)) :
    ∃ P ∈ supp (K := ↥Qbar) (E k), aeval u P = u ^ k * v := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  let L : (↥Qbar)[X] →ₗ[↥Qbar] ℂ :=
    LinearMap.mulLeft (↥Qbar) (u ^ (m + 1))⁻¹ ∘ₗ (aeval u).toLinearMap
  have key : ∀ n ∈ E (m + 1), (u ^ (m + 1))⁻¹ * u ^ n ∈ (supp (E (m + 1))).map L :=
    fun n hn => ⟨X ^ n, X_pow_mem_supp hn, by simp [L]⟩
  have hum : u ^ (m + 1) ≠ 0 := pow_ne_zero _ hu0
  have gen : ∀ n ∈ E (m + 1), ∀ z, (u ^ (m + 1))⁻¹ * u ^ n = z →
      z ∈ ((supp (E (m + 1))).map L : Set ℂ) := fun n hn z e => e ▸ key n hn
  have hle : Submodule.span Qbar ({(u ^ (m + 1))⁻¹, u⁻¹, 1, u, u ^ (m + 1)} : Set ℂ) ≤
      (supp (E (m + 1))).map L := by
    rw [Submodule.span_le]
    rintro z (rfl | rfl | rfl | rfl | rfl)
    · exact gen 0 (by simp [E]) _ (by simp)
    · exact gen m (by simp [E]) _ (by field_simp; ring)
    · exact gen (m + 1) (by simp [E]) _ (inv_mul_cancel₀ hum)
    · exact gen (m + 2) (by simp [E]) _ (by field_simp; ring)
    · exact gen (2 * (m + 1)) (by simp [E]) _ (by field_simp; ring)
  obtain ⟨P, hP, hPv⟩ := hle hv
  refine ⟨P, hP, ?_⟩
  simp only [L, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply] at hPv
  rw [← hPv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hu0), one_mul]

/-- Non-existence for `k = 1` and `k ≥ 4`. -/
theorem no_config {u : ℂ} (hu : u ∉ Qbar) {k : ℕ} (hk1 : 1 ≤ k) (hk : k = 1 ∨ 4 ≤ k)
    {x : Fin 2 → ℂ} {y : Fin 3 → ℂ} (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y)
    (hxy : ∀ i j, x i * y j ∈ Submodule.span Qbar ({(u ^ k)⁻¹, u⁻¹, 1, u, u ^ k} : Set ℂ)) :
    False := by
  have hu0 := ne_zero_of_not_mem hu
  choose P hP hPe using fun i j => hull_poly hu0 hk1 (hxy i j)
  have hev : ∀ i (c : Fin 3 → ↥Qbar),
      aeval u (∑ j, c j • P i j) = u ^ k * x i * ∑ j, c j • y j := by
    intro i c
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hPe, mul_smul_comm, mul_assoc]
  have hY : ∀ c : Fin 3 → ↥Qbar, c ≠ 0 → ∑ j, c j • y j ≠ 0 := fun c hc h =>
    hc (funext (Fintype.linearIndependent_iff.1 hy c h))
  have hx1 : ∀ l : ↥Qbar, x 1 - l • x 0 ≠ 0 := by
    intro l h
    have := Fintype.linearIndependent_iff.1 hx ![-l, 1]
      (by simpa [Fin.sum_univ_two, neg_smul, neg_add_eq_sub] using h) 1
    simp at this
  have huk : u ^ k ≠ 0 := pow_ne_zero _ hu0
  refine core hk (P 0) (P 1) (hP 0) (hP 1) ?_ ?_ ?_
  · intro c hc h
    have := hev 0 c
    rw [h, map_zero] at this
    exact mul_ne_zero (mul_ne_zero huk (hx.ne_zero 0)) (hY c hc) this.symm
  · intro l c hc h
    have := congrArg (aeval u) h
    rw [map_sub, map_mul, hev 1 c, hev 0 c, aeval_C, map_zero] at this
    apply mul_ne_zero (mul_ne_zero huk (hx1 l)) (hY c hc)
    rw [← this, Algebra.smul_def]
    ring
  · intro c d
    apply sub_eq_zero.1 (aeval_eq_zero hu _)
    rw [map_sub, map_mul, map_mul, hev, hev, hev, hev]
    ring

/-! ## Existence for `k = 2` and `k = 3` -/

/-- `a + b uᵐ + c uⁿ = 0`, with `0, m, n` distinct, forces `a = b = c = 0`. -/
theorem three_terms {u : ℂ} (hu : u ∉ Qbar) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ≠ n)
    {a b c : ↥Qbar} (h : (a : ℂ) + b * u ^ m + c * u ^ n = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hP := aeval_eq_zero hu (P := C a + C b * X ^ m + C c * X ^ n)
    (by simp only [map_add, map_mul, aeval_C, aeval_X_pow]; exact h)
  have h0 := congrArg (coeff · 0) hP
  have h1 := congrArg (coeff · m) hP
  have h2 := congrArg (coeff · n) hP
  simp [coeff_C, coeff_X_pow, hm, hn, hmn, hm.symm, hn.symm, hmn.symm] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

/-- `k = 2`: `x = (1, u)`, `y = (u⁻¹, 1, u)`; the products are `u⁻¹, 1, u, 1, u, u²`. -/
theorem exists_two {u : ℂ} (hu : u ∉ Qbar) :
    ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
      LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({(u ^ 2)⁻¹, u⁻¹, 1, u, u ^ 2} : Set ℂ) := by
  have hu0 := ne_zero_of_not_mem hu
  refine ⟨![1, u], ![u⁻¹, 1, u], ?_, ?_, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro s t h
    have h' : (s : ℂ) + t * u ^ 1 + (0 : ↥Qbar) * u ^ 2 = 0 := by
      simpa [Subfield.smul_def] using h
    obtain ⟨h1, h2, -⟩ := three_terms hu one_ne_zero two_ne_zero (by norm_num) h'
    exact ⟨h1, h2⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : (g 0 : ℂ) * u⁻¹ + (g 1 : ℂ) + (g 2 : ℂ) * u = 0 := by
      simpa [Fin.sum_univ_three, Subfield.smul_def] using hg
    have h' : (g 0 : ℂ) + g 1 * u ^ 1 + g 2 * u ^ 2 = 0 := by
      have := congrArg (· * u) hg'
      simp only [zero_mul] at this
      rw [← this]
      field_simp
    obtain ⟨h0, h1, h2⟩ := three_terms hu one_ne_zero two_ne_zero (by norm_num) h'
    intro i
    fin_cases i <;> assumption
  · have e : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
    intro i j
    apply Submodule.subset_span
    fin_cases i <;> fin_cases j <;> simp [e, sq]

/-- `k = 3`: `x = (u, u⁻¹)`, `y = (1, u⁻², u²)`; the products are `u, u⁻¹, u³, u⁻¹, u⁻³, u`. -/
theorem exists_three {u : ℂ} (hu : u ∉ Qbar) :
    ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
      LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({(u ^ 3)⁻¹, u⁻¹, 1, u, u ^ 3} : Set ℂ) := by
  have hu0 := ne_zero_of_not_mem hu
  refine ⟨![u, u⁻¹], ![1, (u ^ 2)⁻¹, u ^ 2], ?_, ?_, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro s t h
    have h' : (t : ℂ) + s * u ^ 2 + (0 : ↥Qbar) * u ^ 1 = 0 := by
      have : (s : ℂ) * u + (t : ℂ) * u⁻¹ = 0 := by simpa [Subfield.smul_def] using h
      have := congrArg (· * u) this
      simp only [zero_mul] at this
      rw [← this]
      field_simp
      push_cast
      ring
    obtain ⟨h1, h2, -⟩ := three_terms hu two_ne_zero one_ne_zero (by norm_num) h'
    exact ⟨h2, h1⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : (g 0 : ℂ) + (g 1 : ℂ) * (u ^ 2)⁻¹ + (g 2 : ℂ) * u ^ 2 = 0 := by
      simpa [Fin.sum_univ_three, Subfield.smul_def] using hg
    have h' : (g 1 : ℂ) + g 0 * u ^ 2 + g 2 * u ^ 4 = 0 := by
      have := congrArg (· * u ^ 2) hg'
      simp only [zero_mul] at this
      rw [← this]
      field_simp
      ring
    obtain ⟨h1, h0, h2⟩ := three_terms hu two_ne_zero four_ne_zero (by norm_num) h'
    intro i
    fin_cases i <;> assumption
  · have e1 : u * (u ^ 2)⁻¹ = u⁻¹ := by field_simp
    have e2 : u * u ^ 2 = u ^ 3 := by ring
    have e3 : u⁻¹ * (u ^ 2)⁻¹ = (u ^ 3)⁻¹ := by field_simp
    have e4 : u⁻¹ * u ^ 2 = u := by field_simp
    intro i j
    apply Submodule.subset_span
    fin_cases i <;> fin_cases j <;> simp [e1, e2, e3, e4]

end D6_power_hull

open DiazModulus D6_power_hull in
/-- For `u ∉ Q̄` and `k ≥ 1`, a strong six exponentials configuration with all six products in
`Q̄u⁻ᵏ + Q̄u⁻¹ + Q̄ + Q̄u + Q̄uᵏ` exists exactly when `k = 2` or `k = 3`. -/
theorem solution {u : ℂ} (hu : u ∉ Qbar) {k : ℕ} (hk : 1 ≤ k) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({(u ^ k)⁻¹, u⁻¹, 1, u, u ^ k} : Set ℂ)) ↔
    (k = 2 ∨ k = 3) := by
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    by_contra h
    exact no_config hu hk (by omega) hx hy hxy
  · rintro (rfl | rfl)
    · exact exists_two hu
    · exact exists_three hu
