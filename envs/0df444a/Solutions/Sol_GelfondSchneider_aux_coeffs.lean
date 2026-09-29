-- Prove2me | solution 1 for GelfondSchneider.aux_coeffs
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:09:01.723738+00:00
-- url     : https://prove2.me/submissions/a58d103d-b88e-420c-920f-a1d060ee2a4c

import Mathlib
import Theorems.Thm_GelfondSchneider_system_entry_house_le

open NumberField

namespace GS_aux

open Matrix

/-- Siegel's lemma in the shape used here (`card κ = 2 * card ι`, so the Siegel exponent is `1`),
with an existential constant. Derived from Mathlib's
`NumberField.house.exists_ne_zero_int_vec_house_le`, whose constant is private: it is captured
by unification and never named. -/
theorem gs_siegel (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (a : Matrix ι κ (𝓞 K)) (A : ℝ),
      0 < Fintype.card ι → Fintype.card κ = 2 * Fintype.card ι → a ≠ 0 →
      (∀ i j, house (a i j : K) ≤ A) →
      ∃ ξ : κ → 𝓞 K, ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧ ∀ j, house (ξ j : K) ≤ C * Fintype.card κ * A := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (a : Matrix ι κ (𝓞 K))
      (A : ℝ), a ≠ 0 → 0 < Fintype.card ι → Fintype.card ι < Fintype.card κ →
      (∀ i j, house (algebraMap (𝓞 K) K (a i j)) ≤ A) →
      ∃ ξ : κ → 𝓞 K, ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧ ∀ j, house (ξ j).1 ≤
        c * (c * Fintype.card κ * A) ^ ((Fintype.card ι : ℝ) /
          (Fintype.card κ - Fintype.card ι)) :=
    ⟨_, fun a A ha hp hpq hA =>
      NumberField.house.exists_ne_zero_int_vec_house_le K a ha hp hpq rfl hA rfl⟩
  refine ⟨c ^ 2, sq_nonneg c, fun {ι κ} _ _ a A hp hcard ha hA => ?_⟩
  have hpq : Fintype.card ι < Fintype.card κ := by omega
  obtain ⟨ξ, hξ0, hξ, hbd⟩ := hc a A ha hp hpq hA
  refine ⟨ξ, hξ0, hξ, fun j => (hbd j).trans (le_of_eq ?_)⟩
  have hexp : ((Fintype.card ι : ℝ) / (Fintype.card κ - Fintype.card ι)) = 1 := by
    rw [hcard]; push_cast
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hp
    field_simp; ring
  rw [hexp, Real.rpow_one]; ring

/-- A common integer denominator for three elements of a number field. -/
theorem exists_int_mul_isIntegral {K : Type*} [Field K] [NumberField K] (x y z : K) :
    ∃ c : ℤ, c ≠ 0 ∧ IsIntegral ℤ ((c : K) * x) ∧ IsIntegral ℤ ((c : K) * y) ∧
      IsIntegral ℤ ((c : K) * z) := by
  classical
  obtain ⟨c, hc, h⟩ := exists_integral_multiples ℤ ℚ (L := K) {x, y, z}
  refine ⟨c, hc, ?_, ?_, ?_⟩
  · simpa [zsmul_eq_mul] using h x (by simp)
  · simpa [zsmul_eq_mul] using h y (by simp)
  · simpa [zsmul_eq_mul] using h z (by simp)

/-- If `c x` is integral and `e ≤ N`, then `c ^ N * x ^ e` is integral. -/
theorem isIntegral_intCast_pow_mul_pow {K : Type*} [Field K] (c : ℤ) (x : K)
    (hx : IsIntegral ℤ ((c : K) * x)) {e N : ℕ} (h : e ≤ N) :
    IsIntegral ℤ ((c : K) ^ N * x ^ e) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have : (c : K) ^ (e + d) * x ^ e = (c : K) ^ d * ((c : K) * x) ^ e := by ring
  rw [this]
  exact ((isIntegral_intCast c).pow d).mul (hx.pow e)

/-- The unscaled system entry `((a+1) + (b+1)β')^k · α'^((a+1)j) · γ'^((b+1)j)`. -/
def entry {K : Type*} [Field K] (α' β' γ' : K) (a b j k : ℕ) : K :=
  (((a : K) + 1) + ((b : K) + 1) * β') ^ k * α' ^ ((a + 1) * j) * γ' ^ ((b + 1) * j)

theorem entry_eq {K : Type*} [Field K] (α' β' γ' : K) (a b j k : ℕ) :
    entry α' β' γ' a b j k = (((a + 1 : ℕ) : K) + ((b + 1 : ℕ) : K) * β') ^ k *
      α' ^ ((a + 1) * j) * γ' ^ ((b + 1) * j) := by
  unfold entry; push_cast; ring

theorem isIntegral_scaled_entry {K : Type*} [Field K] (α' β' γ' : K) (c : ℤ)
    (hcα : IsIntegral ℤ ((c : K) * α')) (hcβ : IsIntegral ℤ ((c : K) * β'))
    (hcγ : IsIntegral ℤ ((c : K) * γ')) {a b j k N₁ N₂ N₃ : ℕ}
    (hk : k ≤ N₁) (ha : (a + 1) * j ≤ N₂) (hb : (b + 1) * j ≤ N₃) :
    IsIntegral ℤ ((c : K) ^ (N₁ + N₂ + N₃) * entry α' β' γ' a b j k) := by
  have hs : IsIntegral ℤ ((c : K) * (((a : K) + 1) + ((b : K) + 1) * β')) := by
    have e : (c : K) * (((a : K) + 1) + ((b : K) + 1) * β') =
        (c : K) * ((a + 1 : ℕ) : K) + ((b + 1 : ℕ) : K) * ((c : K) * β') := by
      push_cast; ring
    rw [e]
    exact ((isIntegral_intCast c).mul (isIntegral_natCast _)).add
      ((isIntegral_natCast _).mul hcβ)
  have h1 := isIntegral_intCast_pow_mul_pow c _ hs hk
  have h2 := isIntegral_intCast_pow_mul_pow c _ hcα ha
  have h3 := isIntegral_intCast_pow_mul_pow c _ hcγ hb
  have e : (c : K) ^ (N₁ + N₂ + N₃) * entry α' β' γ' a b j k =
      ((c : K) ^ N₁ * (((a : K) + 1) + ((b : K) + 1) * β') ^ k) *
        ((c : K) ^ N₂ * α' ^ ((a + 1) * j)) * ((c : K) ^ N₃ * γ' ^ ((b + 1) * j)) := by
    unfold entry; rw [pow_add, pow_add]; ring
  rw [e]
  exact (h1.mul h2).mul h3

/-- Integrality of the scaled entries, for the exponent `N = (n - 1) + m q + m q`. -/
theorem sysMat_int {K : Type*} [Field K] (α' β' γ' : K) (c : ℤ)
    (hcα : IsIntegral ℤ ((c : K) * α')) (hcβ : IsIntegral ℤ ((c : K) * β'))
    (hcγ : IsIntegral ℤ ((c : K) * γ')) (m n q : ℕ) (i : Fin m × Fin n) (t : Fin q × Fin q) :
    IsIntegral ℤ ((c : K) ^ (n - 1 + m * q + m * q) *
      entry α' β' γ' (t.1 : ℕ) (t.2 : ℕ) ((i.1 : ℕ) + 1) (i.2 : ℕ)) := by
  have hi1 := i.1.isLt
  have hi2 := i.2.isLt
  have ht1 := t.1.isLt
  have ht2 := t.2.isLt
  apply isIntegral_scaled_entry α' β' γ' c hcα hcβ hcγ
  · omega
  · calc ((t.1 : ℕ) + 1) * ((i.1 : ℕ) + 1) ≤ q * m := Nat.mul_le_mul (by omega) (by omega)
      _ = m * q := Nat.mul_comm _ _
  · calc ((t.2 : ℕ) + 1) * ((i.1 : ℕ) + 1) ≤ q * m := Nat.mul_le_mul (by omega) (by omega)
      _ = m * q := Nat.mul_comm _ _

/-- The scaled system matrix: rows `(j, k) ↦ (j + 1, k)`, columns `(a, b)`. -/
def sysMat {K : Type*} [Field K] [NumberField K] (α' β' γ' : K) (c : ℤ) (m n q : ℕ)
    (hint : ∀ (i : Fin m × Fin n) (t : Fin q × Fin q), IsIntegral ℤ
      ((c : K) ^ (n - 1 + m * q + m * q) *
        entry α' β' γ' (t.1 : ℕ) (t.2 : ℕ) ((i.1 : ℕ) + 1) (i.2 : ℕ))) :
    Matrix (Fin m × Fin n) (Fin q × Fin q) (𝓞 K) :=
  fun i t => ⟨_, hint i t⟩

theorem sysMat_ne_zero {K : Type*} [Field K] [NumberField K] {α' β' γ' : K} (hα' : α' ≠ 0)
    (hγ' : γ' ≠ 0) {c : ℤ} (hc : c ≠ 0) {m n q : ℕ} (hm : 0 < m) (hn : 0 < n) (hq : 0 < q)
    (hint : ∀ (i : Fin m × Fin n) (t : Fin q × Fin q), IsIntegral ℤ
      ((c : K) ^ (n - 1 + m * q + m * q) *
        entry α' β' γ' (t.1 : ℕ) (t.2 : ℕ) ((i.1 : ℕ) + 1) (i.2 : ℕ))) :
    sysMat α' β' γ' c m n q hint ≠ 0 := by
  intro h
  have h0 := congrFun (congrFun h (⟨0, hm⟩, ⟨0, hn⟩)) (⟨0, hq⟩, ⟨0, hq⟩)
  have h1 := congrArg (algebraMap (𝓞 K) K) h0
  simp [sysMat, entry, hc, hα', hγ'] at h1

/-- `N = (n - 1) + m q + m q ≤ (1 + 4 m²) n`, using `q ≤ q² = 2 m n`. -/
theorem exponent_le {m n q : ℕ} (hq : q ^ 2 = 2 * m * n) :
    n - 1 + m * q + m * q ≤ (1 + 4 * m ^ 2) * n := by
  have h1 : q ≤ 2 * m * n := by
    have := Nat.le_self_pow two_ne_zero q
    rwa [hq] at this
  have h2 : m * q ≤ m * (2 * m * n) := Nat.mul_le_mul_left m h1
  have h3 : (1 + 4 * m ^ 2) * n = n + m * (2 * m * n) + m * (2 * m * n) := by ring
  rw [h3]; omega

theorem house_scaled_le {K : Type*} [Field K] [NumberField K] (c : ℤ) (hc : c ≠ 0) (e : K)
    {N L n : ℕ} (hN : N ≤ L * n) {B : ℝ} (he : house e ≤ B) :
    house ((c : K) ^ N * e) ≤ (|(c : ℝ)| ^ L) ^ n * B := by
  have h1 : house ((c : K) ^ N) = |(c : ℝ)| ^ N := by
    rw [← Int.cast_pow, house_intCast]; push_cast; rw [abs_pow]
  have hc1 : 1 ≤ |(c : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hc
  have h2 : |(c : ℝ)| ^ N ≤ (|(c : ℝ)| ^ L) ^ n := by
    rw [← pow_mul]; exact pow_le_pow_right₀ hc1 hN
  calc house ((c : K) ^ N * e) ≤ house ((c : K) ^ N) * house e := house_mul_le _ _
    _ ≤ (|(c : ℝ)| ^ L) ^ n * B := by
      rw [h1]; exact mul_le_mul h2 he (house_nonneg _) (by positivity)

theorem sysMat_house_le {K : Type*} [Field K] [NumberField K] {α' β' γ' : K} {c : ℤ}
    (hc : c ≠ 0) {m : ℕ} {C₀ : ℝ}
    (hE : ∀ n q a b j k : ℕ, 0 < n → q ^ 2 = 2 * m * n →
      1 ≤ a → a ≤ q → 1 ≤ b → b ≤ q → 1 ≤ j → j ≤ m → k < n →
      house (((a : K) + (b : K) * β') ^ k * α' ^ (a * j) * γ' ^ (b * j)) ≤
        C₀ ^ n * (n : ℝ) ^ (((n : ℝ) - 1) / 2))
    {n q : ℕ} (hn : 0 < n) (hq : q ^ 2 = 2 * m * n)
    (hint : ∀ (i : Fin m × Fin n) (t : Fin q × Fin q), IsIntegral ℤ
      ((c : K) ^ (n - 1 + m * q + m * q) *
        entry α' β' γ' (t.1 : ℕ) (t.2 : ℕ) ((i.1 : ℕ) + 1) (i.2 : ℕ)))
    (i : Fin m × Fin n) (t : Fin q × Fin q) :
    house (sysMat α' β' γ' c m n q hint i t : K) ≤
      (|(c : ℝ)| ^ (1 + 4 * m ^ 2) * C₀) ^ n * (n : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  have hi1 := i.1.isLt
  have hi2 := i.2.isLt
  have ht1 := t.1.isLt
  have ht2 := t.2.isLt
  have hE' := hE n q ((t.1 : ℕ) + 1) ((t.2 : ℕ) + 1) ((i.1 : ℕ) + 1) (i.2 : ℕ) hn hq
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hi2
  rw [← entry_eq] at hE'
  have := house_scaled_le c hc _ (exponent_le hq) hE'
  rw [mul_pow, mul_assoc]
  exact this

theorem sum_eq_zero_of_mulVec {K : Type*} [Field K] [NumberField K] {α' β' γ' : K} {c : ℤ}
    (hc : c ≠ 0) {m n q : ℕ}
    (hint : ∀ (i : Fin m × Fin n) (t : Fin q × Fin q), IsIntegral ℤ
      ((c : K) ^ (n - 1 + m * q + m * q) *
        entry α' β' γ' (t.1 : ℕ) (t.2 : ℕ) ((i.1 : ℕ) + 1) (i.2 : ℕ)))
    {ξ : Fin q × Fin q → 𝓞 K} (hξ : sysMat α' β' γ' c m n q hint *ᵥ ξ = 0)
    (j : ℕ) (hj : j < m) (k : ℕ) (hk : k < n) :
    ∑ a : Fin q, ∑ b : Fin q,
      (ξ (a, b) : K) * (((a : ℕ) + 1 : K) + ((b : ℕ) + 1 : K) * β') ^ k *
        α' ^ (((a : ℕ) + 1) * (j + 1)) * γ' ^ (((b : ℕ) + 1) * (j + 1)) = 0 := by
  have h0 := congrFun hξ (⟨j, hj⟩, ⟨k, hk⟩)
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h0
  have h1 := congrArg (algebraMap (𝓞 K) K) h0
  rw [map_sum, map_zero, Fintype.sum_prod_type] at h1
  have h2 : (c : K) ^ (n - 1 + m * q + m * q) * (∑ a : Fin q, ∑ b : Fin q,
      (ξ (a, b) : K) * (((a : ℕ) + 1 : K) + ((b : ℕ) + 1 : K) * β') ^ k *
        α' ^ (((a : ℕ) + 1) * (j + 1)) * γ' ^ (((b : ℕ) + 1) * (j + 1))) = 0 := by
    rw [← h1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [map_mul]
    simp only [sysMat, RingOfIntegers.map_mk, entry]
    ring
  exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ (Int.cast_ne_zero.mpr hc))

/-- The final real inequality: `S · (M n) · (D^n n^((n-1)/2)) ≤ ((S+1) M D)^n n^((n+1)/2)`. -/
theorem final_bound {S M D x : ℝ} {n : ℕ} (hS : 0 ≤ S) (hM : 1 ≤ M) (hD : 1 ≤ D) (hn : 0 < n)
    (hx : x ≤ S * (M * n) * (D ^ n * (n : ℝ) ^ (((n : ℝ) - 1) / 2))) :
    x ≤ ((S + 1) * M * D) ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : (n : ℝ) ^ (((n : ℝ) + 1) / 2) = (n : ℝ) * (n : ℝ) ^ (((n : ℝ) - 1) / 2) := by
    rw [show ((n : ℝ) + 1) / 2 = 1 + ((n : ℝ) - 1) / 2 by ring, Real.rpow_add hn',
      Real.rpow_one]
  have h1 : 1 ≤ (S + 1) * M := one_le_mul_of_one_le_of_one_le (by linarith) hM
  have h2 : (S + 1) * M ≤ ((S + 1) * M) ^ n := le_self_pow₀ h1 hn.ne'
  have h3 : S * M ≤ (S + 1) * M := by
    have : 0 ≤ M := by linarith
    nlinarith
  have hP : 0 ≤ (n : ℝ) ^ (((n : ℝ) - 1) / 2) := Real.rpow_nonneg hn'.le _
  have hDn : 0 ≤ D ^ n := pow_nonneg (by linarith) n
  have hQ : 0 ≤ D ^ n * ((n : ℝ) * (n : ℝ) ^ (((n : ℝ) - 1) / 2)) :=
    mul_nonneg hDn (mul_nonneg hn'.le hP)
  calc x ≤ S * (M * n) * (D ^ n * (n : ℝ) ^ (((n : ℝ) - 1) / 2)) := hx
    _ = (S * M) * (D ^ n * ((n : ℝ) * (n : ℝ) ^ (((n : ℝ) - 1) / 2))) := by ring
    _ ≤ ((S + 1) * M) ^ n * (D ^ n * ((n : ℝ) * (n : ℝ) ^ (((n : ℝ) - 1) / 2))) :=
      mul_le_mul_of_nonneg_right (h3.trans h2) hQ
    _ = ((S + 1) * M * D) ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2) := by
      rw [hr, mul_pow ((S + 1) * M) D n]; ring

end GS_aux

open GS_aux in
theorem solution (K : Type*) [Field K] [NumberField K] (α' β' γ' : K)
    (hα' : α' ≠ 0) (hγ' : γ' ≠ 0) (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n q : ℕ, 0 < n → q ^ 2 = 2 * m * n →
      ∃ η : Fin q → Fin q → 𝓞 K, η ≠ 0 ∧
        (∀ a b, house (η a b : K) ≤ C ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ k < n, ∑ a : Fin q, ∑ b : Fin q,
          (η a b : K) * (((a : ℕ) + 1 : K) + ((b : ℕ) + 1 : K) * β') ^ k *
            α' ^ (((a : ℕ) + 1) * j) * γ' ^ (((b : ℕ) + 1) * j) = 0 := by
  obtain ⟨c, hc0, hcα, hcβ, hcγ⟩ := exists_int_mul_isIntegral α' β' γ'
  obtain ⟨C₀, hC₀, hE⟩ := GelfondSchneider.system_entry_house_le K α' β' γ' m hm
  obtain ⟨S, hS, hSiegel⟩ := gs_siegel K
  have hc1 : 1 ≤ |(c : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hc0
  have hM : (1 : ℝ) ≤ 2 * m := by
    have : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr hm
    linarith
  have hD : 1 ≤ |(c : ℝ)| ^ (1 + 4 * m ^ 2) * C₀ :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hc1) hC₀
  refine ⟨(S + 1) * (2 * m) * (|(c : ℝ)| ^ (1 + 4 * m ^ 2) * C₀),
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hM) hD, ?_⟩
  intro n q hn hq
  have hq0 : 0 < q := by
    have h1 : 0 < q ^ 2 := by rw [hq]; exact Nat.mul_pos (Nat.mul_pos two_pos hm) hn
    exact Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
  have hint := sysMat_int α' β' γ' c hcα hcβ hcγ m n q
  have hcardpos : 0 < Fintype.card (Fin m × Fin n) := by
    simp only [Fintype.card_prod, Fintype.card_fin]; exact Nat.mul_pos hm hn
  have hcard : Fintype.card (Fin q × Fin q) = 2 * Fintype.card (Fin m × Fin n) := by
    simp only [Fintype.card_prod, Fintype.card_fin]; rw [← sq, hq, mul_assoc]
  have hcardR : ((Fintype.card (Fin q × Fin q) : ℕ) : ℝ) = 2 * m * n := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    have : q * q = 2 * m * n := by rw [← sq, hq]
    exact_mod_cast this
  obtain ⟨ξ, hξ0, hMξ, hξ⟩ := hSiegel (sysMat α' β' γ' c m n q hint)
    ((|(c : ℝ)| ^ (1 + 4 * m ^ 2) * C₀) ^ n * (n : ℝ) ^ (((n : ℝ) - 1) / 2))
    hcardpos hcard (sysMat_ne_zero hα' hγ' hc0 hm hn hq0 hint)
    (sysMat_house_le hc0 hE hn hq hint)
  refine ⟨fun a b => ξ (a, b), ?_, ?_, ?_⟩
  · intro h
    apply hξ0
    funext t
    exact congrFun (congrFun h t.1) t.2
  · intro a b
    apply final_bound hS hM hD hn
    have := hξ (a, b)
    rw [hcardR] at this
    exact this
  · intro j hj1 hjm k hk
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact sum_eq_zero_of_mulVec hc0 hint hMξ j' (by omega) k hk

#print axioms solution
