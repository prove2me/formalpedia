-- Prove2me | solution 1 for DiazModulus.polynomial_hull_no_two_by_three_configuration
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-16T14:02:23.471189+00:00
-- url     : https://prove2.me/submissions/e92b833e-7fdb-473e-b8d3-6f9af1e2e6b0

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_config_shifted_polynomial_spans
import Theorems.Thm_DiazModulus_polynomial_submodule_trailing_degrees_card
import Theorems.Thm_DiazModulus_polynomial_submodule_degrees_card
import Theorems.Thm_DiazModulus_shifted_polynomial_hull_orders
import Theorems.Thm_DiazModulus_five_point_sumset_rigid

open Complex ComplexConjugate

/-! # A polynomial hull of degree at most one or at least four carries no 2×3 configuration

Let `u ∉ Q̄` with `ρ = u ū` algebraic, `P ∈ Q̄[X]` of degree `k`, and
`W = span_Q̄ {1, u, ū, P(u), conj P(u)}`. Suppose free `x₀, x₁` and free `y₀, y₁, y₂` have all
six products in `W`; we derive a contradiction.

* If `u^N` times each of the five spanning numbers is the value at `u` of a polynomial in a
  subspace `H ⊆ Q̄[X]`, the same holds for all of `W` (`shift`). Then
  `config_shifted_polynomial_spans` gives free `a₀, a₁` and free `b₀, b₁, b₂` in `Q̄[X]` and
  `P₀ ≠ 0` with `f g ∈ P₀ H` whenever `f` lies in the span of the `a`'s and `g` in the span of
  the `b`'s. Along `f g = P₀ h` orders at `0` and degrees add up (`pairs`), and each span has as
  many orders, and as many degrees, as its dimension (`cards`).
* `k ≤ 1`: take `N = 1` and `H` the polynomials of degree at most `2` (recall `u ū = ρ`). The six
  degree sums `deg f + deg g` then lie in a window of three consecutive values, which two and
  three distinct degrees cannot do (`narrow`).
* `k ≥ 4`: let `L = P − p₀ − p₁X`, `m` its order (so `2 ≤ m ≤ k`), `Q₁ = L X^k` and
  `Q₂ = Σ_j conj(L_j) ρ^j X^(k−j)`, so that `u^k conj L(u) = Q₂(u)`. With `N = k` and
  `H = span {X^(k−1), X^k, X^(k+1), Q₁, Q₂}`, `shifted_polynomial_hull_orders` puts every order of
  a non-zero element of `H`, minus `k`, in `{−k, −1, 0, 1, m}`, and every degree, reflected about
  `k`, in the same set. By `five_point_sumset_rigid` (read on naturals in `rigid`) the shifted
  order sums are exactly `{−1, 0, 1, 2}`, and so are the reflected degree sums. A product
  `f g = P₀ h` realising the order sum `2` has `ord h = k + 2`, while the degree sums give
  `deg h ≤ k + 1`; this is impossible for `h ≠ 0`.
-/

namespace R16_hull

open DiazModulus Polynomial

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

/-- Conjugation maps `Q̄` to itself. -/
theorem conj_mem {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar :=
  mem_Qbar_iff.2 ((mem_Qbar_iff.1 ha).algHom (starRingEnd ℂ).toRatAlgHom)

/-- If `u ^ N` times each spanning vector is the value at `u` of an element of `H`, so is `u ^ N`
times every vector of the span. -/
theorem shift {u : ℂ} (H : Submodule (↥Qbar) (↥Qbar)[X]) (N : ℕ) {S : Set ℂ}
    (hS : ∀ s ∈ S, ∃ Q ∈ H, aeval u Q = u ^ N * s) {w : ℂ} (hw : w ∈ Submodule.span Qbar S) :
    ∃ Q ∈ H, aeval u Q = u ^ N * w := by
  induction hw using Submodule.span_induction with
  | mem s hs => exact hS s hs
  | zero => exact ⟨0, H.zero_mem, by simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨Q, hQ, e⟩ := hv
    obtain ⟨R, hR, f⟩ := hw
    exact ⟨Q + R, H.add_mem hQ hR, by rw [map_add, e, f]; ring⟩
  | smul c w _ hw =>
    obtain ⟨Q, hQ, e⟩ := hw
    exact ⟨c • Q, H.smul_mem c hQ, by simp only [map_smul, e, Subfield.smul_def, smul_eq_mul]; ring⟩

/-- Orders and degrees add up along `f g = P₀ h`. -/
theorem pairs {K : Type*} [Field K] {H V W : Submodule K K[X]} {P₀ : K[X]} (hP₀ : P₀ ≠ 0)
    (hVW : ∀ f ∈ V, ∀ g ∈ W, ∃ h ∈ H, f * g = P₀ * h) {f g : K[X]} (hf : f ∈ V) (hf0 : f ≠ 0)
    (hg : g ∈ W) (hg0 : g ≠ 0) :
    ∃ h ∈ H, h ≠ 0 ∧
      f.natTrailingDegree + g.natTrailingDegree = P₀.natTrailingDegree + h.natTrailingDegree ∧
      f.natDegree + g.natDegree = P₀.natDegree + h.natDegree := by
  obtain ⟨h, hh, e⟩ := hVW f hf g hg
  have h0 : h ≠ 0 := by rintro rfl; exact mul_ne_zero hf0 hg0 (by rw [e, mul_zero])
  refine ⟨h, hh, h0, ?_, ?_⟩
  · rw [← natTrailingDegree_mul hf0 hg0, e, natTrailingDegree_mul hP₀ h0]
  · rw [← natDegree_mul hf0 hg0, e, natDegree_mul hP₀ h0]

/-- The span of `n` independent polynomials has `n` orders and `n` degrees. -/
theorem cards {K : Type*} [Field K] {n : ℕ} {a : Fin n → K[X]} (ha : LinearIndependent K a) :
    (natTrailingDegree '' ((Submodule.span K (Set.range a) : Set K[X]) \ {0})).ncard = n ∧
      (natDegree '' ((Submodule.span K (Set.range a) : Set K[X]) \ {0})).ncard = n := by
  have := FiniteDimensional.span_of_finite K (Set.finite_range a)
  have e := (finrank_span_eq_card ha).trans (Fintype.card_fin n)
  exact ⟨(polynomial_submodule_trailing_degrees_card K _).trans e,
    (polynomial_submodule_degrees_card K _).trans e⟩

/-- Sums of two and of three distinct naturals do not fit in three consecutive values. -/
theorem narrow {S T : Set ℕ} (hS : S.ncard = 2) (hT : T.ncard = 3) (c : ℕ)
    (h : ∀ s ∈ S, ∀ t ∈ T, c ≤ s + t ∧ s + t ≤ c + 2) : False := by
  obtain ⟨s₁, s₂, h₁₂, rfl⟩ := Set.ncard_eq_two.1 hS
  obtain ⟨t₁, t₂, t₃, h₁, h₂, h₃, rfl⟩ := Set.ncard_eq_three.1 hT
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq] at h
  omega

open Pointwise in
/-- `five_point_sumset_rigid`, read on sets of naturals through injective maps to `ℤ`. -/
theorem rigid {k m : ℕ} (hk : 4 ≤ k) (hm : 2 ≤ m) (hmk : m ≤ k) {S T : Set ℕ}
    (hS : S.ncard = 2) (hT : T.ncard = 3) (α β : ℕ → ℤ) (hα : Function.Injective α)
    (hβ : Function.Injective β)
    (h : ∀ s ∈ S, ∀ t ∈ T, α s + β t ∈ ({-(k : ℤ), -1, 0, 1, (m : ℤ)} : Finset ℤ)) :
    (∀ s ∈ S, ∀ t ∈ T, α s + β t ∈ ({-1, 0, 1, 2} : Finset ℤ)) ∧
      ∃ s ∈ S, ∃ t ∈ T, α s + β t = 2 := by
  have hSf := Set.finite_of_ncard_ne_zero (s := S) (by omega)
  have hTf := Set.finite_of_ncard_ne_zero (s := T) (by omega)
  set A := hSf.toFinset.image α
  set B := hTf.toFinset.image β
  have mem : ∀ s ∈ S, ∀ t ∈ T, α s + β t ∈ A + B := fun s hs t ht =>
    Finset.add_mem_add (Finset.mem_image_of_mem _ (hSf.mem_toFinset.2 hs))
      (Finset.mem_image_of_mem _ (hTf.mem_toFinset.2 ht))
  have hAB := (five_point_sumset_rigid k m (by exact_mod_cast hk) (by exact_mod_cast hm)
    (by exact_mod_cast hmk) A B
    (by rw [Finset.card_image_of_injective _ hα, ← Set.ncard_eq_toFinset_card S hSf, hS])
    (by rw [Finset.card_image_of_injective _ hβ, ← Set.ncard_eq_toFinset_card T hTf, hT])
    (by
      intro z hz
      obtain ⟨_, hx, _, hy, rfl⟩ := Finset.mem_add.1 hz
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
      exact h s (hSf.mem_toFinset.1 hs) t (hTf.mem_toFinset.1 ht))).2
  refine ⟨fun s hs t ht => by rw [← hAB]; exact mem s hs t ht, ?_⟩
  have h2 : (2 : ℤ) ∈ A + B := by rw [hAB]; simp
  obtain ⟨_, hx, _, hy, e⟩ := Finset.mem_add.1 h2
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
  exact ⟨s, hSf.mem_toFinset.1 hs, t, hTf.mem_toFinset.1 ht, e⟩

end R16_hull

open DiazModulus Polynomial Pointwise in
theorem solution {u : ℂ} (hu : u ∉ Qbar)
    (hρ : IsAlgebraic ℚ (u * conj u)) (P : (↥Qbar)[X])
    (hP : P.natDegree ≤ 1 ∨ 4 ≤ P.natDegree) :
    ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
      LinearIndependent (↥Qbar) y ∧ ∀ i j, x i * y j ∈
        Submodule.span Qbar ({1, u, conj u, aeval u P, conj (aeval u P)} : Set ℂ) := by
  rintro ⟨x, y, hx, hy, hxy⟩
  obtain ⟨ρ, hρu⟩ : ∃ ρ : ↥Qbar, (ρ : ℂ) = u * conj u := ⟨⟨_, mem_Qbar_iff.2 hρ⟩, rfl⟩
  obtain ⟨cj, hcj⟩ : ∃ cj : ↥Qbar → ↥Qbar, ∀ c, (cj c : ℂ) = conj (c : ℂ) :=
    ⟨fun c => ⟨_, R16_hull.conj_mem c.2⟩, fun _ => rfl⟩
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (zero_mem _)
  have ev : ∀ (c : ↥Qbar) n, aeval u (c • (X : (↥Qbar)[X]) ^ n) = c * u ^ n := fun c n => by
    rw [map_smul, aeval_X_pow, Subfield.smul_def, smul_eq_mul]
  rcases hP with hP | hP
  · -- degree at most one: `u` times `W` consists of values of polynomials of degree `≤ 2`
    have hPe : aeval u P = P.coeff 1 * u + P.coeff 0 := by
      conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hP]
      simp only [map_add, map_mul, aeval_C, aeval_X, R16_hull.am]
    obtain ⟨a, b, P₀, ha, hb, hP₀, hab⟩ := config_shifted_polynomial_spans hu
      (degreeLE (↥Qbar) (2 : ℕ)) 1 x y hx hy fun i j => R16_hull.shift _ 1 (by
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl
        · exact ⟨X, mem_degreeLE.2 (by compute_degree!), by simp⟩
        · exact ⟨X ^ 2, mem_degreeLE.2 (by compute_degree!), by rw [aeval_X_pow, pow_one, sq]⟩
        · exact ⟨C ρ, mem_degreeLE.2 (by compute_degree!), by rw [aeval_C, R16_hull.am, hρu, pow_one]⟩
        · refine ⟨C (P.coeff 1) * X ^ 2 + C (P.coeff 0) * X, mem_degreeLE.2 (by compute_degree!), ?_⟩
          rw [hPe]
          simp only [map_add, map_mul, aeval_C, aeval_X_pow, aeval_X, R16_hull.am]
          ring
        · refine ⟨C (cj (P.coeff 1) * ρ) + C (cj (P.coeff 0)) * X,
            mem_degreeLE.2 (by compute_degree!), ?_⟩
          rw [hPe]
          simp only [map_add, map_mul, aeval_C, aeval_X, R16_hull.am, hcj, hρu]
          ring) (hxy i j)
    refine R16_hull.narrow (R16_hull.cards ha).2 (R16_hull.cards hb).2 P₀.natDegree ?_
    rintro _ ⟨f, ⟨hf, hf0⟩, rfl⟩ _ ⟨g, ⟨hg, hg0⟩, rfl⟩
    obtain ⟨h, hh, -, -, e⟩ := R16_hull.pairs hP₀ hab hf hf0 hg hg0
    have := natDegree_le_of_degree_le (mem_degreeLE.1 hh)
    omega
  · -- degree `k ≥ 4`
    set k := P.natDegree
    obtain ⟨L, hL⟩ : ∃ L, L = P - (C (P.coeff 1) * X + C (P.coeff 0)) := ⟨_, rfl⟩
    have hLd : L.natDegree = k := by
      rw [hL]; exact natDegree_sub_eq_left_of_natDegree_lt (natDegree_linear_le.trans_lt (by omega))
    have hL0 : L ≠ 0 := by rintro rfl; rw [natDegree_zero] at hLd; omega
    set m := L.natTrailingDegree
    have hm2 : 2 ≤ m := le_natTrailingDegree hL0 fun j hj => by
      interval_cases j <;> simp [hL, coeff_X, coeff_C]
    have hmk : m ≤ k := hLd ▸ natTrailingDegree_le_natDegree L
    have hρ0 : ρ ≠ 0 := by
      rintro rfl
      exact mul_ne_zero hu0 ((_root_.map_ne_zero _).2 hu0) (by rw [← hρu, ZeroMemClass.coe_zero])
    have hcj0 : ∀ c, cj c = 0 ↔ c = 0 := fun c => by
      rw [← ZeroMemClass.coe_eq_zero, hcj, map_eq_zero, ZeroMemClass.coe_eq_zero]
    -- `Q₂`, with `u ^ k * conj L(u) = Q₂(u)`
    obtain ⟨Q₂, hQ₂⟩ : ∃ Q : (↥Qbar)[X],
        Q = ∑ j ∈ Finset.range (k + 1), C (cj (L.coeff j) * ρ ^ j) * X ^ (k - j) := ⟨_, rfl⟩
    have hQc : ∀ i ≤ k, Q₂.coeff i = cj (L.coeff (k - i)) * ρ ^ (k - i) := by
      intro i hi
      rw [hQ₂, finsetSum_coeff, Finset.sum_eq_single (k - i)]
      · rw [coeff_C_mul_X_pow, if_pos (by omega)]
      · intro j hj hne
        rw [coeff_C_mul_X_pow, if_neg (by rw [Finset.mem_range] at hj; omega)]
      · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
    have hQ₂0 : Q₂.coeff 0 ≠ 0 := by
      rw [hQc 0 (by omega), Nat.sub_zero, ← hLd]
      exact mul_ne_zero ((hcj0 _).not.2 (leadingCoeff_ne_zero.2 hL0)) (pow_ne_zero _ hρ0)
    have hQ₂d : Q₂.natDegree = k - m := by
      refine natDegree_eq_of_le_of_coeff_ne_zero
        (natDegree_le_iff_coeff_eq_zero.2 fun N hN => ?_) ?_
      · rcases le_or_gt N k with hNk | hNk
        · rw [hQc N hNk, coeff_eq_zero_of_lt_natTrailingDegree (by omega), (hcj0 0).2 rfl, zero_mul]
        · rw [hQ₂, finsetSum_coeff]
          exact Finset.sum_eq_zero fun j _ => by rw [coeff_C_mul_X_pow, if_neg (by omega)]
      · rw [hQc _ (by omega), Nat.sub_sub_self hmk]
        exact mul_ne_zero ((hcj0 _).not.2 (trailingCoeff_nonzero_iff_nonzero.2 hL0))
          (pow_ne_zero _ hρ0)
    have hQ₂e : aeval u Q₂ = u ^ k * conj (aeval u L) := by
      rw [hQ₂, aeval_eq_sum_range (p := L), hLd, map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have : u ^ k = u ^ (k - j) * u ^ j := by
        rw [← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
      simp only [map_mul, aeval_C, aeval_X, R16_hull.am, hcj, hρu, Subfield.smul_def,
        smul_eq_mul, map_pow]
      rw [this]
      ring
    have hPe : aeval u P = aeval u L + P.coeff 1 * u + P.coeff 0 := by
      have : aeval u L = aeval u P - (P.coeff 1 * u + P.coeff 0) := by
        rw [hL]; simp only [map_sub, map_add, map_mul, aeval_C, aeval_X, R16_hull.am]
      rw [this]; ring
    -- the hull `H` and the shift by `u ^ k`
    set H := Submodule.span (↥Qbar)
      ({X ^ (k - 1), X ^ k, X ^ (k + 1), L * X ^ k, Q₂} : Set (↥Qbar)[X])
    have g1 : X ^ (k - 1) ∈ H := Submodule.subset_span (by simp)
    have g2 : X ^ k ∈ H := Submodule.subset_span (by simp)
    have g3 : X ^ (k + 1) ∈ H := Submodule.subset_span (by simp)
    have g4 : L * X ^ k ∈ H := Submodule.subset_span (by simp)
    have g5 : Q₂ ∈ H := Submodule.subset_span (by simp)
    have hk1 : u ^ k = u ^ (k - 1) * u := (pow_sub_one_mul (by omega) u).symm
    obtain ⟨a, b, P₀, ha, hb, hP₀, hab⟩ := config_shifted_polynomial_spans hu H k x y hx hy
      fun i j => R16_hull.shift H k (by
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl
        · exact ⟨_, g2, by simp⟩
        · exact ⟨_, g3, by rw [aeval_X_pow, pow_succ]⟩
        · exact ⟨ρ • X ^ (k - 1), H.smul_mem ρ g1, by rw [ev, hρu, hk1]; ring⟩
        · refine ⟨P.coeff 0 • X ^ k + P.coeff 1 • X ^ (k + 1) + L * X ^ k,
            H.add_mem (H.add_mem (H.smul_mem _ g2) (H.smul_mem _ g3)) g4, ?_⟩
          rw [map_add, map_add, ev, ev, map_mul, aeval_X_pow, hPe, pow_succ u k]
          ring
        · refine ⟨cj (P.coeff 0) • X ^ k + (cj (P.coeff 1) * ρ) • X ^ (k - 1) + Q₂,
            H.add_mem (H.add_mem (H.smul_mem _ g2) (H.smul_mem _ g1)) g5, ?_⟩
          rw [map_add, map_add, ev, ev, hQ₂e, hPe, Subfield.coe_mul, hcj, hcj, hρu, hk1]
          simp only [map_add, map_mul]
          ring) (hxy i j)
    -- orders and degrees in `H`
    have ord : ∀ h ∈ H, h ≠ 0 →
        h.natTrailingDegree ∈ ({0, k - 1, k, k + 1, k + m} : Finset ℕ) ∧
          h.natDegree ∈ ({k - m, k - 1, k, k + 1, 2 * k} : Finset ℕ) := fun h hh h0 =>
      shifted_polynomial_hull_orders (↥Qbar) k m hm2 hmk (L * X ^ k) Q₂
        (mul_ne_zero hL0 (pow_ne_zero _ X_ne_zero))
        (by rw [natTrailingDegree_mul_X_pow hL0, add_comm])
        (by rw [natDegree_mul_X_pow k hL0, hLd, two_mul]) hQ₂0 hQ₂d h hh h0
    obtain ⟨hA, hA'⟩ := R16_hull.cards ha
    obtain ⟨hB, hB'⟩ := R16_hull.cards hb
    -- the reflected degree sums lie in `{-1, 0, 1, 2}`
    have hdeg := (R16_hull.rigid hP hm2 hmk hA' hB' (fun s => (P₀.natDegree : ℤ) + k - s)
      (fun t => -(t : ℤ)) (fun _ _ e => by simpa using e) (fun _ _ e => by simpa using e) (by
        rintro _ ⟨f, ⟨hf, hf0⟩, rfl⟩ _ ⟨g, ⟨hg, hg0⟩, rfl⟩
        obtain ⟨h, hh, h0, -, e⟩ := R16_hull.pairs hP₀ hab hf hf0 hg hg0
        have := (ord h hh h0).2
        simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
        omega)).1
    -- some shifted order sum equals `2`
    obtain ⟨-, _, ⟨f, ⟨hf, hf0⟩, rfl⟩, _, ⟨g, ⟨hg, hg0⟩, rfl⟩, e2⟩ := R16_hull.rigid hP hm2 hmk
      hA hB (fun s => (s : ℤ) - ((P₀.natTrailingDegree : ℤ) + k)) (fun t => (t : ℤ))
      (fun _ _ e => by simpa using e) (fun _ _ e => by simpa using e) (by
        rintro _ ⟨f, ⟨hf, hf0⟩, rfl⟩ _ ⟨g, ⟨hg, hg0⟩, rfl⟩
        obtain ⟨h, hh, h0, e, -⟩ := R16_hull.pairs hP₀ hab hf hf0 hg hg0
        have := (ord h hh h0).1
        simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
        omega)
    obtain ⟨h, -, -, et, ed⟩ := R16_hull.pairs hP₀ hab hf hf0 hg hg0
    have hd := hdeg _ ⟨f, ⟨hf, hf0⟩, rfl⟩ _ ⟨g, ⟨hg, hg0⟩, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd e2
    have := natTrailingDegree_le_natDegree h
    omega
