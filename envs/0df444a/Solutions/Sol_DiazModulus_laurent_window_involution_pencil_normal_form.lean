-- Prove2me | solution 1 for DiazModulus.laurent_window_involution_pencil_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:46:40.492454+00:00
-- url     : https://prove2.me/submissions/a951f5f7-28e3-446c-ab07-5a2383d76fcb

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_laurent_window_factor_in_hull_plus_min_degree_line

open Complex ComplexConjugate

/-! # Three free factors for the pencil `(X, X² + β)` put `M` in the involution normal form

Write `N = k + 3`, `H = span {X^(N-1), X^N, X^(N+1)}` and `W = H + M`, with `M` two-dimensional, free
of window terms (`hMc`), every non-zero element of order `≤ N - 2` and degree `≥ N + 2`. By `hMc`,
an element of `W` without window terms lies in `M`. Let `n` be the element of least degree of `M`
(`laurent_window_factor_in_hull_plus_min_degree_line`, with `(p, q) = (X, X² + β)`): every factor
`y` with `X y, (X² + β) y ∈ W` has `X y ∈ H + K n`.
* Two linear functionals (the coefficients of `X^(deg n - 1)` and `X^(N-1)`) kill a non-zero
  combination `y` of the `b_j`. Then `X y ∈ H`, `y = a X^(N-2) + c X^N`, and removing the window
  terms of `(X² + β) y` leaves `β a X^(N-2) + c X^(N+2) ∈ M`. The order and degree bounds give
  `a ≠ 0 ≠ c`, so `X^(N-2) + e X^(N+2) ∈ M` with `e ≠ 0`; by least degree, `n` is a multiple of it.
* Killing the coefficients of `X^(N-2)` and `X^(N-1)` instead gives `y = s X^(N-3) + c X^N +
  s e X^(N+1)`, and `(X² + β) y` leaves `β s X^(N-3) + c X^(N+2) + s e X^(N+3) ∈ M`, with `s ≠ 0`
  by the order bound. Dividing by `s` gives the second generator, and two free elements span `M`.
-/

namespace R18_L5

open DiazModulus Polynomial

variable {K : Type*} [Field K]

/-- Coefficients of an element of the window vanish off the window. -/
theorem win_coeff {k : ℕ} {h : K[X]}
    (hh : h ∈ Submodule.span K ({X ^ (k + 2), X ^ (k + 3), X ^ (k + 4)} : Set K[X]))
    {i : ℕ} (h1 : i ≠ k + 2) (h2 : i ≠ k + 3) (h3 : i ≠ k + 4) : h.coeff i = 0 := by
  induction hh using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> simp [coeff_X_pow, h1, h2, h3]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => simp [hx]

/-- An element of the window is determined by its three window coefficients. -/
theorem win_eq {k : ℕ} {h : K[X]}
    (hh : h ∈ Submodule.span K ({X ^ (k + 2), X ^ (k + 3), X ^ (k + 4)} : Set K[X])) :
    h = C (h.coeff (k + 2)) * X ^ (k + 2) + C (h.coeff (k + 3)) * X ^ (k + 3) +
      C (h.coeff (k + 4)) * X ^ (k + 4) := by
  ext i
  simp only [coeff_add, coeff_C_mul, coeff_X_pow]
  rcases (by omega : i = k + 2 ∨ i = k + 3 ∨ i = k + 4 ∨ (i ≠ k + 2 ∧ i ≠ k + 3 ∧ i ≠ k + 4)) with
    h | h | h | ⟨h1, h2, h3⟩
  · rw [if_pos h, if_neg (by omega), if_neg (by omega), h]; ring
  · rw [if_neg (by omega), if_pos h, if_neg (by omega), h]; ring
  · rw [if_neg (by omega), if_neg (by omega), if_pos h, h]; ring
  · rw [if_neg h1, if_neg h2, if_neg h3, win_coeff hh h1 h2 h3]; ring

theorem gen_mem {S : Set K[X]} {x : K[X]} (hx : x ∈ S) (c : K) :
    C c * x ∈ Submodule.span K S := by
  rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

theorem cXm (p : K[X]) {i : ℕ} (hi : 1 ≤ i) : (X * p).coeff i = p.coeff (i - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp [coeff_X_mul]

theorem ntd_mono {c : K} (hc : c ≠ 0) (m : ℕ) : (C c * X ^ m).natTrailingDegree = m := by
  rw [C_mul_X_pow_eq_monomial, natTrailingDegree_monomial hc]

/-- Membership in the span of four elements. -/
theorem sp4 {a b c n x : K[X]} (hx : x ∈ Submodule.span K ({a, b, c, n} : Set K[X])) :
    ∃ h ∈ Submodule.span K ({a, b, c} : Set K[X]), ∃ t : K, x = h + t • n := by
  have hle : Submodule.span K ({a, b, c, n} : Set K[X]) ≤
      Submodule.span K ({a, b, c} : Set K[X]) ⊔ K ∙ n := by
    rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Submodule.mem_sup_left (Submodule.subset_span (by simp))
    · exact Submodule.mem_sup_left (Submodule.subset_span (by simp))
    · exact Submodule.mem_sup_left (Submodule.subset_span (by simp))
    · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  obtain ⟨h, hh, z, hz, rfl⟩ := Submodule.mem_sup.mp (hle hx)
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨h, hh, t, rfl⟩

/-- Two free elements of a plane span it. -/
theorem pair_eq {M : Submodule K K[X]} (hM2 : Module.finrank K M = 2) {x y : K[X]} (hx : x ∈ M)
    (hy : y ∈ M) (hx0 : x ≠ 0) (hxy : ∀ c : K, c • x ≠ y) : M = Submodule.span K {x, y} := by
  have : FiniteDimensional K M := Module.finite_of_finrank_pos (by omega)
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> assumption
  · rw [hM2, ← Matrix.range_cons_cons_empty x y ![],
      finrank_span_eq_card ((LinearIndependent.pair_iff' hx0).mpr hxy)]
    simp

/-- Two linear functionals kill a non-zero combination of three free vectors. -/
theorem two_kill {S : Submodule K K[X]} {b : Fin 3 → K[X]} (hb : LinearIndependent K b)
    (hbS : ∀ j, b j ∈ S) (f g : K[X] →ₗ[K] K) : ∃ y ∈ S, y ≠ 0 ∧ f y = 0 ∧ g y = 0 := by
  set U := Submodule.span K (Set.range b)
  have hU : Module.finrank K U = 3 := by rw [finrank_span_eq_card hb]; simp
  have : FiniteDimensional K U := Module.finite_of_finrank_pos (by omega)
  have hlt : Module.finrank K (K × K) < Module.finrank K U := by
    rw [hU, Module.finrank_prod, Module.finrank_self]; norm_num
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp
    (LinearMap.ker_ne_bot_of_finrank_lt (f := (f.prod g).comp U.subtype) hlt)
  have hUS : U ≤ S := Submodule.span_le.mpr (Set.range_subset_iff.mpr hbS)
  have hk := LinearMap.mem_ker.mp hu
  have h1 : f u = 0 := by simpa using congrArg Prod.fst hk
  have h2 : g u = 0 := by simpa using congrArg Prod.snd hk
  exact ⟨u, hUS u.2, fun h => hu0 (Subtype.ext h), h1, h2⟩

end R18_L5

open DiazModulus R18_L5 Polynomial in
theorem solution (K : Type*) [Field K] (N : ℕ) (M : Submodule K K[X]) (hM2 : Module.finrank K M = 2) (hN : 3 ≤ N)
    (hMc : ∀ f ∈ M, f.coeff (N - 1) = 0 ∧ f.coeff N = 0 ∧ f.coeff (N + 1) = 0)
    (hMo : ∀ f ∈ M, f ≠ 0 → f.natTrailingDegree + 2 ≤ N)
    (hMd : ∀ f ∈ M, f ≠ 0 → N + 2 ≤ f.natDegree)
    (β : K) (hβ : β ≠ 0) (b : Fin 3 → K[X]) (hb : LinearIndependent K b)
    (hbW : ∀ j, X * b j ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) ∧ (X ^ 2 + C β) * b j ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M)) :
    ∃ e ζ : K, e ≠ 0 ∧ M = Submodule.span K
      ({X ^ (N - 2) + C e * X ^ (N + 2), C β * X ^ (N - 3) + C ζ * X ^ (N + 2) + C e * X ^ (N + 3)} : Set K[X]) := by
  obtain ⟨n, hnM, hn0, hnmin, hn⟩ :=
    DiazModulus.laurent_window_factor_in_hull_plus_min_degree_line K N M hM2 hMd
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 3 := ⟨N - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega, show k + 3 + 1 = k + 4 by omega, show k + 3 + 2 = k + 5 by omega,
    show k + 3 + 3 = k + 6 by omega] at hMc hMd hbW hn ⊢
  set H := Submodule.span K ({X ^ (k + 2), X ^ (k + 3), X ^ (k + 4)} : Set K[X]) with hH
  set W := H ⊔ M with hW
  have hHW : H ≤ W := le_sup_left
  have hXW : ∀ (c : K) (i : ℕ), i = k + 2 ∨ i = k + 3 ∨ i = k + 4 → C c * X ^ i ∈ W := by
    intro c i hi
    rcases hi with rfl | rfl | rfl <;> exact hHW (gen_mem (by simp) c)
  -- an element of `W` without window terms lies in `M`
  have hWM : ∀ f ∈ W, f.coeff (k + 2) = 0 → f.coeff (k + 3) = 0 → f.coeff (k + 4) = 0 → f ∈ M := by
    intro f hf h1 h2 h3
    obtain ⟨h, hh, m, hm, rfl⟩ := Submodule.mem_sup.mp hf
    obtain ⟨m1, m2, m3⟩ := hMc m hm
    simp only [coeff_add, m1, m2, m3, add_zero] at h1 h2 h3
    rw [win_eq hh, h1, h2, h3]
    simpa using hm
  -- the width count of `laurent_window_factor_in_hull_plus_min_degree_line`
  have hL2 : ∀ y, X * y ∈ W → (X ^ 2 + C β) * y ∈ W → ∃ h ∈ H, ∃ t : K, X * y = h + t • n := by
    intro y h1 h2
    exact sp4 (hn X (X ^ 2 + C β) y (by rw [natDegree_X, natDegree_X_pow_add_C]; norm_num) h1 h2)
  have hS : ∀ j, b j ∈ W.comap (LinearMap.mulLeft K X) ⊓
      W.comap (LinearMap.mulLeft K (X ^ 2 + C β)) := fun j => ⟨(hbW j).1, (hbW j).2⟩
  set D := n.natDegree with hD
  have hnD : k + 5 ≤ D := hMd n hnM hn0
  have hlc : n.coeff D ≠ 0 := by rw [hD]; exact mt leadingCoeff_eq_zero.mp hn0
  -- Step 1: the line `X^(N-2) + e X^(N+2)` of `M`
  obtain ⟨y, ⟨hy1, hy2⟩, hy0, hyD, hyN⟩ := two_kill hb hS (lcoeff K (D - 1)) (lcoeff K (k + 2))
  replace hy1 : X * y ∈ W := hy1
  replace hy2 : (X ^ 2 + C β) * y ∈ W := hy2
  change y.coeff (D - 1) = 0 at hyD
  change y.coeff (k + 2) = 0 at hyN
  obtain ⟨h, hh, t, hyeq⟩ := hL2 y hy1 hy2
  have ht : t = 0 := by
    have := congrArg (fun p => p.coeff D) hyeq
    simp only [coeff_add, coeff_smul, smul_eq_mul, cXm y (show 1 ≤ D by omega), hyD,
      win_coeff hh (show D ≠ k + 2 by omega) (by omega) (by omega), zero_add] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hlc
  rw [ht, zero_smul, add_zero] at hyeq
  have hb0 : h.coeff (k + 3) = 0 := by
    rw [← hyeq, cXm y (by omega)]; exact hyN
  set a := h.coeff (k + 2)
  set c := h.coeff (k + 4)
  have hyf : y = C a * X ^ (k + 1) + C c * X ^ (k + 3) := by
    apply mul_left_cancel₀ (X_ne_zero : (X : K[X]) ≠ 0)
    rw [hyeq, win_eq hh, hb0, C_0]
    ring
  set F1 := C (β * a) * X ^ (k + 1) + C c * X ^ (k + 5) with hF1
  have hF1M : F1 ∈ M := by
    have hF1e : F1 = (X ^ 2 + C β) * y - C (a + β * c) * X ^ (k + 3) := by
      rw [hyf, hF1, C_mul, C_add, C_mul]; ring
    apply hWM F1 (by rw [hF1e]; exact sub_mem hy2 (hXW _ _ (by omega))) <;>
      simp only [hF1, coeff_add, coeff_C_mul_X_pow] <;> split_ifs <;> first | omega | simp
  have ha : a ≠ 0 := by
    intro ha
    have hc : c ≠ 0 := by
      intro hc; apply hy0; rw [hyf, ha, hc]; simp
    have hF1c : F1 = C c * X ^ (k + 5) := by rw [hF1, ha]; simp
    have := hMo F1 hF1M (by rw [hF1c]; exact mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero _ X_ne_zero))
    rw [hF1c, ntd_mono hc] at this
    omega
  have hβa : β * a ≠ 0 := mul_ne_zero hβ ha
  have hc : c ≠ 0 := by
    intro hc
    have hF1c : F1 = C (β * a) * X ^ (k + 1) := by rw [hF1, hc]; simp
    have := hMd F1 hF1M (by
      rw [hF1c]; exact mul_ne_zero (C_ne_zero.mpr hβa) (pow_ne_zero _ X_ne_zero))
    rw [hF1c, natDegree_C_mul_X_pow _ _ hβa] at this
    omega
  set e := (β * a)⁻¹ * c with he
  have he0 : e ≠ 0 := mul_ne_zero (inv_ne_zero hβa) hc
  set n0 := X ^ (k + 1) + C e * X ^ (k + 5) with hn0d
  have hn0M : n0 ∈ M := by
    have : n0 = C (β * a)⁻¹ * F1 := by
      rw [hn0d, hF1, mul_add, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, inv_mul_cancel₀ hβa,
        C_1, one_mul]
    rw [this, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hF1M
  have hn0deg : n0.natDegree = k + 5 := by
    rw [hn0d, natDegree_add_eq_right_of_natDegree_lt] <;>
      rw [natDegree_C_mul_X_pow _ _ he0]
    rw [natDegree_X_pow]; omega
  have hn00 : n0 ≠ 0 := by
    intro h0; rw [h0, natDegree_zero] at hn0deg; omega
  have hDe : D = k + 5 := le_antisymm (hn0deg ▸ hnmin n0 hn0M hn00) hnD
  -- `n` is a multiple of `n0`
  set lam := n.coeff (k + 5) / e with hlam
  have hnn0 : n = lam • n0 := by
    set r := n - lam • n0 with hr
    have hrM : r ∈ M := sub_mem hnM (Submodule.smul_mem _ _ hn0M)
    by_contra hne
    have hr0 : r ≠ 0 := sub_ne_zero.mpr hne
    have h1 := hMd r hrM hr0
    have h2 : r.natDegree ≤ k + 5 := by
      refine (natDegree_sub_le _ _).trans (max_le (by omega) ?_)
      exact (natDegree_smul_le _ _).trans hn0deg.le
    have h3 : r.coeff (k + 5) = 0 := by
      simp [hr, hn0d, hlam, coeff_X_pow, div_mul_cancel₀ _ he0]
    have h4 : r.natDegree = k + 5 := by omega
    exact hr0 (leadingCoeff_eq_zero.mp (by rw [leadingCoeff, h4]; exact h3))
  -- Step 2: the second generator
  obtain ⟨y, ⟨hy1, hy2⟩, hy0, hy1c, hy2c⟩ := two_kill hb hS (lcoeff K (k + 1)) (lcoeff K (k + 2))
  replace hy1 : X * y ∈ W := hy1
  replace hy2 : (X ^ 2 + C β) * y ∈ W := hy2
  change y.coeff (k + 1) = 0 at hy1c
  change y.coeff (k + 2) = 0 at hy2c
  obtain ⟨h, hh, t, hyeq⟩ := hL2 y hy1 hy2
  rw [hnn0, smul_smul] at hyeq
  set s := t * lam
  clear_value s
  have ha' : h.coeff (k + 2) = 0 := by
    have := congrArg (fun p => p.coeff (k + 2)) hyeq
    simp only [cXm y (show 1 ≤ k + 2 by omega), coeff_add, coeff_smul, hn0d, coeff_X_pow,
      coeff_C_mul, smul_eq_mul] at this
    simpa [hy1c] using this.symm
  have hb' : h.coeff (k + 3) = 0 := by
    have := congrArg (fun p => p.coeff (k + 3)) hyeq
    simp only [cXm y (show 1 ≤ k + 3 by omega), coeff_add, coeff_smul, hn0d, coeff_X_pow,
      coeff_C_mul, smul_eq_mul] at this
    simpa [hy2c] using this.symm
  set c' := h.coeff (k + 4)
  have hyf : y = C s * X ^ k + C c' * X ^ (k + 3) + C (s * e) * X ^ (k + 4) := by
    apply mul_left_cancel₀ (X_ne_zero : (X : K[X]) ≠ 0)
    rw [hyeq, win_eq hh, ha', hb', hn0d, smul_eq_C_mul, C_0]
    simp only [C_mul]
    ring
  set F2 := C (s * β) * X ^ k + C c' * X ^ (k + 5) + C (s * e) * X ^ (k + 6) with hF2
  have hF2M : F2 ∈ M := by
    have hF2e : F2 = (X ^ 2 + C β) * y - C s * X ^ (k + 2) - C (β * c') * X ^ (k + 3) -
        C (β * (s * e)) * X ^ (k + 4) := by
      rw [hyf, hF2]; simp only [C_mul]; ring
    apply hWM F2 (by
      rw [hF2e]
      exact sub_mem (sub_mem (sub_mem hy2 (hXW _ _ (by omega))) (hXW _ _ (by omega)))
        (hXW _ _ (by omega))) <;>
      simp only [hF2, coeff_add, coeff_C_mul_X_pow] <;> split_ifs <;> first | omega | simp
  have hs : s ≠ 0 := by
    intro hs
    have hc' : c' ≠ 0 := by
      intro hc'; apply hy0; rw [hyf, hs, hc']; simp
    have hF2c : F2 = C c' * X ^ (k + 5) := by rw [hF2, hs]; simp
    have := hMo F2 hF2M (by
      rw [hF2c]; exact mul_ne_zero (C_ne_zero.mpr hc') (pow_ne_zero _ X_ne_zero))
    rw [hF2c, ntd_mono hc'] at this
    omega
  set ζ := s⁻¹ * c'
  have hm2M : C β * X ^ k + C ζ * X ^ (k + 5) + C e * X ^ (k + 6) ∈ M := by
    have : C β * X ^ k + C ζ * X ^ (k + 5) + C e * X ^ (k + 6) = C s⁻¹ * F2 := by
      rw [hF2, mul_add, mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, ← C_mul,
        inv_mul_cancel_left₀ hs, inv_mul_cancel_left₀ hs]
    rw [this, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hF2M
  refine ⟨e, ζ, he0, pair_eq hM2 hn0M hm2M hn00 (fun l hl => hβ ?_)⟩
  have := congrArg (fun p => p.coeff k) hl
  simp [coeff_X_pow] at this
  exact this.symm
