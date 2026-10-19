-- Prove2me | solution 1 for DiazModulus.laurent_window_degree_one_pencil_factor_space
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:46:37.839934+00:00
-- url     : https://prove2.me/submissions/7ca097eb-7eaa-4ff9-8140-27adb7913567

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_laurent_window_factor_in_hull_plus_min_degree_line

open Complex ComplexConjugate

/-! # Three free factors for the pencil `(1, X)` make `H_N + M` equal to `span(H_N, G, X G)`

Write `H = span {X^(N-1), X^N, X^(N+1)}` and `W = H + M`, with `M` two-dimensional, every non-zero
element of order at most `N - 2` and degree at least `N + 2`.
* Two linear functionals (the coefficients of `X^(N-1)` and `X^N`) kill a non-zero combination `G`
  of the three free `b_j`; it still has `G, X G ∈ W`.
* `laurent_window_factor_in_hull_plus_min_degree_line` with `(p, q) = (1, X)` puts every `F` with
  `F, X F ∈ W` in `H + K n`, `n` the element of least degree of `M`.
* If `F ∈ H` and `X F ∈ W`, the `M`-part of `X F` has order `≥ N - 1`, so it is `0`, and the
  coefficient of `X^(N+1)` in `F` vanishes. Hence `G = h + μ n` with `μ ≠ 0`, and every such `F`
  is `F - (t/μ) G ∈ span(X^(N-1), X^N)` plus a multiple of `G`.
* Write `X G = h'' + m''`. Then `deg m'' = deg n + 1`, so `n` and `m''` span `M`, and both lie in
  `span(H, G, X G)`, which is therefore `W`.
-/

namespace R18_L4

open DiazModulus Polynomial

variable {K : Type*} [Field K]

/-- Coefficients of an element of the window vanish off the window. -/
theorem win_coeff {N : ℕ} {h : K[X]}
    (hh : h ∈ Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]))
    {i : ℕ} (h1 : i ≠ N - 1) (h2 : i ≠ N) (h3 : i ≠ N + 1) : h.coeff i = 0 := by
  induction hh using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> simp [coeff_X_pow, h1, h2, h3]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => simp [hx]

/-- An element of the window is determined by its three window coefficients. -/
theorem win_eq {N : ℕ} (hN : 1 ≤ N) {h : K[X]}
    (hh : h ∈ Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X])) :
    h = C (h.coeff (N - 1)) * X ^ (N - 1) + C (h.coeff N) * X ^ N +
      C (h.coeff (N + 1)) * X ^ (N + 1) := by
  ext i
  simp only [coeff_add, coeff_C_mul, coeff_X_pow]
  rcases (by omega : i = N - 1 ∨ i = N ∨ i = N + 1 ∨ (i ≠ N - 1 ∧ i ≠ N ∧ i ≠ N + 1)) with
    h | h | h | ⟨h1, h2, h3⟩
  · rw [if_pos h, if_neg (by omega), if_neg (by omega), h]; ring
  · rw [if_neg (by omega), if_pos h, if_neg (by omega), h]; ring
  · rw [if_neg (by omega), if_neg (by omega), if_pos h, h]; ring
  · rw [if_neg h1, if_neg h2, if_neg h3, win_coeff hh h1 h2 h3]; ring

theorem gen_mem {S : Set K[X]} {x : K[X]} (hx : x ∈ S) (c : K) :
    C c * x ∈ Submodule.span K S := by
  rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

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

end R18_L4

open DiazModulus R18_L4 Polynomial in
theorem solution (K : Type*) [Field K] (N : ℕ) (M : Submodule K K[X]) (hM2 : Module.finrank K M = 2)
    (hMo : ∀ f ∈ M, f ≠ 0 → f.natTrailingDegree + 2 ≤ N)
    (hMd : ∀ f ∈ M, f ≠ 0 → N + 2 ≤ f.natDegree)
    (b : Fin 3 → K[X]) (hb : LinearIndependent K b)
    (hbW : ∀ j, b j ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) ∧ X * b j ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M)) :
    ∃ G ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M), X * G ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) ∧
      (∀ F : K[X], F ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) → X * F ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) →
        F ∈ Submodule.span K ({X ^ (N - 1), X ^ N, G} : Set K[X])) ∧
      (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) = Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1), G, X * G} : Set K[X]) := by
  set H := Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) with hH
  set W := H ⊔ M with hW
  have : FiniteDimensional K M := Module.finite_of_finrank_pos (by omega)
  obtain ⟨f0, hf0, hf00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := M)
    (by intro h; rw [h, finrank_bot] at hM2; omega)
  have hN : 2 ≤ N := by have := hMo f0 hf0 hf00; omega
  obtain ⟨n, hnM, hn0, -, hn⟩ :=
    DiazModulus.laurent_window_factor_in_hull_plus_min_degree_line K N M hM2 hMd
  have hnd : N + 2 ≤ n.natDegree := hMd n hnM hn0
  have hHW : H ≤ W := le_sup_left
  have hMW : M ≤ W := le_sup_right
  -- every `F` with `F, X F ∈ W` lies in `H + K n`
  have hV1 : ∀ F, F ∈ W → X * F ∈ W → ∃ h ∈ H, ∃ t : K, F = h + t • n := by
    intro F hF hXF
    have := hn 1 X F (by simp) (by rwa [one_mul]) hXF
    rw [one_mul] at this
    exact sp4 this
  -- if `F ∈ H` and `X F ∈ W`, then `F` has no `X^(N+1)` term
  have hV1H : ∀ F, F ∈ H → X * F ∈ W → F.coeff (N + 1) = 0 := by
    intro F hF hXF
    obtain ⟨h', hh', m', hm', hsum⟩ := Submodule.mem_sup.mp hXF
    have hm'e : m' = X * F - h' := by rw [← hsum]; ring
    have hm0 : m' = 0 := by
      by_contra hne
      have h1 := hMo m' hm' hne
      have h2 : N - 1 ≤ m'.natTrailingDegree := by
        apply le_natTrailingDegree hne
        intro i hi
        rw [hm'e, coeff_sub, win_coeff hh' (by omega) (by omega) (by omega)]
        rcases i with _ | i
        · simp
        · rw [coeff_X_mul, win_coeff hF (by omega) (by omega) (by omega)]; simp
      omega
    rw [hm0, add_zero] at hsum
    have := congrArg (fun p => p.coeff (N + 1 + 1)) hsum
    simp only [coeff_X_mul] at this
    rw [← this, win_coeff hh' (by omega) (by omega) (by omega)]
  -- the factor `G`
  have hS : ∀ j, b j ∈ W ⊓ W.comap (LinearMap.mulLeft K X) := fun j => ⟨(hbW j).1, (hbW j).2⟩
  obtain ⟨G, ⟨hGW, hXGW⟩, hG0, hG1, hG2⟩ := two_kill hb hS (lcoeff K (N - 1)) (lcoeff K N)
  replace hXGW : X * G ∈ W := hXGW
  change G.coeff (N - 1) = 0 at hG1
  change G.coeff N = 0 at hG2
  obtain ⟨hG, hGH, μ, hGeq⟩ := hV1 G hGW hXGW
  have hμ : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hGeq
    subst hGeq
    apply hG0
    rw [win_eq (by omega) hGH, hG1, hG2, hV1H _ hGH hXGW]
    simp
  have hhd : ∀ h ∈ H, h.natDegree ≤ N + 1 := fun h hh =>
    natDegree_le_iff_coeff_eq_zero.mpr (fun i hi => win_coeff hh (by omega) (by omega) (by omega))
  have hGd : G.natDegree = n.natDegree := by
    rw [hGeq, natDegree_add_eq_right_of_natDegree_lt, natDegree_smul _ hμ]
    rw [natDegree_smul _ hμ]
    have := hhd hG hGH
    omega
  have hG0' : G ≠ 0 := hG0
  have hXGd : (X * G).natDegree = n.natDegree + 1 := by rw [natDegree_X_mul hG0', hGd]
  obtain ⟨h'', hh'', m'', hm'', hsum''⟩ := Submodule.mem_sup.mp hXGW
  have hm''e : m'' = X * G - h'' := by rw [← hsum'']; ring
  have hm''d : m''.natDegree = n.natDegree + 1 := by
    rw [hm''e, natDegree_sub_eq_left_of_natDegree_lt (by have := hhd h'' hh''; omega), hXGd]
  have hMeq : M = Submodule.span K {n, m''} := pair_eq hM2 hnM hm'' hn0 (fun c hc => by
    have := natDegree_smul_le c n
    rw [hc] at this
    omega)
  refine ⟨G, hGW, hXGW, ?_, ?_⟩
  · intro F hF hXF
    obtain ⟨hF', hhF, t, hFeq⟩ := hV1 F hF hXF
    set D := F - (t / μ) • G with hD
    have hDH : D ∈ H := by
      have : D = hF' - (t / μ) • hG := by
        rw [hD, hFeq, hGeq, smul_add, smul_smul, div_mul_cancel₀ _ hμ]; abel
      rw [this]
      exact sub_mem hhF (Submodule.smul_mem _ _ hGH)
    have hXD : X * D ∈ W := by
      rw [hD, mul_sub, mul_smul_comm]
      exact sub_mem hXF (Submodule.smul_mem _ _ hXGW)
    have hF2 : F = D + C (t / μ) * G := by rw [hD, smul_eq_C_mul]; ring
    rw [hF2, win_eq (by omega) hDH, hV1H D hDH hXD, C_0, zero_mul, add_zero]
    exact add_mem (add_mem (gen_mem (by simp) _) (gen_mem (by simp) _)) (gen_mem (by simp) _)
  · set S5 := Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1), G, X * G} : Set K[X])
    have hHS : H ≤ S5 := by
      apply Submodule.span_mono
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto
    have hGS : G ∈ S5 := Submodule.subset_span (by simp)
    have hXGS : X * G ∈ S5 := Submodule.subset_span (by simp)
    apply le_antisymm
    · refine sup_le hHS ?_
      rw [hMeq, Submodule.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · have : z = μ⁻¹ • (G - hG) := by
          rw [hGeq, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hμ, one_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (sub_mem hGS (hHS hGH))
      · rw [hm''e]
        exact sub_mem hXGS (hHS hh'')
    · rw [Submodule.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl
      · exact hHW (Submodule.subset_span (by simp))
      · exact hHW (Submodule.subset_span (by simp))
      · exact hHW (Submodule.subset_span (by simp))
      · exact hGW
      · exact hXGW
