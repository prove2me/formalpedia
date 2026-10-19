-- Prove2me | solution 1 for DiazModulus.laurent_conj_hull_shifted_polynomial_model
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:46:29.631895+00:00
-- url     : https://prove2.me/submissions/f3dbc789-de2e-4a94-8fac-cdc7b4792a94

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The shifted polynomial model of a five-dimensional Laurent hull without `v² P(v)`

Let `v ∉ Q̄` with `v v̄ = 1`, `L = Σ_{|j| ≤ k} c_j v^j` and `W = span_Q̄ {1, v, v̄, L, L̄}` with
`dim W = 5` and no non-zero `v² P(v)` in `W` (`hB`). Take `N = k + 3` and `φ(F) = F(v)/v^N`, a
`Q̄`-linear map `Q̄[X] → ℂ`, injective because `v` is transcendental. Then `φ(X^(N-1)) = v̄`,
`φ(X^N) = 1`, `φ(X^(N+1)) = v`, `φ(F_L) = L` for `F_L = Σ c_j X^(j+N)` and `φ(F_R) = L̄` for
`F_R = Σ c̄_j X^(N-j)` (as `v̄ = v⁻¹`). Let `π` delete the coefficients at `N - 1, N, N + 1`,
`H = span {X^(N-1), X^N, X^(N+1)}` and `M = span {π F_L, π F_R}`, so `hMc` holds.
`φ` maps `H ⊔ M` into `W` and onto it (`F = π F + (F − π F)`), so with injectivity
`φ(F) ∈ W ↔ F ∈ H ⊔ M`. `5 = dim W ≤ dim (H ⊔ M) ≤ 3 + dim M ≤ 5` gives `dim M = 2`.
`hMo`: a non-zero `f ∈ M` of order `≥ N - 1` has order `≥ N + 2` (`hMc`), so `f = X^(N+2) P`
and `φ(f) = v² P(v) ∈ W`; `hB` gives `P = 0`. `hMd`: a non-zero `f ∈ M` of degree `≤ N + 1` has
degree `≤ N - 2`; `W` is conjugation-stable and `conj φ(f) = v² · R(v)` with `R` the reflection
of the conjugate of `f` about `N - 2` (`Polynomial.eval₂_reflect_mul_pow`), so `hB` gives `R = 0`.
-/

namespace R18_C9

open DiazModulus Polynomial

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

/-- Conjugation maps `Q̄` to itself. -/
theorem conj_mem_Qbar {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar :=
  mem_Qbar_iff.2 ((mem_Qbar_iff.1 ha).algHom (starRingEnd ℂ).toRatAlgHom)

/-- Complex conjugation restricted to `Q̄`. -/
noncomputable def cqh : ↥Qbar →+* ↥Qbar where
  toFun a := ⟨conj (a : ℂ), conj_mem_Qbar a.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ (a : ℂ) b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ (a : ℂ) b)

theorem conj_aeval (x : ℂ) (G : (↥Qbar)[X]) : conj (aeval x G) = aeval (conj x) (G.map cqh) := by
  rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]
  rw [show (starRingEnd ℂ).comp (algebraMap (↥Qbar) ℂ) = (algebraMap (↥Qbar) ℂ).comp cqh from
    RingHom.ext fun _ => rfl]

/-- `xᴺ H(x⁻¹)` is the value at `x` of the reflected polynomial. -/
theorem inv_aeval {x : ℂ} (hx : x ≠ 0) (N : ℕ) (H : (↥Qbar)[X]) (hH : H.natDegree ≤ N) :
    x ^ N * aeval x⁻¹ H = aeval x (reflect N H) := by
  have : Invertible x := invertibleOfNonzero hx
  have h := eval₂_reflect_mul_pow (algebraMap (↥Qbar) ℂ) x N (reflect N H)
    (natDegree_reflect_le.trans (max_le le_rfl hH))
  rw [reflect_reflect, invOf_eq_inv] at h
  rw [aeval_def, aeval_def, ← h, mul_comm]

/-- A span whose generators have conjugates in it is conjugation-stable. -/
theorem span_conj_stable {S : Set ℂ} (hS : ∀ x ∈ S, conj x ∈ Submodule.span Qbar S) :
    ∀ w ∈ Submodule.span Qbar S, conj w ∈ Submodule.span Qbar S := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have hcx : conj (c • x) = cqh c • conj x := map_mul conj (c : ℂ) x
    rw [hcx]
    exact Submodule.smul_mem _ _ hx

/-- The shifted evaluation `F ↦ F(v) / vᴺ`. -/
noncomputable def phi (v : ℂ) (N : ℕ) : (↥Qbar)[X] →ₗ[↥Qbar] ℂ where
  toFun F := aeval v F / v ^ N
  map_add' F G := by rw [map_add, add_div]
  map_smul' a F := by
    rw [map_smul, RingHom.id_apply, Subfield.smul_def, Subfield.smul_def, smul_eq_mul,
      smul_eq_mul, mul_div_assoc]

theorem phi_apply (v : ℂ) (N : ℕ) (F : (↥Qbar)[X]) : phi v N F = aeval v F / v ^ N := rfl

/-- The part of `F` at `X^(N-1), X^N, X^(N+1)`. -/
noncomputable def hpart (N : ℕ) (F : (↥Qbar)[X]) : (↥Qbar)[X] :=
  C (F.coeff (N - 1)) * X ^ (N - 1) + C (F.coeff N) * X ^ N + C (F.coeff (N + 1)) * X ^ (N + 1)

theorem hpart_mem (N : ℕ) (F : (↥Qbar)[X]) :
    hpart N F ∈ Submodule.span (↥Qbar) ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set (↥Qbar)[X]) := by
  rw [hpart, C_mul', C_mul', C_mul']
  exact add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem coeff_sub_hpart {N : ℕ} (hN : 1 ≤ N) (F : (↥Qbar)[X]) :
    (F - hpart N F).coeff (N - 1) = 0 ∧ (F - hpart N F).coeff N = 0 ∧
      (F - hpart N F).coeff (N + 1) = 0 := by
  simp only [hpart, coeff_sub, coeff_add, coeff_C_mul_X_pow]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [show N - 1 ≠ N by omega, show N - 1 ≠ N + 1 by omega, show N ≠ N - 1 by omega,
      show N + 1 ≠ N - 1 by omega]

end R18_C9

open DiazModulus R18_C9 in
open Polynomial in
theorem solution
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1) (k : ℕ) (c : ℤ → ℂ) (hc : ∀ j, c j ∈ Qbar)
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ)) = 5)
    (hB : ∀ P : Polynomial ↥Qbar, v ^ 2 * Polynomial.aeval v P ∈ Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ) → P = 0) :
    ∃ (N : ℕ) (M : Submodule (↥Qbar) (↥Qbar)[X]), 3 ≤ N ∧ Module.finrank (↥Qbar) M = 2 ∧
      (∀ f ∈ M, f.coeff (N - 1) = 0 ∧ f.coeff N = 0 ∧ f.coeff (N + 1) = 0) ∧
      (∀ f ∈ M, f ≠ 0 → f.natTrailingDegree + 2 ≤ N) ∧ (∀ f ∈ M, f ≠ 0 → N + 2 ≤ f.natDegree) ∧
      (∀ F : (↥Qbar)[X], aeval v F / v ^ N ∈ Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ) ↔
        F ∈ Submodule.span (↥Qbar) ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set (↥Qbar)[X]) ⊔ M) ∧
      ∀ w ∈ Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ),
        ∃ F ∈ Submodule.span (↥Qbar) ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set (↥Qbar)[X]) ⊔ M,
          aeval v F / v ^ N = w := by
  set L := ∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j with hL
  set W := Submodule.span Qbar ({1, v, conj v, L, conj L} : Set ℂ) with hW
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv1
  have hcv : conj v = v⁻¹ := (inv_eq_of_mul_eq_one_right hv1).symm
  set N := k + 3 with hN
  set γ : ℤ → ↥Qbar := fun j => ⟨c j, hc j⟩ with hγ
  set FL : (↥Qbar)[X] := ∑ j ∈ Finset.Icc (-(k : ℤ)) k, C (γ j) * X ^ (j + N).toNat with hFLd
  set FR : (↥Qbar)[X] := ∑ j ∈ Finset.Icc (-(k : ℤ)) k, C (cqh (γ j)) * X ^ ((N : ℤ) - j).toNat
    with hFRd
  have hFL : phi v N FL = L := by
    rw [phi_apply, div_eq_iff (pow_ne_zero N hv0), mul_comm]
    simp only [hFLd, map_sum, map_mul, aeval_C, aeval_X_pow, am, hL, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : 0 ≤ j + N := by simp only [Finset.mem_Icc] at hj; omega
    rw [← zpow_natCast v (j + N).toNat, Int.toNat_of_nonneg hj', zpow_add₀ hv0, zpow_natCast]
    simp only [hγ]; ring
  have hFR : phi v N FR = conj L := by
    rw [phi_apply, div_eq_iff (pow_ne_zero N hv0), mul_comm]
    simp only [hFRd, map_sum, map_mul, aeval_C, aeval_X_pow, am, hL, Finset.mul_sum, map_zpow₀,
      hcv]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : 0 ≤ (N : ℤ) - j := by simp only [Finset.mem_Icc] at hj; omega
    rw [inv_zpow, ← zpow_natCast v ((N : ℤ) - j).toNat, Int.toNat_of_nonneg hj', zpow_sub₀ hv0,
      zpow_natCast]
    simp only [hγ, cqh, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]; ring
  set H := Submodule.span (↥Qbar) ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set (↥Qbar)[X]) with hH
  set M := Submodule.span (↥Qbar) ({FL - hpart N FL, FR - hpart N FR} : Set (↥Qbar)[X]) with hM
  have hconjW : ∀ w ∈ W, conj w ∈ W := span_conj_stable fun x hx => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> refine Submodule.subset_span ?_ <;> simp
  have hp0 : phi v N (X ^ N) = 1 := by
    rw [phi_apply, map_pow, aeval_X, div_self (pow_ne_zero N hv0)]
  have hp1 : phi v N (X ^ (N + 1)) = v := by
    rw [phi_apply, map_pow, aeval_X, pow_succ]; field_simp
  have hpm : phi v N (X ^ (N - 1)) = conj v := by
    rw [phi_apply, map_pow, aeval_X, hcv, show v ^ N = v ^ (N - 1) * v by
      rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ N by omega)]]
    field_simp
  have hHW : H ≤ W.comap (phi v N) := by
    rw [hH, Submodule.span_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      Submodule.mem_comap, hp0, hp1, hpm]
    exact ⟨Submodule.subset_span (by simp), Submodule.subset_span (by simp),
      Submodule.subset_span (by simp)⟩
  have hMW : M ≤ W.comap (phi v N) := by
    rw [hM, Submodule.span_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      Submodule.mem_comap, map_sub, hFL, hFR]
    exact ⟨sub_mem (Submodule.subset_span (by simp)) (hHW (hpart_mem N FL)),
      sub_mem (Submodule.subset_span (by simp)) (hHW (hpart_mem N FR))⟩
  have hsplit : ∀ F, F - hpart N F ∈ M → F ∈ H ⊔ M := fun F hF => by
    rw [← sub_add_cancel F (hpart N F)]
    exact add_mem (Submodule.mem_sup_right hF) (Submodule.mem_sup_left (hpart_mem N F))
  have hWsup : W ≤ (H ⊔ M).map (phi v N) := by
    rw [hW, Submodule.span_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      Submodule.mem_map]
    exact ⟨⟨_, Submodule.mem_sup_left (Submodule.subset_span (by simp)), hp0⟩,
      ⟨_, Submodule.mem_sup_left (Submodule.subset_span (by simp)), hp1⟩,
      ⟨_, Submodule.mem_sup_left (Submodule.subset_span (by simp)), hpm⟩,
      ⟨_, hsplit FL (Submodule.subset_span (by simp)), hFL⟩,
      ⟨_, hsplit FR (Submodule.subset_span (by simp)), hFR⟩⟩
  have hinj : ∀ F G, phi v N F = phi v N G → F = G := fun F G h => by
    rw [phi_apply, phi_apply, div_left_inj' (pow_ne_zero N hv0)] at h
    exact sub_eq_zero.1 (aeval_eq_zero hv (by rw [map_sub, h, sub_self]))
  have hiff : ∀ F : (↥Qbar)[X], aeval v F / v ^ N ∈ W ↔ F ∈ H ⊔ M := fun F =>
    ⟨fun h => by
      obtain ⟨G, hG, hGF⟩ := Submodule.mem_map.1 (hWsup h)
      rwa [← hinj G F hGF],
    fun h => (sup_le hHW hMW) h⟩
  have hMc : ∀ f ∈ M, f.coeff (N - 1) = 0 ∧ f.coeff N = 0 ∧ f.coeff (N + 1) = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> exact coeff_sub_hpart (by omega) _
    | zero => simp
    | add x y _ _ hx hy => simp [coeff_add, hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2]
    | smul a x _ hx => simp [coeff_smul, hx.1, hx.2.1, hx.2.2]
  refine ⟨N, M, by omega, ?_, hMc, ?_, ?_, hiff, fun w hw => ?_⟩
  · classical
    have hH3 : Module.finrank (↥Qbar) H ≤ 3 := by
      have := finrank_span_finset_le_card (R := ↥Qbar)
        ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Finset (↥Qbar)[X])
      simp only [Finset.coe_insert, Finset.coe_singleton] at this
      exact this.trans Finset.card_le_three
    have hM2 : Module.finrank (↥Qbar) M ≤ 2 := by
      have := finrank_span_finset_le_card (R := ↥Qbar)
        ({FL - hpart N FL, FR - hpart N FR} : Finset (↥Qbar)[X])
      simp only [Finset.coe_insert, Finset.coe_singleton] at this
      exact this.trans Finset.card_le_two
    have : FiniteDimensional (↥Qbar) H := FiniteDimensional.span_of_finite _ (Set.toFinite _)
    have : FiniteDimensional (↥Qbar) M := FiniteDimensional.span_of_finite _ (Set.toFinite _)
    have e1 := Submodule.finrank_mono hWsup
    have e2 := Submodule.finrank_map_le (phi v N) (H ⊔ M)
    have e3 := Submodule.finrank_add_le_finrank_add_finrank H M
    omega
  · intro f hf hf0
    by_contra hlt
    obtain ⟨h1, h2, h3⟩ := hMc f hf
    have hdvd : X ^ (N + 2) ∣ f := by
      rw [X_pow_dvd_iff]
      intro d hd
      by_cases hdN : d < N - 1
      · exact coeff_eq_zero_of_lt_natTrailingDegree (by omega)
      · rcases (show d = N - 1 ∨ d = N ∨ d = N + 1 by omega) with rfl | rfl | rfl <;> assumption
    obtain ⟨P, rfl⟩ := hdvd
    have hP := hB P (by
      have := (hiff _).2 (Submodule.mem_sup_right hf)
      convert this using 1
      rw [map_mul, map_pow, aeval_X, pow_add, mul_comm (v ^ N), mul_assoc, mul_div_assoc,
        mul_div_cancel_left₀ _ (pow_ne_zero N hv0)])
    exact hf0 (by rw [hP, mul_zero])
  · intro f hf hf0
    by_contra hlt
    obtain ⟨h1, h2, h3⟩ := hMc f hf
    have hlc : f.coeff f.natDegree ≠ 0 := leadingCoeff_ne_zero.2 hf0
    have hd : f.natDegree ≤ N - 2 := by
      by_contra hd'
      rcases (show f.natDegree = N - 1 ∨ f.natDegree = N ∨ f.natDegree = N + 1 by omega)
        with h | h | h
      · exact hlc (by rw [h]; exact h1)
      · exact hlc (by rw [h]; exact h2)
      · exact hlc (by rw [h]; exact h3)
    have hfc : (f.map cqh).natDegree ≤ N - 2 := natDegree_map_le.trans hd
    have hmem := hconjW _ ((hiff f).2 (Submodule.mem_sup_right hf))
    have hval : conj (aeval v f / v ^ N) = v ^ 2 * aeval v (reflect (N - 2) (f.map cqh)) := by
      rw [← inv_aeval hv0 (N - 2) _ hfc, map_div₀, map_pow, conj_aeval, hcv, inv_pow,
        div_inv_eq_mul, show v ^ N = v ^ 2 * v ^ (N - 2) by
          rw [← pow_add, Nat.add_sub_cancel' (show 2 ≤ N by omega)]]
      ring
    have hP := hB _ (hval ▸ hmem)
    rw [reflect_eq_zero_iff] at hP
    exact hf0 ((Polynomial.map_eq_zero_iff cqh.injective).1 hP)
  · obtain ⟨F, hF, hFw⟩ := Submodule.mem_map.1 (hWsup hw)
    exact ⟨F, hF, hFw⟩
