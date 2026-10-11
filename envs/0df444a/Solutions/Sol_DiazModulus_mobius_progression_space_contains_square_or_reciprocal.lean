-- Prove2me | solution 1 for DiazModulus.mobius_progression_space_contains_square_or_reciprocal
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:06:43.367984+00:00
-- url     : https://prove2.me/submissions/471b5837-e33e-4737-b04e-e1612e9e67ee

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A Möbius progression space contains `u²`, `u⁻²` or some `(u − b)⁻¹`

Write `A = αu + β`, `G = γu + δ`, `D = αδ − βγ ≠ 0` and `c' = c / G³` (`G ≠ 0` as `u ∉ Q̄`).
Each `c hᵏ = c' Aᵏ G³⁻ᵏ`, and since `δA − βG = Du`, `−γA + αG = D`, expanding products of three
linear forms in `A, G` shows `c' uʲ ∈ W` for `j ≤ 3`, hence `c' q(u) ∈ W` for every `q ∈ Q̄[X]≤3`.
The spaces `H = ⟨1, u, u⁻¹⟩` and `P' = ⟨c' uʲ⟩` have dimensions 3 and 4 (`u` is transcendental),
and `H ⊔ P' ≤ W` has dimension at most 5, so `H ⊓ P' ≠ 0` (Grassmann's formula). A non-zero
`x ∈ H ⊓ P'` gives polynomials `p ≠ 0` (degree ≤ 3) and `r ≠ 0` (degree ≤ 2) with
`F p(u) = r(u)`, `F = c'u`. Induction on `deg p`: if `p` is constant, `F` is a polynomial of degree
≤ 2 in `u` and `u³ ∈ F·Q̄[u]≤3 + Q̄[u]≤2`; otherwise `p` has a root `b ∈ Q̄`; if `r(b) = 0` cancel
`u − b`, else `(u − b)⁻¹ = F q(u) + s(u)` with `q = p/((X − b) r(b))`. Dividing by `u` puts
`u²`, `u⁻²` (if `b = 0`) or `(u(u − b))⁻¹`, hence `(u − b)⁻¹`, in `W`.
-/

namespace R11_mobius

open DiazModulus Polynomial

theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem quad_eval {q : (↥Qbar)[X]} (hq : q.natDegree ≤ 2) (z : ℂ) :
    aeval z q = (q.coeff 0 : ℂ) + q.coeff 1 * z + q.coeff 2 * z ^ 2 := by
  rw [aeval_eq_sum_range' (n := 3) (by omega)]
  simp [Finset.sum_range_succ, Subfield.smul_def]

theorem cubic_eval {q : (↥Qbar)[X]} (hq : q.natDegree ≤ 3) (z : ℂ) :
    aeval z q = (q.coeff 0 : ℂ) + q.coeff 1 * z + q.coeff 2 * z ^ 2 + q.coeff 3 * z ^ 3 := by
  rw [aeval_eq_sum_range' (n := 4) (by omega)]
  simp [Finset.sum_range_succ, Subfield.smul_def]

theorem cubic_zero {u : ℂ} (hu : u ∉ Qbar) (a₀ a₁ a₂ a₃ : ↥Qbar)
    (h : (a₀ : ℂ) + a₁ * u + a₂ * u ^ 2 + a₃ * u ^ 3 = 0) :
    a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 := by
  have hP := aeval_eq_zero hu (P := C a₀ + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3)
    (by simpa [am] using h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using congrArg (coeff · 0) hP
  · simpa using congrArg (coeff · 1) hP
  · simpa using congrArg (coeff · 2) hP
  · simpa using congrArg (coeff · 3) hP

theorem exists_root {p : (↥Qbar)[X]} (hp : 0 < p.natDegree) : ∃ b : ↥Qbar, p.IsRoot b := by
  have hp0 : p ≠ 0 := ne_zero_of_natDegree_gt hp
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective (k := ℂ)
    (R := ↥Qbar) Subtype.val_injective p (by
      rw [degree_eq_natDegree hp0]; exact_mod_cast hp.ne')
  by_cases hzq : z ∈ Qbar
  · refine ⟨⟨z, hzq⟩, ?_⟩
    have : aeval (algebraMap (↥Qbar) ℂ ⟨z, hzq⟩) p = 0 := hz
    rw [aeval_algebraMap_apply, coe_aeval_eq_eval] at this
    exact Subtype.val_injective (by simpa using this)
  · exact absurd (aeval_eq_zero hzq hz) hp0

/-- From one relation `F p(u) = r(u)`, `F` reaches `u³` or some `(u − b)⁻¹` modulo `Q̄[u]≤2`. -/
theorem key {u : ℂ} (hu : u ∉ Qbar) (F : ℂ) (n : ℕ) :
    ∀ p r : (↥Qbar)[X], p.natDegree ≤ n → n ≤ 3 → p ≠ 0 → r ≠ 0 → r.natDegree ≤ 2 →
      F * aeval u p = aeval u r →
      ∃ q s : (↥Qbar)[X], q.natDegree ≤ 3 ∧ s.natDegree ≤ 2 ∧
        (u ^ 3 = F * aeval u q + aeval u s ∨
          ∃ b : ↥Qbar, (u - b)⁻¹ = F * aeval u q + aeval u s) := by
  induction n with
  | zero =>
    intro p r hp _ hp0 hr0 hr h
    have hpC := eq_C_of_natDegree_le_zero hp
    have hp₀ : p.coeff 0 ≠ 0 := fun e => hp0 (by rw [hpC, e, map_zero])
    rw [hpC, aeval_C, am, quad_eval hr] at h
    by_cases h2 : r.coeff 2 = 0
    · by_cases h1 : r.coeff 1 = 0
      · have h0 : r.coeff 0 ≠ 0 := by
          intro h0; apply hr0; ext i
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ 2 < i) with rfl | rfl | rfl | hi
          · simpa using h0
          · simpa using h1
          · simpa using h2
          · simp [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hr hi)]
        refine ⟨C (p.coeff 0 / r.coeff 0) * X ^ 3, 0, by compute_degree!, by simp, Or.inl ?_⟩
        have hc : (r.coeff 0 : ℂ) * (r.coeff 0 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast h0)
        simp only [h1, h2] at h
        simp only [map_mul, aeval_C, am, map_pow, aeval_X, map_zero, add_zero]
        push_cast at h ⊢
        linear_combination (-((r.coeff 0 : ℂ)⁻¹ * u ^ 3)) * h - u ^ 3 * hc
      · refine ⟨C (p.coeff 0 / r.coeff 1) * X ^ 2, C (-(r.coeff 0 / r.coeff 1)) * X ^ 2,
          by compute_degree!, by compute_degree!, Or.inl ?_⟩
        have hc : (r.coeff 1 : ℂ) * (r.coeff 1 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast h1)
        simp only [h2] at h
        simp only [map_mul, aeval_C, am, map_pow, aeval_X]
        push_cast at h ⊢
        linear_combination (-((r.coeff 1 : ℂ)⁻¹ * u ^ 2)) * h - u ^ 3 * hc
    · refine ⟨C (p.coeff 0 / r.coeff 2) * X,
        C (-(r.coeff 0 / r.coeff 2)) * X + C (-(r.coeff 1 / r.coeff 2)) * X ^ 2,
        by compute_degree!, by compute_degree!, Or.inl ?_⟩
      have hc : (r.coeff 2 : ℂ) * (r.coeff 2 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast h2)
      simp only [map_mul, map_add, aeval_C, am, map_pow, aeval_X]
      push_cast at h ⊢
      linear_combination (-((r.coeff 2 : ℂ)⁻¹ * u)) * h - u ^ 3 * hc
  | succ n ih =>
    intro p r hp hn hp0 hr0 hr h
    by_cases hpn : p.natDegree ≤ n
    · exact ih p r hpn (by omega) hp0 hr0 hr h
    obtain ⟨b, hb⟩ := exists_root (p := p) (by omega)
    have hpp : (X - C b) * (p /ₘ (X - C b)) = p := mul_divByMonic_eq_iff_isRoot.2 hb
    have hp'deg : (p /ₘ (X - C b)).natDegree ≤ n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C b), natDegree_X_sub_C]; omega
    have hp'0 : p /ₘ (X - C b) ≠ 0 := by
      intro e; rw [e, mul_zero] at hpp; exact hp0 hpp.symm
    have hub : u - (b : ℂ) ≠ 0 := sub_ne_zero.2 (fun e => hu (e ▸ b.2))
    have hev : ∀ f : (↥Qbar)[X], aeval u ((X - C b) * f) = (u - b) * aeval u f := by
      intro f; simp [am]
    rw [← hpp, hev] at h
    by_cases hrb : r.IsRoot b
    · have hrr : (X - C b) * (r /ₘ (X - C b)) = r := mul_divByMonic_eq_iff_isRoot.2 hrb
      have hr'0 : r /ₘ (X - C b) ≠ 0 := by
        intro e; rw [e, mul_zero] at hrr; exact hr0 hrr.symm
      have hr'deg : (r /ₘ (X - C b)).natDegree ≤ 2 := by
        rw [natDegree_divByMonic _ (monic_X_sub_C b)]; omega
      rw [← hrr, hev] at h
      exact ih _ _ hp'deg (by omega) hp'0 hr'0 hr'deg
        (mul_left_cancel₀ hub (by linear_combination h))
    · have hrb0 : r.eval b ≠ 0 := hrb
      have hrr : (X - C b) * ((r - C (r.eval b)) /ₘ (X - C b)) = r - C (r.eval b) :=
        mul_divByMonic_eq_iff_isRoot.2 (by simp)
      have hr₂deg : ((r - C (r.eval b)) /ₘ (X - C b)).natDegree ≤ 2 := by
        rw [natDegree_divByMonic _ (monic_X_sub_C b)]
        have : (r - C (r.eval b)).natDegree ≤ 2 :=
          (natDegree_sub_le _ _).trans (by simp [hr])
        omega
      have hE : (u - b) * aeval u ((r - C (r.eval b)) /ₘ (X - C b)) =
          aeval u r - ((r.eval b : ↥Qbar) : ℂ) := by
        rw [← hev, hrr]; simp [am]
      refine ⟨C (r.eval b)⁻¹ * (p /ₘ (X - C b)),
        -(C (r.eval b)⁻¹ * ((r - C (r.eval b)) /ₘ (X - C b))), ?_, ?_, Or.inr ⟨b, ?_⟩⟩
      · exact (natDegree_C_mul_le _ _).trans (by omega)
      · rw [natDegree_neg]; exact (natDegree_C_mul_le _ _).trans hr₂deg
      · have hc : ((r.eval b : ↥Qbar) : ℂ) * ((r.eval b : ↥Qbar) : ℂ)⁻¹ = 1 :=
          mul_inv_cancel₀ (by exact_mod_cast hrb0)
        have hc2 : (u - b) * (u - b)⁻¹ = 1 := mul_inv_cancel₀ hub
        simp only [map_neg, map_mul, aeval_C, am]
        push_cast
        set P' := aeval u (p /ₘ (X - C b))
        set R₂ := aeval u ((r - C (r.eval b)) /ₘ (X - C b))
        set i := (u - (b : ℂ))⁻¹
        set j := ((r.eval b : ↥Qbar) : ℂ)⁻¹
        linear_combination (-(j * i)) * h + (j * i) * hE + (j * (F * P' - R₂)) * hc2 - i * hc

/-- A product of three `Q̄`-linear forms in `A, G`, times `c / G³`, lies in the span of the
`c (A/G)ᵏ`. -/
theorem prod3_mem (S : Submodule (↥Qbar) ℂ) {c A G : ℂ} (hG : G ≠ 0)
    (hm : ∀ k : ℕ, k < 4 → c * (A / G) ^ k ∈ S) {x y z w e f : ℂ} (hx : x ∈ Qbar)
    (hy : y ∈ Qbar) (hz : z ∈ Qbar) (hw : w ∈ Qbar) (he : e ∈ Qbar) (hf : f ∈ Qbar) :
    c / G ^ 3 * ((x * A + y * G) * (z * A + w * G) * (e * A + f * G)) ∈ S := by
  have hsm : ∀ {k v : ℂ}, k ∈ Qbar → v ∈ S → k * v ∈ S := fun hk hv => S.smul_mem ⟨_, hk⟩ hv
  have key : c / G ^ 3 * ((x * A + y * G) * (z * A + w * G) * (e * A + f * G)) =
      (x * z * e) * (c * (A / G) ^ 3) + (x * z * f + x * w * e + y * z * e) * (c * (A / G) ^ 2) +
        (x * w * f + y * w * e + y * z * f) * (c * (A / G) ^ 1) + (y * w * f) * (c * (A / G) ^ 0) := by
    field_simp; ring
  rw [key]
  refine add_mem (add_mem (add_mem (hsm ?_ (hm 3 (by norm_num))) (hsm ?_ (hm 2 (by norm_num))))
    (hsm ?_ (hm 1 (by norm_num)))) (hsm ?_ (hm 0 (by norm_num)))
  · exact mul_mem (mul_mem hx hz) he
  · exact add_mem (add_mem (mul_mem (mul_mem hx hz) hf) (mul_mem (mul_mem hx hw) he))
      (mul_mem (mul_mem hy hz) he)
  · exact add_mem (add_mem (mul_mem (mul_mem hx hw) hf) (mul_mem (mul_mem hy hw) he))
      (mul_mem (mul_mem hy hz) hf)
  · exact mul_mem (mul_mem hy hw) hf

end R11_mobius

open DiazModulus R11_mobius Polynomial in
theorem solution
    (u : ℂ) (hu : u ∉ Qbar) (α β γ δ c : ℂ) (hα : α ∈ Qbar) (hβ : β ∈ Qbar) (hγ : γ ∈ Qbar)
    (hδ : δ ∈ Qbar) (hdet : α * δ - β * γ ≠ 0) (hc : c ≠ 0)
    (hdim : Module.finrank (↥Qbar) (Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
      Set.range (fun k : Fin 4 => c * ((α * u + β) / (γ * u + δ)) ^ (k : ℕ)))) = 5) :
    u ^ 2 ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
        Set.range (fun k : Fin 4 => c * ((α * u + β) / (γ * u + δ)) ^ (k : ℕ))) ∨
      (u ^ 2)⁻¹ ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
        Set.range (fun k : Fin 4 => c * ((α * u + β) / (γ * u + δ)) ^ (k : ℕ))) ∨
      ∃ b ∈ Qbar, b ≠ 0 ∧ (u - b)⁻¹ ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
        Set.range (fun k : Fin 4 => c * ((α * u + β) / (γ * u + δ)) ^ (k : ℕ))) := by
  set W := Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
    Set.range (fun k : Fin 4 => c * ((α * u + β) / (γ * u + δ)) ^ (k : ℕ))) with hW
  have hsm : ∀ {k v : ℂ}, k ∈ Qbar → v ∈ W → k * v ∈ W := fun hk hv => W.smul_mem ⟨_, hk⟩ hv
  have h1 : (1 : ℂ) ∈ W := Submodule.subset_span (Or.inl (by simp))
  have hu1 : u ∈ W := Submodule.subset_span (Or.inl (by simp))
  have hui : u⁻¹ ∈ W := Submodule.subset_span (Or.inl (by simp))
  have hP : ∀ k : ℕ, k < 4 → c * ((α * u + β) / (γ * u + δ)) ^ k ∈ W :=
    fun k hk => Submodule.subset_span (Or.inr ⟨⟨k, hk⟩, rfl⟩)
  have hu0 : u ≠ 0 := fun e => hu (e ▸ zero_mem _)
  have hG : γ * u + δ ≠ 0 := by
    intro e
    by_cases hγ0 : γ = 0
    · have hδ0 : δ = 0 := by rw [hγ0] at e; simpa using e
      exact hdet (by rw [hγ0, hδ0]; ring)
    · exact hu (by
        have : u = -δ / γ := by field_simp; linear_combination e
        rw [this]; exact div_mem (neg_mem hδ) hγ)
  have hDi : (α * δ - β * γ)⁻¹ ∈ Qbar :=
    inv_mem (sub_mem (mul_mem hα hδ) (mul_mem hβ hγ))
  -- `c' uʲ ∈ W` for `j ≤ 3`
  have hcu : ∀ j : ℕ, j ≤ 3 → c / (γ * u + δ) ^ 3 * u ^ j ∈ W := by
    intro j hj
    have nγ := neg_mem hγ
    have nβ := neg_mem hβ
    have e1 : δ * (α * u + β) + -β * (γ * u + δ) = (α * δ - β * γ) * u := by ring
    have e2 : -γ * (α * u + β) + α * (γ * u + δ) = α * δ - β * γ := by ring
    have hD3 : ((α * δ - β * γ)⁻¹) ^ 3 * (α * δ - β * γ) ^ 3 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hdet, one_pow]
    interval_cases j
    · have := prod3_mem W hG hP nγ hα nγ hα nγ hα
      simp only [e2] at this
      have e : c / (γ * u + δ) ^ 3 * u ^ 0 = ((α * δ - β * γ)⁻¹) ^ 3 *
          (c / (γ * u + δ) ^ 3 * ((α * δ - β * γ) * (α * δ - β * γ) * (α * δ - β * γ))) := by
        linear_combination (-(c / (γ * u + δ) ^ 3 * u ^ 0)) * hD3
      rw [e]; exact hsm (pow_mem hDi 3) this
    · have := prod3_mem W hG hP hδ nβ nγ hα nγ hα
      simp only [e1, e2] at this
      have e : c / (γ * u + δ) ^ 3 * u ^ 1 = ((α * δ - β * γ)⁻¹) ^ 3 *
          (c / (γ * u + δ) ^ 3 * (((α * δ - β * γ) * u) * (α * δ - β * γ) * (α * δ - β * γ))) := by
        linear_combination (-(c / (γ * u + δ) ^ 3 * u ^ 1)) * hD3
      rw [e]; exact hsm (pow_mem hDi 3) this
    · have := prod3_mem W hG hP hδ nβ hδ nβ nγ hα
      simp only [e1, e2] at this
      have e : c / (γ * u + δ) ^ 3 * u ^ 2 = ((α * δ - β * γ)⁻¹) ^ 3 *
          (c / (γ * u + δ) ^ 3 * (((α * δ - β * γ) * u) * ((α * δ - β * γ) * u) * (α * δ - β * γ))) := by
        linear_combination (-(c / (γ * u + δ) ^ 3 * u ^ 2)) * hD3
      rw [e]; exact hsm (pow_mem hDi 3) this
    · have := prod3_mem W hG hP hδ nβ hδ nβ hδ nβ
      simp only [e1] at this
      have e : c / (γ * u + δ) ^ 3 * u ^ 3 = ((α * δ - β * γ)⁻¹) ^ 3 *
          (c / (γ * u + δ) ^ 3 * (((α * δ - β * γ) * u) * ((α * δ - β * γ) * u) * ((α * δ - β * γ) * u))) := by
        linear_combination (-(c / (γ * u + δ) ^ 3 * u ^ 3)) * hD3
      rw [e]; exact hsm (pow_mem hDi 3) this
  set c' := c / (γ * u + δ) ^ 3 with hc'def
  have hc' : c' ≠ 0 := div_ne_zero hc (pow_ne_zero _ hG)
  have hpoly : ∀ q : (↥Qbar)[X], q.natDegree ≤ 3 → c' * aeval u q ∈ W := by
    intro q hq
    rw [cubic_eval hq]
    have e : c' * ((q.coeff 0 : ℂ) + q.coeff 1 * u + q.coeff 2 * u ^ 2 + q.coeff 3 * u ^ 3) =
        (q.coeff 0 : ℂ) * (c' * u ^ 0) + (q.coeff 1 : ℂ) * (c' * u ^ 1) +
          (q.coeff 2 : ℂ) * (c' * u ^ 2) + (q.coeff 3 : ℂ) * (c' * u ^ 3) := by ring
    rw [e]
    exact add_mem (add_mem (add_mem (hsm (q.coeff 0).2 (hcu 0 (by norm_num)))
      (hsm (q.coeff 1).2 (hcu 1 (by norm_num)))) (hsm (q.coeff 2).2 (hcu 2 (by norm_num))))
      (hsm (q.coeff 3).2 (hcu 3 (by norm_num)))
  have hquad : ∀ s : (↥Qbar)[X], s.natDegree ≤ 2 → aeval u s / u ∈ W := by
    intro s hs
    rw [quad_eval hs]
    have e : ((s.coeff 0 : ℂ) + s.coeff 1 * u + s.coeff 2 * u ^ 2) / u =
        (s.coeff 0 : ℂ) * u⁻¹ + (s.coeff 1 : ℂ) * 1 + (s.coeff 2 : ℂ) * u := by
      field_simp
    rw [e]
    exact add_mem (add_mem (hsm (s.coeff 0).2 hui) (hsm (s.coeff 1).2 h1)) (hsm (s.coeff 2).2 hu1)
  -- dimension count: `H ⊓ P' ≠ 0`
  set H := Submodule.span (↥Qbar) (Set.range ![(1 : ℂ), u, u⁻¹]) with hH
  set P' := Submodule.span (↥Qbar) (Set.range (fun j : Fin 4 => c' * u ^ (j : ℕ))) with hP'
  have hHli : LinearIndependent (↥Qbar) ![(1 : ℂ), u, u⁻¹] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Subfield.smul_def, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, smul_eq_mul, Matrix.tail_cons] at hg
    have := cubic_zero hu (g 2) (g 0) (g 1) 0 (by
      have hu' : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
      push_cast
      linear_combination u * hg - (g 2 : ℂ) * hu')
    intro i; fin_cases i
    exacts [this.2.1, this.2.2.1, this.1]
  have hPli : LinearIndependent (↥Qbar) (fun j : Fin 4 => c' * u ^ (j : ℕ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_four, Subfield.smul_def, smul_eq_mul, show ((0 : Fin 4) : ℕ) = 0 from rfl, show ((1 : Fin 4) : ℕ) = 1 from rfl,
      show ((2 : Fin 4) : ℕ) = 2 from rfl, show ((3 : Fin 4) : ℕ) = 3 from rfl] at hg
    have := cubic_zero hu (g 0) (g 1) (g 2) (g 3) (by
      have : c' * ((g 0 : ℂ) + g 1 * u + g 2 * u ^ 2 + g 3 * u ^ 3) = 0 := by
        linear_combination hg
      exact (mul_eq_zero.1 this).resolve_left hc')
    intro i; fin_cases i
    exacts [this.1, this.2.1, this.2.2.1, this.2.2.2]
  have : FiniteDimensional (↥Qbar) H := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have : FiniteDimensional (↥Qbar) P' := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have : FiniteDimensional (↥Qbar) W :=
    FiniteDimensional.span_of_finite _ ((Set.toFinite _).union (Set.finite_range _))
  have hfH : Module.finrank (↥Qbar) H = 3 := by rw [hH, finrank_span_eq_card hHli]; simp
  have hfP : Module.finrank (↥Qbar) P' = 4 := by rw [hP', finrank_span_eq_card hPli]; simp
  have hle : H ⊔ P' ≤ W := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      exacts [h1, hu1, hui]
    · rintro _ ⟨j, rfl⟩
      exact hcu j (by omega)
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq H P'
  have hmono := Submodule.finrank_mono hle
  rw [hdim] at hmono
  have hne : H ⊓ P' ≠ ⊥ := by
    intro e; rw [e, finrank_bot] at hsup; omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (↥Qbar)).1 (Submodule.mem_inf.1 hx).1
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun (↥Qbar)).1 (Submodule.mem_inf.1 hx).2
  simp only [Fin.sum_univ_three, Subfield.smul_def, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, smul_eq_mul, Matrix.tail_cons] at ha
  simp only [Fin.sum_univ_four, Subfield.smul_def, smul_eq_mul, show ((0 : Fin 4) : ℕ) = 0 from rfl, show ((1 : Fin 4) : ℕ) = 1 from rfl,
      show ((2 : Fin 4) : ℕ) = 2 from rfl, show ((3 : Fin 4) : ℕ) = 3 from rfl] at hb
  -- the relation `F p(u) = r(u)` with `F = c' u`
  have hpx : c' * aeval u (C (b 0) + C (b 1) * X + C (b 2) * X ^ 2 + C (b 3) * X ^ 3) = x := by
    simp only [map_add, map_mul, aeval_C, am, map_pow, aeval_X]
    linear_combination hb
  have hrx : aeval u (C (a 2) + C (a 0) * X + C (a 1) * X ^ 2) = u * x := by
    simp only [map_add, map_mul, aeval_C, am, map_pow, aeval_X]
    rw [← ha]; field_simp; ring
  have hp0 : C (b 0) + C (b 1) * X + C (b 2) * X ^ 2 + C (b 3) * X ^ 3 ≠ 0 := by
    intro e; rw [e, map_zero, mul_zero] at hpx; exact hx0 hpx.symm
  have hr0 : C (a 2) + C (a 0) * X + C (a 1) * X ^ 2 ≠ 0 := by
    intro e; rw [e, map_zero] at hrx
    exact hx0 ((mul_eq_zero.1 hrx.symm).resolve_left hu0)
  obtain ⟨q, s, hq, hs, hcase⟩ := key hu (c' * u) 3 _ _ (by compute_degree!) le_rfl hp0 hr0
    (by compute_degree!) (by rw [hrx, ← hpx]; ring)
  have hy : ∀ t : ℂ, t = c' * u * aeval u q + aeval u s → t / u ∈ W := by
    intro t ht
    have e : t / u = c' * aeval u q + aeval u s / u := by rw [ht]; field_simp
    rw [e]; exact add_mem (hpoly q hq) (hquad s hs)
  rcases hcase with h3 | ⟨b, hb⟩
  · left
    have := hy _ h3
    rwa [show u ^ 3 / u = u ^ 2 by field_simp] at this
  · by_cases hb0 : (b : ℂ) = 0
    · right; left
      have := hy _ hb
      rwa [hb0, sub_zero, show u⁻¹ / u = (u ^ 2)⁻¹ by field_simp] at this
    · right; right
      refine ⟨b, b.2, hb0, ?_⟩
      have hub : u - (b : ℂ) ≠ 0 := sub_ne_zero.2 (fun e => hu (e ▸ b.2))
      have := hsm b.2 (hy _ hb)
      have e : (u - b)⁻¹ = (b : ℂ) * ((u - b)⁻¹ / u) + u⁻¹ := by field_simp; ring
      rw [e]; exact add_mem this hui
