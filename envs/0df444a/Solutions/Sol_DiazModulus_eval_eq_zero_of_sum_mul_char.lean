-- Prove2me | solution 1 for DiazModulus.eval_eq_zero_of_sum_mul_char
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:06:20.170883+00:00
-- url     : https://prove2.me/submissions/ec6ee579-27f1-496c-9aeb-ac5b2938d58e

import Mathlib

open Complex ComplexConjugate

/-! # Generalised Dedekind lemma, through finite differences

Say `u : Γ → ℂ` has difference degree `≤ N` (`PD N`) when every `(N+1)`-fold difference `Δ_{h₀} ⋯ Δ_{h_N} u` vanishes,
`Δ_h u = u(· h) − u`. Polynomials along an additive homomorphism `ρ` have finite difference degree (multiplying by
an additive coordinate raises it by one), while a nonzero multiple of a nontrivial character has none
(`Δ_h(aψ) = (ψ(h) − 1)aψ`). The lemma is proved by induction on the finset of characters and, inside, on the
degree of the first coefficient `u_{c₀}`: the translated relation `Σ_c [χ_c(h) u_c(g h) − χ_{c₀}(h) u_c(g)] χ_c(g) = 0`
has lower degree in `c₀`, so its coefficients vanish; for `c ≠ c₀` this says `u_c = u_c(1) · χ_{c₀}/χ_c`, a multiple
of a nontrivial character of finite degree, hence `0`; then `u_{c₀} = 0` from the original relation. -/

namespace C13_G1
variable {Γ : Type*} [CommGroup Γ]

/-- Functions of difference degree `≤ N` on `Γ`: `Δ_h u = u(· h) − u` lowers the degree. -/
def PD : ℕ → Set (Γ → ℂ)
  | 0 => {u | ∀ g h, u (g * h) = u g}
  | N + 1 => {u | ∀ h, (fun g => u (g * h) - u g) ∈ PD N}

theorem PD_add : ∀ (N : ℕ) {u v : Γ → ℂ}, u ∈ PD N → v ∈ PD N → (u + v) ∈ PD N
  | 0, u, v, hu, hv => fun g h => by simp [hu g h, hv g h]
  | N + 1, u, v, hu, hv => fun h => by
    have := PD_add N (hu h) (hv h)
    convert this using 1
    funext g; simp; ring

theorem PD_smul : ∀ (N : ℕ) (a : ℂ) {u : Γ → ℂ}, u ∈ PD N → (fun g => a * u g) ∈ PD N
  | 0, a, u, hu => fun g h => by simp [hu g h]
  | N + 1, a, u, hu => fun h => by
    have := PD_smul N a (hu h)
    convert this using 1
    funext g; ring

theorem PD_zero_mem : ∀ (N : ℕ), (0 : Γ → ℂ) ∈ PD N
  | 0 => fun g h => rfl
  | N + 1 => fun h => by convert PD_zero_mem N using 1; funext g; simp

theorem PD_transl : ∀ (N : ℕ) (h' : Γ) {u : Γ → ℂ}, u ∈ PD N → (fun g => u (g * h')) ∈ PD N
  | 0, h', u, hu => fun g h => by
    have := hu (g * h') h
    rwa [mul_right_comm] at this
  | N + 1, h', u, hu => fun h => by
    have := PD_transl N h' (hu h)
    convert this using 1
    funext g; simp only [mul_right_comm]

theorem PD_succ_of_mem : ∀ (N : ℕ) {u : Γ → ℂ}, u ∈ PD N → u ∈ PD (N + 1)
  | 0, u, hu => fun h => by
    have : (fun g => u (g * h) - u g) = 0 := by funext g; simp [hu g h]
    rw [this]; exact PD_zero_mem 0
  | N + 1, u, hu => fun h => PD_succ_of_mem N (hu h)

theorem PD_mono {N M : ℕ} (hNM : N ≤ M) {u : Γ → ℂ} (hu : u ∈ PD N) : u ∈ PD M := by
  induction hNM with
  | refl => exact hu
  | step _ ih => exact PD_succ_of_mem _ ih

theorem PD_const (a : ℂ) (N : ℕ) : (fun _ : Γ => a) ∈ PD N :=
  PD_mono (Nat.zero_le N) (fun _ _ => rfl)

/-- Multiplying by an additive coordinate `w` raises the difference degree by one. -/
theorem PD_mul_add_hom (w : Γ → ℂ) (hw : ∀ g h, w (g * h) = w g + w h) :
    ∀ (N : ℕ) {u : Γ → ℂ}, u ∈ PD N → (fun g => u g * w g) ∈ PD (N + 1)
  | 0, u, hu => fun h => by
    have : (fun g => u (g * h) * w (g * h) - u g * w g) = fun _ => u 1 * w h := by
      funext g
      have h1 := hu g h
      have h2 := hu 1 g
      simp only [one_mul] at h2
      rw [h1, hw, ← h2]; ring
    rw [this]; exact PD_const _ 0
  | N + 1, u, hu => fun h => by
    have e : (fun g => u (g * h) * w (g * h) - u g * w g) =
        (fun g => (u (g * h) - u g) * w g) + (fun g => w h * (u (g * h) - u g))
          + (fun g => w h * u g) := by
      funext g; simp only [Pi.add_apply, hw]; ring
    rw [e]
    exact PD_add _ (PD_add _ (PD_mul_add_hom w hw N (hu h))
      (PD_succ_of_mem _ (PD_smul _ _ (hu h)))) (PD_smul _ _ hu)

/-- A nonzero multiple of a nontrivial character has no finite difference degree. -/
theorem PD_char (ψ : Γ →* ℂˣ) : ∀ (N : ℕ) (a : ℂ), (fun g => a * (ψ g : ℂ)) ∈ PD N →
    a = 0 ∨ ψ = 1
  | 0, a, ha => by
    by_cases h0 : a = 0
    · exact Or.inl h0
    · right; ext h
      have := ha 1 h
      simp only [one_mul, map_one, Units.val_one, mul_one] at this
      have h' : a * ((ψ h : ℂ) - 1) = 0 := by rw [mul_sub, this]; ring
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' h0
      · simpa [sub_eq_zero] using h''
  | N + 1, a, ha => by
    by_cases h1 : ψ = 1
    · exact Or.inr h1
    · left
      obtain ⟨h, hh⟩ : ∃ h, ψ h ≠ 1 := by
        by_contra hc; push Not at hc; exact h1 (MonoidHom.ext hc)
      have key := ha h
      have e : (fun g => a * (ψ (g * h) : ℂ) - a * (ψ g : ℂ)) =
          fun g => (a * ((ψ h : ℂ) - 1)) * (ψ g : ℂ) := by
        funext g; simp only [map_mul, Units.val_mul]; ring
      rw [e] at key
      rcases PD_char ψ N _ key with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · exact h3
        · exact absurd (by simpa [sub_eq_zero, Units.val_eq_one] using h3) hh
      · exact absurd h2 h1

/-- GDed on functions. -/
theorem eq_zero_of_sum_mul_char_PD {ι : Type*} [DecidableEq ι] (χ : ι → Γ →* ℂˣ)
    (hχ : Function.Injective χ) (s : Finset ι) :
    ∀ (N : ℕ) (u : ι → Γ → ℂ), (∀ c ∈ s, u c ∈ PD N) →
      (∀ g, ∑ c ∈ s, u c g * (χ c g : ℂ) = 0) → ∀ c ∈ s, u c = 0 := by
  induction s using Finset.induction_on with
  | empty => intro _ _ _ _ c hc; simp at hc
  | @insert c₀ s' hc₀ ih =>
    intro N u hu hrel
    -- inner induction on the degree of `u c₀`
    suffices H : ∀ M (u : ι → Γ → ℂ), (∀ c ∈ s', u c ∈ PD N) → u c₀ ∈ PD M →
        (∀ g, ∑ c ∈ insert c₀ s', u c g * (χ c g : ℂ) = 0) → ∀ c ∈ insert c₀ s', u c = 0 by
      exact H (max N 0) u (fun c hc => hu c (Finset.mem_insert_of_mem hc))
        (PD_mono (le_max_left _ _) (hu c₀ (Finset.mem_insert_self _ _))) hrel
    have hs' : ∀ c ∈ s', c ≠ c₀ := fun c hc h => hc₀ (h ▸ hc)
    -- the step shared by both cases: the translated relations force `u c = 0` off `c₀`
    have key : ∀ u : ι → Γ → ℂ, (∀ c ∈ s', u c ∈ PD N) →
        (∀ g, ∑ c ∈ insert c₀ s', u c g * (χ c g : ℂ) = 0) →
        (∀ h, ∀ c ∈ s', ∀ g, (χ c h : ℂ) * u c (g * h) = (χ c₀ h : ℂ) * u c g) →
        ∀ c ∈ insert c₀ s', u c = 0 := by
      intro u hu hrel hG
      have hoff : ∀ c ∈ s', u c = 0 := by
        intro c hc
        let ψ : Γ →* ℂˣ := χ c₀ * (χ c)⁻¹
        have hform : u c = fun g => u c 1 * (ψ g : ℂ) := by
          funext g
          have := hG g c hc 1
          simp only [one_mul] at this
          have hu0 : (χ c g : ℂ) ≠ 0 := (χ c g).ne_zero
          simp only [ψ, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
          rw [Units.val_inv_eq_inv_val, ← mul_assoc, eq_mul_inv_iff_mul_eq₀ hu0]
          linear_combination this
        rcases PD_char ψ N (u c 1) (hform ▸ hu c hc) with h0 | h1
        · rw [hform, h0]; funext g; simp
        · exfalso
          have : χ c₀ = χ c := mul_inv_eq_one.mp h1
          exact hs' c hc (hχ this).symm
      have hc₀z : u c₀ = 0 := by
        funext g
        have := hrel g
        rw [Finset.sum_insert hc₀, Finset.sum_eq_zero (fun c hc => by simp [hoff c hc])] at this
        simpa [(χ c₀ g).ne_zero] using this
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hc₀z
      · exact hoff c hc
    -- the translated family
    have hGrel : ∀ (u : ι → Γ → ℂ), (∀ g, ∑ c ∈ insert c₀ s', u c g * (χ c g : ℂ) = 0) →
        ∀ h g, ∑ c ∈ insert c₀ s',
          ((χ c h : ℂ) * u c (g * h) - (χ c₀ h : ℂ) * u c g) * (χ c g : ℂ) = 0 := by
      intro u hrel h g
      simp_rw [sub_mul, Finset.sum_sub_distrib]
      have e1 : ∑ c ∈ insert c₀ s', (χ c h : ℂ) * u c (g * h) * (χ c g : ℂ)
          = ∑ c ∈ insert c₀ s', u c (g * h) * (χ c (g * h) : ℂ) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [map_mul, Units.val_mul]; ring
      have e2 : ∑ c ∈ insert c₀ s', (χ c₀ h : ℂ) * u c g * (χ c g : ℂ)
          = (χ c₀ h : ℂ) * ∑ c ∈ insert c₀ s', u c g * (χ c g : ℂ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c _ => ?_; ring
      rw [e1, e2, hrel (g * h), hrel g]; ring
    have hGPD : ∀ (u : ι → Γ → ℂ), (∀ c ∈ s', u c ∈ PD N) → ∀ h, ∀ c ∈ s',
        (fun g => (χ c h : ℂ) * u c (g * h) - (χ c₀ h : ℂ) * u c g) ∈ PD N := by
      intro u hu h c hc
      have := PD_add N (PD_smul N (χ c h : ℂ) (PD_transl N h (hu c hc)))
        (PD_smul N (-(χ c₀ h : ℂ)) (hu c hc))
      convert this using 1; funext g; simp; ring
    intro M
    induction M with
    | zero =>
      intro u hu hu0 hrel
      refine key u hu hrel fun h c hc g => ?_
      -- `u c₀` is constant, so the translated `c₀`-term vanishes
      have hG := ih N (fun c g => (χ c h : ℂ) * u c (g * h) - (χ c₀ h : ℂ) * u c g)
        (hGPD u hu h) (fun g => by
          have := hGrel u hrel h g
          rw [Finset.sum_insert hc₀] at this
          have h0 : (χ c₀ h : ℂ) * u c₀ (g * h) - (χ c₀ h : ℂ) * u c₀ g = 0 := by
            rw [hu0 g h]; ring
          rw [h0, zero_mul, zero_add] at this
          exact this) c hc
      have := congrFun hG g
      simp only [Pi.zero_apply, sub_eq_zero] at this
      exact this
    | succ M ihM =>
      intro u hu hu0 hrel
      refine key u hu hrel fun h c hc g => ?_
      have hG := ihM (fun c g => (χ c h : ℂ) * u c (g * h) - (χ c₀ h : ℂ) * u c g)
        (hGPD u hu h) (by
          have := PD_smul M (χ c₀ h : ℂ) (hu0 h)
          convert this using 1; funext g; ring)
        (hGrel u hrel h) c (Finset.mem_insert_of_mem hc)
      have := congrFun hG g
      simp only [Pi.zero_apply, sub_eq_zero] at this
      exact this

/-- The bridge: a polynomial along an additive homomorphism has a finite difference degree. -/
theorem PD_eval_poly {A₀ : Type*} (ρ : Γ →* Multiplicative (A₀ → ℂ)) (F : MvPolynomial A₀ ℂ) :
    ∃ N, (fun g => MvPolynomial.eval (Multiplicative.toAdd (ρ g)) F) ∈ PD N := by
  induction F using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simpa using PD_const (Γ := Γ) a 0⟩
  | add p q hp hq =>
    obtain ⟨N, hN⟩ := hp; obtain ⟨M, hM⟩ := hq
    refine ⟨max N M, ?_⟩
    have := PD_add _ (PD_mono (le_max_left N M) hN) (PD_mono (le_max_right N M) hM)
    convert this using 1; funext g; simp [map_add]
  | mul_X p i hp =>
    obtain ⟨N, hN⟩ := hp
    refine ⟨N + 1, ?_⟩
    have := PD_mul_add_hom (fun g => Multiplicative.toAdd (ρ g) i)
      (fun g h => by simp [toAdd_mul]) N hN
    simpa using this
end C13_G1

open C13_G1 in
theorem solution {Γ A₀ ι : Type*} [CommGroup Γ] [Fintype ι]
    (ρ : Γ →* Multiplicative (A₀ → ℂ)) (χ : ι → Γ →* ℂˣ) (hχ : Function.Injective χ)
    (F : ι → MvPolynomial A₀ ℂ)
    (h : ∀ g, ∑ c, MvPolynomial.eval (Multiplicative.toAdd (ρ g)) (F c) * (χ c g : ℂ) = 0) :
    ∀ c g, MvPolynomial.eval (Multiplicative.toAdd (ρ g)) (F c) = 0 := by
  classical
  choose N hN using fun c => PD_eval_poly ρ (F c)
  let M := Finset.univ.sup N
  have := eq_zero_of_sum_mul_char_PD χ hχ Finset.univ M
    (fun c g => MvPolynomial.eval (Multiplicative.toAdd (ρ g)) (F c))
    (fun c _ => PD_mono (Finset.le_sup (Finset.mem_univ c)) (hN c)) h
  intro c g
  exact congrFun (this c (Finset.mem_univ c)) g
