-- Prove2me | solution 1 for DiazModulus.exists_chain_prime
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:00:49.117818+00:00
-- url     : https://prove2.me/submissions/00b31ce8-f153-44a7-9d71-942191c42949

import Mathlib
import Definitions.Def_DiazMultiplicity
import Theorems.Thm_DiazModulus_torusTransl_algEquiv
import Theorems.Thm_DiazModulus_torusVanishing_univ

open Complex ComplexConjugate

/-! # The descent: a prime of the chain `I_0 ≤ I_1 ≤ ⋯ ≤ I_d` at which the height stops growing

Let `I_k = J₀ + (σ_{g_s} D_l P : |s_j| ≤ k M₁, l a W-list, |l| ≤ k M₀)` (`obstructionSpan … {1}`), an
increasing chain, and `h_k = ht I_k`. Since `g_0 = 1`, `σ_1 = id` (V2) and `D_[] = id`, `P ∈ I_0`; as `P ∉ J₀` and
`J₀` is prime with `ht J₀ ≥ d₁` (V3), every minimal prime `Q` of `I_0` satisfies `J₀ < Q`, so
`h_0 ≥ d₁ + 1` (`Ideal.height_add_one_le_of_lt_of_isPrime`, `Ideal.height_eq_inf_minimalPrimes`). At the point
`1`, `J₀ = I(G)` (V3) vanishes and every generator `σ_{g_s} D_l P` of `I_d` takes the value `(D_l P)(g_s) = 0`
(`hvan`), so `I_d ≠ ⊤` and `h_d ≤ dim R = d₀ + 2 d₁` (`Ideal.height_le_ringKrullDim_of_ne_top`,
`MvPolynomial.ringKrullDim_of_isNoetherianRing`). If `h_k < h_{k+1}` for all `k < d`, then `h_0 + d ≤ h_d`,
i.e. `d₁ + 1 + d ≤ d₀ + 2 d₁`, absurd: so some `r < d` has `h_{r+1} ≤ h_r`. Pick a prime `𝔭 ⊇ I_{r+1}` of height
`h_{r+1} = n < ∞` (`Ideal.exists_isPrime_height_eq`); it contains `J₀`, `P` and every `σ_{g_s} D_l P` of
`I_{r+1}` (clause (b)). For (c): if `I_r ≤ Q := 𝔭.comap σ_z`, then `ht Q = ht 𝔭 = n` (`σ_z` is a ring
automorphism, V2, `RingEquiv.height_comap`); a minimal prime `Q' ≤ Q` of `I_r` has `ht Q' ≥ h_r ≥ h_{r+1} = ht Q`,
so `Q' = Q` (`Ideal.eq_of_le_of_height_le`) and `Q` is minimal over `I_r`. -/

namespace C13_Z1
open DiazModulus MvPolynomial

/-- The descent ideal `I_k` (0-based). -/
noncomputable def descI {A₀ A₁ B₁ : Type*} [Fintype B₁] (P : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)
    (W : Submodule ℂ ((A₀ → ℂ) × (A₁ → ℂ))) (u : B₁ → A₀ → ℂ) (a : B₁ → A₁ → ℂˣ) (M₀ M₁ k : ℕ) :
    Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) :=
  torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (k * M₁) (k * M₀) {1} :
    Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ))

variable {A₀ A₁ B₁ : Type*} [Fintype B₁] (P : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)
    (W : Submodule ℂ ((A₀ → ℂ) × (A₁ → ℂ))) (u : B₁ → A₀ → ℂ) (a : B₁ → A₁ → ℂˣ) (M₀ M₁ : ℕ)

theorem descI_mono {k k' : ℕ} (h : k ≤ k') : descI P W u a M₀ M₁ k ≤ descI P W u a M₀ M₁ k' := by
  refine sup_le_sup_left (Ideal.span_mono (SetLike.coe_subset_coe.mpr (Submodule.span_mono ?_))) _
  rintro _ ⟨s, hs, v, hv, l, hl, hW, rfl⟩
  exact ⟨s, fun j => (hs j).trans (by exact_mod_cast Nat.mul_le_mul_right _ h), v, hv, l,
    hl.trans (Nat.mul_le_mul_right _ h), hW, rfl⟩

theorem gen_mem (k : ℕ) (s : B₁ → ℤ) (hs : ∀ b, |s b| ≤ ((k * M₁ : ℕ) : ℤ))
    (l : List ((A₀ → ℂ) × (A₁ → ℂ))) (hl : l.length ≤ k * M₀) (hW : ∀ w ∈ l, w ∈ W) :
    torusTransl (hmePoint u a s) (torusDerivList l P) ∈ descI P W u a M₀ M₁ k :=
  Ideal.mem_sup_right (Ideal.subset_span (Submodule.subset_span
    ⟨s, hs, 1, rfl, l, hl, hW, by rw [mul_one]⟩))

theorem hmePoint_zero : hmePoint u a (0 : B₁ → ℤ) = 1 := by
  refine Prod.ext ?_ ?_
  · simp [hmePoint]
  · funext i
    simp [hmePoint]

end C13_Z1

open DiazModulus C13_Z1 in
theorem solution {A₀ A₁ B₁ : Type*} [Fintype A₀] [Fintype A₁] [Fintype B₁] (P : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) (hP0 : P ∉ torusIdeal ℂ A₀ A₁)
    (W : Submodule ℂ ((A₀ → ℂ) × (A₁ → ℂ))) (u : B₁ → A₀ → ℂ) (a : B₁ → A₁ → ℂˣ) (M₀ M₁ : ℕ)
    (hvan : ∀ l : List ((A₀ → ℂ) × (A₁ → ℂ)), l.length ≤ (Fintype.card A₀ + Fintype.card A₁) * M₀ → (∀ w ∈ l, w ∈ W) →
      ∀ s : B₁ → ℤ, (∀ b, |s b| ≤ (((Fintype.card A₀ + Fintype.card A₁) * M₁ : ℕ) : ℤ)) →
        MvPolynomial.eval (torusPt (hmePoint u a s)) (torusDerivList l P) = 0) :
    ∃ r < (Fintype.card A₀ + Fintype.card A₁), ∃ 𝔭 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ), 𝔭.IsPrime ∧ torusIdeal ℂ A₀ A₁ ≤ 𝔭 ∧ P ∈ 𝔭 ∧
      (∀ s : B₁ → ℤ, (∀ b, |s b| ≤ (((r + 1) * M₁ : ℕ) : ℤ)) → ∀ l : List ((A₀ → ℂ) × (A₁ → ℂ)), l.length ≤ (r + 1) * M₀ →
        (∀ w ∈ l, w ∈ W) → torusTransl (hmePoint u a s) (torusDerivList l P) ∈ 𝔭) ∧
      ∀ z : TorusGroup ℂ A₀ A₁, torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) {1} : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) ≤ 𝔭.comap (torusTransl z) →
        𝔭.comap (torusTransl z) ∈ (torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) {1} : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ))).minimalPrimes := by
  obtain ⟨hJeq, hJprime, hJht⟩ := DiazModulus.torusVanishing_univ (A₀ := A₀) (A₁ := A₁)
  have hP0mem : P ∈ descI P W u a M₀ M₁ 0 := by
    have := gen_mem P W u a M₀ M₁ 0 0 (by simp) [] (by simp) (by simp)
    rwa [hmePoint_zero, torusDerivList_nil, Module.End.one_apply,
      (DiazModulus.torusTransl_algEquiv (1 : TorusGroup ℂ A₀ A₁)).2.2] at this
  -- lower bound at `k = 0`
  have h0 : (Fintype.card A₁ : ℕ∞) + 1 ≤ (descI P W u a M₀ M₁ 0).height := by
    rw [Ideal.height_eq_inf_minimalPrimes]
    refine le_iInf₂ fun Q hQ => ?_
    have := hQ.isPrime
    have hlt : torusIdeal ℂ A₀ A₁ < Q := lt_of_le_of_ne (le_sup_left.trans hQ.1.2)
      (fun h => hP0 (by rw [h]; exact hQ.1.2 hP0mem))
    exact (add_le_add hJht le_rfl).trans (Ideal.height_add_one_le_of_lt_of_isPrime hlt)
  -- upper bound at `k = d`
  have htop : descI P W u a M₀ M₁ (Fintype.card A₀ + Fintype.card A₁) ≠ ⊤ := by
    intro h
    have hle : descI P W u a M₀ M₁ (Fintype.card A₀ + Fintype.card A₁) ≤
        RingHom.ker (MvPolynomial.eval (torusPt (1 : TorusGroup ℂ A₀ A₁))) := by
      refine sup_le ?_ ?_
      · rw [← hJeq]
        intro f hf
        simp only [torusVanishing, Submodule.mem_iInf] at hf
        exact hf 1 (Set.mem_univ _)
      · have hsp : obstructionSpan P W u a ((Fintype.card A₀ + Fintype.card A₁) * M₁)
            ((Fintype.card A₀ + Fintype.card A₁) * M₀) {1} ≤
            (RingHom.ker (MvPolynomial.eval (torusPt (1 : TorusGroup ℂ A₀ A₁)))).restrictScalars ℂ := by
          refine Submodule.span_le.mpr ?_
          rintro _ ⟨s, hs, v, hv, l, hl, hW, rfl⟩
          rw [Set.mem_singleton_iff] at hv
          subst hv
          simp only [SetLike.mem_coe, Submodule.restrictScalars_mem, RingHom.mem_ker, eval_torusTransl,
            one_mul, mul_one]
          exact hvan l hl hW s hs
        rw [Ideal.span_le]
        exact fun x hx => hsp hx
    have h1 : (1 : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) ∈
        RingHom.ker (MvPolynomial.eval (torusPt (1 : TorusGroup ℂ A₀ A₁))) := hle (h ▸ Submodule.mem_top)
    simp at h1
  have hcard : Nat.card (A₀ ⊕ (A₁ × Bool)) = Fintype.card A₀ + Fintype.card A₁ * 2 := by
    simp [Nat.card_eq_fintype_card]
  have hd : (descI P W u a M₀ M₁ (Fintype.card A₀ + Fintype.card A₁)).height ≤
      ((Fintype.card A₀ + Fintype.card A₁ * 2 : ℕ) : ℕ∞) := by
    have h1 := Ideal.height_le_ringKrullDim_of_ne_top htop
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      hcard] at h1
    have h2 : (((descI P W u a M₀ M₁ (Fintype.card A₀ + Fintype.card A₁)).height : ℕ∞) : WithBot ℕ∞) ≤
        (((Fintype.card A₀ + Fintype.card A₁ * 2 : ℕ) : ℕ∞) : WithBot ℕ∞) := h1
    exact WithBot.coe_le_coe.mp h2
  -- pigeonhole
  have hex : ∃ r < Fintype.card A₀ + Fintype.card A₁,
      (descI P W u a M₀ M₁ (r + 1)).height ≤ (descI P W u a M₀ M₁ r).height := by
    by_contra hne
    simp only [not_exists, not_and, not_le] at hne
    have key : ∀ k ≤ Fintype.card A₀ + Fintype.card A₁,
        (descI P W u a M₀ M₁ 0).height + k ≤ (descI P W u a M₀ M₁ k).height := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have hlt := hne k (by omega)
        calc (descI P W u a M₀ M₁ 0).height + ((k + 1 : ℕ) : ℕ∞)
            = ((descI P W u a M₀ M₁ 0).height + k) + 1 := by push_cast; ring
          _ ≤ (descI P W u a M₀ M₁ k).height + 1 := by gcongr; exact ih (by omega)
          _ ≤ _ := (ENat.add_one_le_iff (ne_top_of_lt hlt)).mpr hlt
    have h2 := (add_le_add h0 (le_refl ((Fintype.card A₀ + Fintype.card A₁ : ℕ) : ℕ∞))).trans ((key _ le_rfl).trans hd)
    have h3 : Fintype.card A₁ + 1 + (Fintype.card A₀ + Fintype.card A₁) ≤
        Fintype.card A₀ + Fintype.card A₁ * 2 := by exact_mod_cast h2
    omega
  obtain ⟨r, hr, hrle⟩ := hex
  have hfin : (descI P W u a M₀ M₁ (r + 1)).height ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _)
      ((Ideal.height_mono (descI_mono P W u a M₀ M₁ (by omega))).trans hd)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  obtain ⟨𝔭, h𝔭, hI𝔭, h𝔭ht⟩ := Ideal.exists_isPrime_height_eq hn.symm
  refine ⟨r, hr, 𝔭, h𝔭, le_sup_left.trans hI𝔭,
    hI𝔭 (descI_mono P W u a M₀ M₁ (Nat.zero_le _) hP0mem),
    fun s hs l hl hW => hI𝔭 (gen_mem P W u a M₀ M₁ (r + 1) s hs l hl hW), fun z hz => ?_⟩
  obtain ⟨⟨e, he, -⟩, -⟩ := DiazModulus.torusTransl_algEquiv z
  have hqe : 𝔭.comap (torusTransl z) = 𝔭.comap e.toRingEquiv := by
    ext f
    simp [Ideal.mem_comap, he]
  have hQht : (𝔭.comap (torusTransl z)).height = n := by
    rw [hqe, RingEquiv.height_comap e.toRingEquiv 𝔭, h𝔭ht]
  have : (𝔭.comap (torusTransl z)).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨Q', hQ', hQ'Q⟩ := Ideal.exists_minimalPrimes_le hz
  have := hQ'.isPrime
  have hQ'ht : (𝔭.comap (torusTransl z)).height ≤ Q'.height := by
    rw [hQht, hn]
    exact hrle.trans (Ideal.height_mono hQ'.1.2)
  have : Q'.FiniteHeight := Ideal.finiteHeight_iff_lt.mpr
    (Or.inr ((Ideal.height_mono hQ'Q).trans_lt (by rw [hQht]; exact ENat.natCast_lt_top n)))
  rw [← Ideal.eq_of_le_of_height_le Q' hQ'Q hQ'ht]
  exact hQ'
