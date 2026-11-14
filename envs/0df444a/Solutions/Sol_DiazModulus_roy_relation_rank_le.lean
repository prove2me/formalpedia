-- Prove2me | solution 1 for DiazModulus.roy_relation_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-13T10:03:35.774205+00:00
-- url     : https://prove2.me/submissions/cd9edf65-f8e5-40c9-8853-35c8ef745682

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The relation rank is at most `m · dim_Q̄ (span z ⊓ (T + 2πi·Q̄^d))`
Write `Υ(u, v)_i = u_i + Σ_k ω_k v_{(k,i)}`, `V₀ = span_ℂ(V' ∩ Q̄^d)`, `T = Υ(V₀ × L₁)` and
`Λ(c) = Σ_p c_p ω_{p.1} z_{p.2}` for `c ∈ ℚ^{m×ℓ}`. For a relation `s`, put `ζ = Σ_j s_j η_j`, so
`Λ(s) = Υ(ζ)`. The exponential condition reads `exp(Σ_i φ_{ki} ζ.2_i) = 1`, i.e.
`Σ_i φ_{ki} ζ.2_i = 2πi e_k` with `e_k ∈ ℤ`; applying a ℚ-linear projection `π : ℂ → ℚ` with
`π(1) = 1` to `ζ.2/2πi` gives `r ∈ ℚ^{md}` with `Σ_i φ_{ki} r_i = e_k`, so `ζ.2 − 2πi r ∈ L₁`.
Also `ζ.1 ∈ V'` is algebraic, hence in `V₀`. So `Λ(s) = Υ(ζ.1, ζ.2 − 2πi r) + 2πi Υ(0, r)` lies in
`F = span z ⊓ span(T + 2πi Q̄^d)`, and by linearity `Λ` maps the ℚ-span `G` of the relations into
`F`. In the basis `z`, the coordinates of `Λ(c)` are `Σ_b c_{(b,j)} ω_b`. These `ℓ` coordinate
functionals separate the points of `F`, so some `f ≤ dim F` of them, at columns `a_1..a_f`, already
do. Then `c ↦ (c_{(b, a_t)})` is injective on `G`: if it kills `c`, then `Λ(c) = 0`, so every
coordinate `Σ_b c_{(b,j)} ω_b` vanishes and `c = 0` as `ω` is ℚ-free. Hence `ρ ≤ m·f`. -/

namespace RC1_RRL
open DiazModulus

noncomputable def Ups (d m : ℕ) (ω : Fin m → ℂ) :
    ((Fin d → ℂ) × (Fin m × Fin d → ℂ)) →ₗ[ℂ] (Fin d → ℂ) :=
  LinearMap.pi fun i : Fin d =>
    (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)
    + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
        LinearMap.snd ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)

theorem Ups_apply {d m : ℕ} (ω : Fin m → ℂ) (v : (Fin d → ℂ) × (Fin m × Fin d → ℂ)) (i : Fin d) :
    Ups d m ω v i = v.1 i + ∑ k, ω k * v.2 (k, i) := by
  simp [Ups, LinearMap.sum_apply]

theorem prod_exp {N ι : Type*} [Fintype N] [Fintype ι] (a : N → ι → ℂ) (s : N → ℤ) (φ : ι → ℤ) :
    ∏ i, (∏ j, Complex.exp (a j i) ^ s j) ^ φ i
      = Complex.exp (∑ i, (φ i : ℂ) * ∑ j, (s j : ℂ) * a j i) := by
  simp only [← Complex.exp_int_mul, ← Complex.exp_sum]

/-- A ℚ-linear projection `ℂ → ℚ` fixing `ℚ`. -/
theorem exists_ratProj : ∃ π : ℂ →ₗ[ℚ] ℚ, ∀ q : ℚ, π (q : ℂ) = q := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ ℂ)
    (LinearMap.ker_eq_bot.mpr (algebraMap ℚ ℂ).injective)
  exact ⟨g, fun q => by simpa using LinearMap.congr_fun hg q⟩

/-- If `Φ(y) ∈ 2πiℤ^q` for an integer matrix `Φ`, then `y ∈ ker Φ + 2πi ℚ^ι`. -/
theorem rat_lift {ι : Type} [Fintype ι] {q : ℕ} (φ : Fin q → ι → ℤ) (y : ι → ℂ)
    (hy : ∀ k, ∃ e : ℤ, ∑ i, (φ k i : ℂ) * y i = e * (2 * Real.pi * I)) :
    ∃ r : ι → ℚ, ∀ k, ∑ i, (φ k i : ℂ) * (y i - 2 * Real.pi * I * r i) = 0 := by
  obtain ⟨π, hπ⟩ := exists_ratProj
  choose e he using hy
  have h2 : (2 * (Real.pi : ℂ) * I) ≠ 0 := two_pi_I_ne_zero
  refine ⟨fun i => π (y i / (2 * Real.pi * I)), fun k => ?_⟩
  have hc : ∑ i, (φ k i : ℂ) * (y i / (2 * Real.pi * I)) = ((e k : ℚ) : ℂ) := by
    simp only [← mul_div_assoc, ← Finset.sum_div, he k]
    push_cast; field_simp
  have hsum : ∑ i, (φ k i : ℚ) * π (y i / (2 * Real.pi * I)) = e k := by
    have := congrArg π hc
    rw [hπ, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (φ k i : ℂ) * (y i / (2 * Real.pi * I)) = ((φ k i : ℚ)) • (y i / (2 * Real.pi * I)) by
      rw [Rat.smul_def]; push_cast; rfl, map_smul, smul_eq_mul]
  have hcast := congrArg (fun x : ℚ => (x : ℂ)) hsum
  push_cast at hcast
  calc ∑ i, (φ k i : ℂ) * (y i - 2 * Real.pi * I * (π (y i / (2 * Real.pi * I)) : ℂ))
      = ∑ i, (φ k i : ℂ) * y i
          - 2 * Real.pi * I * ∑ i, (φ k i : ℂ) * (π (y i / (2 * Real.pi * I)) : ℂ) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [hcast, he k]; ring

/-- Functionals separating points: at most `finrank` of them already separate points. -/
theorem exists_sep {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Finite ι] (ρ : ι → Module.Dual K V) (hsep : ∀ v, (∀ j, ρ j v = 0) → v = 0) :
    ∃ (κ : Type) (_ : Fintype κ) (a : κ → ι), Fintype.card κ ≤ Module.finrank K V ∧
      ∀ v, (∀ t, ρ (a t) v = 0) → v = 0 := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K ρ
  have : Finite κ := Finite.of_injective a ha
  let _ : Fintype κ := Fintype.ofFinite κ
  refine ⟨κ, inferInstance, a, ?_, ?_⟩
  · calc Fintype.card κ ≤ Module.finrank K (Module.Dual K V) := hli.fintype_card_le_finrank
      _ = Module.finrank K V := Subspace.dual_finrank_eq
  · intro v hv
    apply hsep
    intro j
    have hle : Submodule.span K (Set.range (ρ ∘ a)) ≤ LinearMap.ker (Module.Dual.eval K V v) := by
      rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      simp [hv t]
    have hj : ρ j ∈ Submodule.span K (Set.range (ρ ∘ a)) :=
      hspan ▸ Submodule.subset_span ⟨j, rfl⟩
    simpa using hle hj

theorem span_le_Qbar {m : ℕ} (ω : Fin m → ℂ) (hωalg : ∀ a, ω a ∈ Qbar) :
    ∀ x ∈ Submodule.span ℚ (Set.range ω), x ∈ Qbar := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hωalg a
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => rw [Rat.smul_def]; exact mul_mem (SubfieldClass.ratCast_mem _ _) hx

variable {d m ℓ : ℕ}

/-- `Λ(c) = Σ_p c_p ω_{p.1} z_{p.2}`. -/
noncomputable def Lam (ω : Fin m → ℂ) (z : Fin ℓ → Fin d → ℂ) :
    (Fin m × Fin ℓ → ℚ) →ₗ[ℚ] (Fin d → ℂ) :=
  Fintype.linearCombination ℚ (fun p : Fin m × Fin ℓ => ω p.1 • z p.2)

/-- The `j`-th coordinate of `Λ(c)` in the basis `z`. -/
noncomputable def bq (ω : Fin m → ℂ) (hωalg : ∀ a, ω a ∈ Qbar) (c : Fin m × Fin ℓ → ℚ)
    (j : Fin ℓ) : ↥Qbar :=
  ⟨∑ b, (c (b, j) : ℂ) * ω b, sum_mem fun b _ => mul_mem (SubfieldClass.ratCast_mem _ _) (hωalg b)⟩

theorem Lam_eq (ω : Fin m → ℂ) (hωalg : ∀ a, ω a ∈ Qbar) (z : Fin ℓ → Fin d → ℂ)
    (c : Fin m × Fin ℓ → ℚ) : Lam ω z c = ∑ j, bq ω hωalg c j • z j := by
  funext i
  simp only [Lam, Fintype.linearCombination_apply, bq, Finset.sum_apply, Pi.smul_apply,
    Subfield.smul_def, smul_eq_mul, Rat.smul_def, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring

theorem main (ω : Fin m → ℂ) (hωQ : LinearIndependent ℚ ω) (hωalg : ∀ a, ω a ∈ Qbar)
    (z : Fin ℓ → Fin d → ℂ) (hzind : LinearIndependent (↥Qbar) z)
    (η : Fin m × Fin ℓ → (Fin d → ℂ) × (Fin m × Fin d → ℂ))
    (hη1 : ∀ p i, (η p).1 i ∈ Submodule.span ℚ (Set.range ω))
    (hηΥ : ∀ p, Ups d m ω (η p) = ω p.1 • z p.2)
    (V' : Submodule ℂ (Fin d → ℂ)) {q : ℕ} (φ : Fin q → Fin m × Fin d → ℤ)
    (L₁ : Submodule ℂ (Fin m × Fin d → ℂ)) (hL₁ : ∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0) :
    Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : Fin m × Fin ℓ → ℤ => fun j => (s j : ℚ)) ''
        {s : Fin m × Fin ℓ → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
            ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1})) ≤
      m * Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range z) ⊓
        Submodule.span (↥Qbar) {x : Fin d → ℂ | ∃ τ ∈ ((Submodule.span ℂ
          {v : Fin d → ℂ | v ∈ V' ∧ ∀ i, v i ∈ Qbar}).prod L₁).map (Ups d m ω),
          ∃ κ : Fin d → ℂ, (∀ i, κ i ∈ Qbar) ∧ x = τ + (2 * (Real.pi : ℂ) * Complex.I) • κ}) := by
  set T := ((Submodule.span ℂ {v : Fin d → ℂ | v ∈ V' ∧ ∀ i, v i ∈ Qbar}).prod L₁).map (Ups d m ω)
    with hT
  set S := {x : Fin d → ℂ | ∃ τ ∈ T,
    ∃ κ : Fin d → ℂ, (∀ i, κ i ∈ Qbar) ∧ x = τ + (2 * (Real.pi : ℂ) * Complex.I) • κ} with hS
  set F := Submodule.span (↥Qbar) (Set.range z) ⊓ Submodule.span (↥Qbar) S with hF
  set G := Submodule.span ℚ ((fun s : Fin m × Fin ℓ → ℤ => fun j => (s j : ℚ)) ''
        {s : Fin m × Fin ℓ → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
            ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1}) with hG
  -- A5: the image of a relation lies in `S`
  have key : ∀ s : Fin m × Fin ℓ → ℤ, (∑ j, (s j : ℂ) • (η j).1) ∈ V' →
      (∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1) →
      Lam ω z (fun j => (s j : ℚ)) ∈ S := by
    intro s hV hk
    simp only [prod_exp] at hk
    obtain ⟨r, hr⟩ := rat_lift φ (fun i => ∑ j, (s j : ℂ) * (η j).2 i)
      (fun k => Complex.exp_eq_one_iff.mp (hk k))
    set ζ := ∑ j, (s j : ℂ) • η j with hζ
    have h1 : ζ.1 = ∑ j, (s j : ℂ) • (η j).1 := by simp [hζ, Prod.fst_sum]
    have h2 : ∀ i, ζ.2 i = ∑ j, (s j : ℂ) * (η j).2 i := by
      intro i; simp [hζ, Prod.snd_sum, Finset.sum_apply]
    have hLam : Lam ω z (fun j => (s j : ℚ)) = Ups d m ω ζ := by
      rw [Lam, Fintype.linearCombination_apply, hζ, map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_smul, hηΥ p, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    refine ⟨Ups d m ω (ζ.1, fun i => ζ.2 i - 2 * Real.pi * I * r i),
      ⟨_, Submodule.mem_prod.mpr ⟨?_, ?_⟩, rfl⟩, fun i => ∑ k, ω k * (r (k, i) : ℂ), ?_, ?_⟩
    · apply Submodule.subset_span
      refine ⟨h1 ▸ hV, fun i => ?_⟩
      rw [h1, Finset.sum_apply]
      exact sum_mem fun j _ => by
        simpa using mul_mem (intCast_mem Qbar (s j)) (span_le_Qbar ω hωalg _ (hη1 j i))
    · rw [hL₁]; intro k; simpa [h2] using hr k
    · intro i; exact sum_mem fun k _ => mul_mem (hωalg k) (SubfieldClass.ratCast_mem _ _)
    · rw [hLam]; funext i
      simp only [Ups_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, add_assoc,
        ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
  -- `Λ` is always inside `span z`
  have hLz : ∀ c, Lam ω z c ∈ Submodule.span (↥Qbar) (Set.range z) := by
    intro c; rw [Lam_eq ω hωalg]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  -- `Λ(G) ⊆ F`
  have hΛF : ∀ c ∈ G, Lam ω z c ∈ F := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, ⟨hsV, hsexp⟩, rfl⟩ := hx
      exact ⟨hLz _, Submodule.subset_span (key s hsV hsexp)⟩
    | zero => rw [map_zero]; exact F.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact F.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      have : a • Lam ω z x = ((a : ↥Qbar)) • Lam ω z x := by
        funext i; simp [Subfield.smul_def, Rat.smul_def]
      rw [this]; exact F.smul_mem _ hx
  -- coordinates
  have : FiniteDimensional (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range z)) :=
    FiniteDimensional.span_of_finite _ (Set.finite_range z)
  have hFfin : FiniteDimensional (↥Qbar) ↥F := Submodule.finiteDimensional_of_le inf_le_left
  let B := Module.Basis.span hzind
  have hrepr : ∀ c (h : Lam ω z c ∈ Submodule.span (↥Qbar) (Set.range z)) j,
      B.repr ⟨Lam ω z c, h⟩ j = bq ω hωalg c j := by
    intro c h j
    have : (⟨Lam ω z c, h⟩ : Submodule.span (↥Qbar) (Set.range z))
        = ∑ j, bq ω hωalg c j • B j := by
      apply Subtype.ext; simp [B, Lam_eq ω hωalg]
    rw [this, B.repr_sum_self]
  let ρ : Fin ℓ → Module.Dual (↥Qbar) ↥F := fun j =>
    (B.coord j) ∘ₗ (Submodule.inclusion (inf_le_left : F ≤ Submodule.span (↥Qbar) (Set.range z)))
  have hρ : ∀ c (h : Lam ω z c ∈ F) j, ρ j ⟨Lam ω z c, h⟩ = bq ω hωalg c j := by
    intro c h j
    simp only [ρ, LinearMap.comp_apply, Module.Basis.coord_apply]
    exact hrepr c h.1 j
  have hsep : ∀ v : ↥F, (∀ j, ρ j v = 0) → v = 0 := by
    intro v hv
    have h0 : B.repr (Submodule.inclusion inf_le_left v) = 0 :=
      Finsupp.ext fun j => by simpa [ρ, Module.Basis.coord_apply] using hv j
    rw [LinearEquiv.map_eq_zero_iff] at h0
    exact (map_eq_zero_iff _ (Submodule.inclusion_injective _)).mp h0
  obtain ⟨κ, _, a, hcard, hsepa⟩ := exists_sep ρ hsep
  let Θ : (Fin m × Fin ℓ → ℚ) →ₗ[ℚ] (Fin m × κ → ℚ) :=
    LinearMap.funLeft ℚ ℚ (fun p : Fin m × κ => (p.1, a p.2))
  have hinj : Function.Injective (Θ ∘ₗ G.subtype) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨c, hc⟩ hx
    have hΘ : ∀ b t, c (b, a t) = 0 := fun b t => congrFun (LinearMap.mem_ker.mp hx) (b, t)
    have hcF := hΛF c hc
    have hv : (⟨Lam ω z c, hcF⟩ : ↥F) = 0 := hsepa _ fun t => by
      rw [hρ c hcF]; apply Subtype.ext; simp [bq, hΘ]
    have hcoord : ∀ j, bq ω hωalg c j = 0 := fun j => by rw [← hρ c hcF j, hv, map_zero]
    apply Subtype.ext
    funext p
    obtain ⟨b, j⟩ := p
    have hj := congrArg Subtype.val (hcoord j)
    have := Fintype.linearIndependent_iff.mp hωQ (fun b => c (b, j)) (by
      simpa [bq, Rat.smul_def] using hj)
    simpa using this b
  calc Module.finrank ℚ ↥G ≤ Module.finrank ℚ (Fin m × κ → ℚ) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = m * Fintype.card κ := by simp [Module.finrank_fintype_fun_eq_card, Fintype.card_prod]
    _ ≤ m * Module.finrank (↥Qbar) ↥F := Nat.mul_le_mul_left _ hcard

end RC1_RRL

-- `hω1`, `hωmul`, `hη2` are part of the contract but not needed for this bound.
set_option linter.unusedVariables false in
open DiazModulus RC1_RRL in
theorem solution {d m ℓ q : ℕ} (ω : Fin m → ℂ) (hωQ : LinearIndependent ℚ ω)
    (hωalg : ∀ a, ω a ∈ Qbar) (hω1 : (1 : ℂ) ∈ Submodule.span ℚ (Set.range ω))
    (hωmul : ∀ a b, ω a * ω b ∈ Submodule.span ℚ (Set.range ω))
    (z : Fin ℓ → Fin d → ℂ) (hzind : LinearIndependent (↥Qbar) z)
    (η : Fin m × Fin ℓ → (Fin d → ℂ) × (Fin m × Fin d → ℂ))
    (hη1 : ∀ p i, (η p).1 i ∈ Submodule.span ℚ (Set.range ω)) (hη2 : ∀ p r, (η p).2 r ∈ LogAlg)
    (hηΥ : ∀ p, (LinearMap.pi fun i : Fin d =>
        (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)) (η p) = ω p.1 • z p.2)
    (V' : Submodule ℂ (Fin d → ℂ)) (φ : Fin q → Fin m × Fin d → ℤ) (L₁ : Submodule ℂ (Fin m × Fin d → ℂ))
    (hL₁ : ∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0) :
    Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : Fin m × Fin ℓ → ℤ => fun j => (s j : ℚ)) ''
        {s : Fin m × Fin ℓ → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
            ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1})) ≤
      m * Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range z) ⊓
        Submodule.span (↥Qbar) {x : Fin d → ℂ | ∃ τ ∈ ((Submodule.span ℂ {v : Fin d → ℂ | v ∈ V' ∧ ∀ i, v i ∈ Qbar}).prod L₁).map (LinearMap.pi fun i : Fin d =>
        (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)),
          ∃ κ : Fin d → ℂ, (∀ i, κ i ∈ Qbar) ∧ x = τ + (2 * (Real.pi : ℂ) * Complex.I) • κ}) := by
  exact main ω hωQ hωalg z hzind η hη1 hηΥ V' φ L₁ hL₁
