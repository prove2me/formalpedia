-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_sub_permField_le_of_adjacent_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:42:18.727032+00:00
-- url     : https://prove2.me/submissions/2149eac0-5300-4b3f-9845-8c90dd272b3c

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Permutation

noncomputable section
open MeasureTheory Finset
open FunctionalInequalities.Analysis.Tensor
open scoped Classical
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  {ν : MeasureTheory.ProbabilityMeasure V} {k : ℕ}
/-- `permField` is a left action: `permField (σ * τ) = permField σ ∘ permField τ`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField_mul (σ τ : Equiv.Perm (Fin k)) (u : Field ν k) :
    permField (σ * τ) u = permField σ (permField τ u) := rfl
/-- `permField σ` commutes with subtraction. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField_sub (σ : Equiv.Perm (Fin k)) (u v : Field ν k) :
    permField σ (u - v) = permField σ u - permField σ v := rfl
/-- `normSq u` is the squared norm of `u` in `PiLp 2`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_eq_norm_toLp_sq (u : Field ν k) :
    normSq u = ‖(WithLp.toLp 2 u :
      PiLp 2 fun _ : Fin k → Fin (Module.finrank ℝ V) => Lp ℝ 2 (ν : Measure V))‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl
/-- The Hilbert–Schmidt norm `√(normSq u)` is the norm of `u` in `PiLp 2`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_eq (u : Field ν k) :
    √(normSq u) = ‖(WithLp.toLp 2 u :
      PiLp 2 fun _ : Fin k → Fin (Module.finrank ℝ V) => Lp ℝ 2 (ν : Measure V))‖ := by
  rw [normSq_eq_norm_toLp_sq, Real.sqrt_sq (norm_nonneg _)]
/-- The triangle inequality for the Hilbert–Schmidt norm `√(normSq ·)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_add_le (u v : Field ν k) :
    √(normSq (u + v)) ≤ √(normSq u) + √(normSq v) := by
  simp only [sqrt_normSq_eq, WithLp.toLp_add]
  exact norm_add_le _ _
/-- `normSq` is invariant under negation. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_neg (u : Field ν k) : normSq (-u) = normSq u := by
  simp [normSq]
/-- `permField σ` preserves the squared Hilbert–Schmidt norm. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_permField (σ : Equiv.Perm (Fin k)) (u : Field ν k) :
    normSq (permField σ u) = normSq u := by
  unfold normSq
  exact (Equiv.arrowCongr σ.symm (Equiv.refl (Fin (Module.finrank ℝ V)))).sum_comp
    fun J => ‖u J‖ ^ 2
/-- Subadditivity of the displacement: `d(σ τ) ≤ d(σ) + d(τ)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_sub_permField_mul_le (σ τ : Equiv.Perm (Fin k)) (u : Field ν k) :
    √(normSq (u - permField (σ * τ) u)) ≤
      √(normSq (u - permField σ u)) + √(normSq (u - permField τ u)) := by
  have h : u - permField (σ * τ) u = (u - permField σ u) + permField σ (u - permField τ u) := by
    rw [permField_sub, permField_mul]
    abel
  rw [h]
  refine (sqrt_normSq_add_le _ _).trans ?_
  rw [normSq_permField]
/-- The displacement of `σ⁻¹` equals that of `σ`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_sub_permField_inv (σ : Equiv.Perm (Fin k)) (u : Field ν k) :
    normSq (u - permField σ⁻¹ u) = normSq (u - permField σ u) := by
  have h : u - permField σ⁻¹ u = -permField σ⁻¹ (u - permField σ u) := by
    rw [permField_sub, ← permField_mul, inv_mul_cancel, permField_one]
    abel
  rw [h, normSq_neg, normSq_permField]
/-- Membership in the permutations of the first `p` positions. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.mem_fixingOutside_slots_zero {p : ℕ} {σ : Equiv.Perm (Fin k)} :
    σ ∈ fixingOutside (slots k 0 p) ↔ ∀ x : Fin k, p ≤ x.val → σ x = x := by
  simp only [fixingOutside, slots, mem_filter, mem_univ, true_and, zero_le, not_lt]
/-- `finRotate k ℓ = ℓ + 1` below the last position. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.val_finRotate_of_lt {ℓ : Fin k} (h : ℓ.val + 1 < k) :
    (finRotate k ℓ).val = ℓ.val + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have := finRotate_of_lt (n := m) (k := ℓ.val) (by omega)
  rw [show ℓ = ⟨ℓ.val, ℓ.val.lt_succ_of_lt (by omega)⟩ from rfl, this]
/-- A chain of adjacent transpositions moving position `a` up to position `b`: some
permutation of the first `b + 1` positions sends `a` to `b` with displacement at most
`(b - a) B`, if every adjacent transposition `τ_ℓ` with `ℓ + 1 < q` has displacement at most
`B`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.exists_chain {q : ℕ} (u : Field ν k) {B : ℝ}
    (hB : ∀ ℓ : Fin k, ℓ.val + 1 < q →
      √(normSq (u - permField (Equiv.swap ℓ (finRotate k ℓ)) u)) ≤ B) :
    ∀ (n : ℕ) (a b : Fin k), b.val = a.val + n → b.val < q →
      ∃ ρ ∈ fixingOutside (slots k 0 (b.val + 1)), ρ a = b ∧
        √(normSq (u - permField ρ u)) ≤ n * B := by
  intro n
  induction n with
  | zero =>
    intro a b hab _
    have : b = a := Fin.ext (by simpa using hab)
    subst this
    refine ⟨1, mem_fixingOutside_slots_zero.mpr fun _ _ => rfl, rfl, ?_⟩
    simp [normSq]
  | succ n ih =>
    intro a b hab hbq
    set b' : Fin k := ⟨b.val - 1, by omega⟩ with hb'
    obtain ⟨ρ', hρ'mem, hρ'a, hρ'd⟩ := ih a b' (by simp [hb']; omega) (by simp [hb']; omega)
    have hrot : finRotate k b' = b := Fin.ext (by
      rw [val_finRotate_of_lt (by simp [hb']; omega)]; simp [hb']; omega)
    refine ⟨Equiv.swap b' b * ρ', ?_, ?_, ?_⟩
    · rw [mem_fixingOutside_slots_zero] at hρ'mem ⊢
      intro x hx
      have hxb' : x ≠ b' := fun h => by subst h; simp [hb'] at hx; omega
      have hxb : x ≠ b := fun h => by subst h; omega
      rw [Equiv.Perm.mul_apply, hρ'mem x (by simp [hb'] at hx ⊢; omega),
        Equiv.swap_apply_of_ne_of_ne hxb' hxb]
    · rw [Equiv.Perm.mul_apply, hρ'a, Equiv.swap_apply_left]
    · refine (sqrt_normSq_sub_permField_mul_le _ _ u).trans ?_
      have h1 := hB b' (by simp [hb']; omega)
      rw [hrot] at h1
      push_cast
      linarith
/-- **Word length bound for the displacement.** If every adjacent transposition `τ_ℓ`
(`ℓ + 1 < q`) moves `u` by at most `B` in the Hilbert–Schmidt norm, then every permutation of
the first `q` positions moves `u` by at most `q² B`. -/
theorem solution {q : ℕ} (hq : q ≤ k) (u : FunctionalInequalities.KLS.LogConcave.PoissonIterate.Field ν k) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ ℓ : Fin k, ℓ.val + 1 < q →
      √(FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField (Equiv.swap ℓ (finRotate k ℓ)) u)) ≤ B)
    {σ : Equiv.Perm (Fin k)} (hσ : σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside (FunctionalInequalities.Analysis.Tensor.slots k 0 q)) :
    √(FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField σ u)) ≤ (q : ℝ) ^ 2 * B := by
  suffices ∀ p ≤ q, ∀ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside (FunctionalInequalities.Analysis.Tensor.slots k 0 p),
      √(FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField σ u)) ≤ (p : ℝ) ^ 2 * B from this q le_rfl σ hσ
  intro p
  induction p with
  | zero =>
    intro _ σ hσ
    have : σ = 1 := Equiv.ext fun x => FunctionalInequalities.KLS.LogConcave.PoissonIterate.mem_fixingOutside_slots_zero.mp hσ x (Nat.zero_le _)
    subst this
    simp [FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq]
  | succ p ih =>
    intro hpq σ hσ
    rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.mem_fixingOutside_slots_zero] at hσ
    set b : Fin k := ⟨p, by omega⟩ with hb
    have hbv : b.val = p := rfl
    have ha : (σ b).val ≤ p := by
      by_contra h
      have hfix := hσ (σ b) (by omega)
      have : σ b = b := σ.injective hfix
      rw [this] at h
      simp [hb] at h
    obtain ⟨ρ, hρmem, hρa, hρd⟩ :=
      FunctionalInequalities.KLS.LogConcave.PoissonIterate.exists_chain u hB (p - (σ b).val) (σ b) b (by rw [hbv]; omega) (by rw [hbv]; omega)
    rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.mem_fixingOutside_slots_zero] at hρmem
    have hσ' : ρ * σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside (FunctionalInequalities.Analysis.Tensor.slots k 0 p) := by
      rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.mem_fixingOutside_slots_zero]
      intro x hx
      rcases eq_or_ne x b with rfl | hxb
      · rw [Equiv.Perm.mul_apply, hρa]
      · have hx' : p + 1 ≤ x.val := by
          have : x.val ≠ p := fun h => hxb (Fin.ext (by simp [hb, h]))
          omega
        rw [Equiv.Perm.mul_apply, hσ x hx', hρmem x (by simp [hb]; omega)]
    have hdecomp : σ = ρ⁻¹ * (ρ * σ) := by group
    have h1 := FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_sub_permField_mul_le ρ⁻¹ (ρ * σ) u
    rw [← hdecomp, FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_sub_permField_inv] at h1
    have h2 := ih (by omega) _ hσ'
    have h3 : ((p - (σ b).val : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le _ _
    have h4 : ((p - (σ b).val : ℕ) : ℝ) * B ≤ p * B := mul_le_mul_of_nonneg_right h3 hB0
    have h5 : (p : ℝ) * B + (p : ℝ) ^ 2 * B ≤ ((p + 1 : ℕ) : ℝ) ^ 2 * B := by
      push_cast
      nlinarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
    linarith
