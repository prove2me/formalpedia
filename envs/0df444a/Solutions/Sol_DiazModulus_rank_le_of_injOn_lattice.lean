-- Prove2me | solution 1 for DiazModulus.rank_le_of_injOn_lattice
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:14:52.540203+00:00
-- url     : https://prove2.me/submissions/e55b6cd7-d2ef-4bf6-99f2-7b64de99aecc

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Rank of a lattice on which a linear map is injective with values in `2πiℤ^q`

Pick a ℚ-basis `t` of `span_ℚ A` inside (the rational image of) `A` (`exists_linearIndependent`),
and for each `b ∈ t` a preimage `s_b ∈ A` and integers `e_b` with `Ψ(s_b) = 2πi e_b`. The vectors
`Ψ(s_b)` lie in `range Ψ`; it suffices to show they are ℂ-linearly independent, since then
`rank A = |t| ≤ dim range Ψ` (`finrank_span_eq_card`, `Submodule.finrank_mono`).
A complex relation among the `Ψ(s_b)` is a complex kernel vector of the integer matrix
`(e_b k)`. Such a matrix has no complex kernel once it has no rational one (the left-inverse
argument of `intMatrix_ker_facts`, repeated here). A rational kernel vector `c` is cleared of
denominators, `D c_b = n_b ∈ ℤ`; then `s = Σ n_b s_b ∈ A` has `Ψ(s) = 2πi D Σ c_b e_b = 0`, so
`s = 0` by injectivity, so `Σ D c_b b = 0`, and the independence of `t` gives `c = 0`. -/

namespace C14_S4
open DiazModulus

theorem exists_leftInv {ι : Type} [Fintype ι] {q : ℕ} (φ : Fin q → ι → ℤ)
    (hφ : ∀ v : ι → ℚ, (∀ k, ∑ i, (φ k i : ℚ) * v i = 0) → v = 0) :
    ∃ B : ι → Fin q → ℚ, ∀ w : ι → ℂ, ∀ i, ∑ k, (B i k : ℂ) * ∑ j, (φ k j : ℂ) * w j = w i := by
  classical
  let f : (ι → ℚ) →ₗ[ℚ] (Fin q → ℚ) :=
    { toFun := fun v k => ∑ i, (φ k i : ℚ) * v i
      map_add' := by intro v w; funext k; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c v; funext k
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
        exact Finset.sum_congr rfl (fun _ _ => by ring) }
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hφ v (fun k => congrFun hv k)
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective hker
  refine ⟨fun i k => g (Pi.single k 1) i, ?_⟩
  have hδ : ∀ i j, ∑ k, g (Pi.single k 1) i * (φ k j : ℚ) = (Pi.single j (1 : ℚ) : ι → ℚ) i := by
    intro i j
    have h1 : g (f (Pi.single j 1)) = Pi.single j 1 := by
      rw [← LinearMap.comp_apply, hg, LinearMap.id_apply]
    have h2 : f (Pi.single j 1) = ∑ k, (φ k j : ℚ) • (Pi.single k (1 : ℚ) : Fin q → ℚ) := by
      funext k'
      simp [f, Finset.sum_apply, Pi.single_apply]
    rw [← h1, h2, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  intro w i
  calc ∑ k, (g (Pi.single k 1) i : ℂ) * ∑ j, (φ k j : ℂ) * w j
      = ∑ j, ((∑ k, g (Pi.single k 1) i * (φ k j : ℚ) : ℚ) : ℂ) * w j := by
        simp only [Finset.mul_sum, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
    _ = w i := by
        simp only [hδ]
        simp [Pi.single_apply, apply_ite]


theorem clear_den {ι : Type} [Fintype ι] (c : ι → ℚ) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ b, ∃ n : ℤ, (n : ℚ) = D * c b := by
  classical
  refine ⟨∏ b, (c b).den, Finset.prod_ne_zero_iff.mpr (fun b _ => (c b).den_nz), fun b => ?_⟩
  refine ⟨((∏ b, (c b).den) / (c b).den : ℕ) * (c b).num, ?_⟩
  have hd : (c b).den ∣ ∏ b, (c b).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ b)
  have h1 : (((∏ b, (c b).den) / (c b).den : ℕ) : ℚ) * (c b).den = ((∏ b, (c b).den : ℕ) : ℚ) := by
    exact_mod_cast Nat.div_mul_cancel hd
  rw [← h1, mul_assoc, mul_comm ((c b).den : ℚ), Rat.mul_den_eq_num]
  rw [Int.cast_mul, Int.cast_natCast]

end C14_S4

open DiazModulus C14_S4 in
theorem solution {N : Type} [Fintype N] {q : ℕ} (Ψ : (N → ℂ) →ₗ[ℂ] (Fin q → ℂ))
    (A : AddSubgroup (N → ℤ))
    (hA : ∀ s ∈ A, ∃ e : Fin q → ℤ, Ψ (fun j => (s j : ℂ)) = fun k => 2 * Real.pi * Complex.I * e k)
    (hinj : ∀ s ∈ A, Ψ (fun j => (s j : ℂ)) = 0 → s = 0) :
    Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : N → ℤ => fun j => (s j : ℚ)) '' (A : Set (N → ℤ))))
      ≤ Module.finrank ℂ ↥(LinearMap.range Ψ) := by
  classical
  set img := (fun s : N → ℤ => fun j => (s j : ℚ)) '' (A : Set (N → ℤ))
  obtain ⟨t, ht_sub, ht_span, ht_li⟩ := exists_linearIndependent ℚ img
  have : Fintype t := (ht_li.setFinite).fintype
  have hrank : Module.finrank ℚ ↥(Submodule.span ℚ img) = Fintype.card t := by
    rw [← ht_span, ← finrank_span_eq_card ht_li, Subtype.range_coe]
  rw [hrank]
  have hpre : ∀ b : t, ∃ s ∈ A, (fun j => (s j : ℚ)) = (b : N → ℚ) := fun b => ht_sub b.2
  choose s hsA hs using hpre
  choose e he using fun b => hA (s b) (hsA b)
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  -- the rational kernel of `(e_b k)` is trivial
  have hφ : ∀ c : t → ℚ, (∀ k, ∑ b, (e b k : ℚ) * c b = 0) → c = 0 := by
    intro c hc
    obtain ⟨D, hD, hn⟩ := clear_den c
    choose n hn using hn
    have hsum : (∑ b, n b • s b) ∈ A := AddSubgroup.sum_mem _ (fun b _ => AddSubgroup.zsmul_mem _ (hsA b) _)
    have hcast : (fun j => (((∑ b, n b • s b) j : ℤ) : ℂ)) = ∑ b, (n b : ℂ) • fun j => (s b j : ℂ) := by
      funext j; simp [Finset.sum_apply]
    have hzero : Ψ (fun j => (((∑ b, n b • s b) j : ℤ) : ℂ)) = 0 := by
      rw [hcast, map_sum]
      simp only [map_smul, he]
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have hk := congrArg (fun r : ℚ => ((D * r : ℚ) : ℂ)) (hc k)
      simp only [mul_zero, Rat.cast_zero, Finset.mul_sum, Rat.cast_sum, Rat.cast_mul,
        Rat.cast_intCast, Rat.cast_natCast] at hk
      calc ∑ b, (n b : ℂ) * (2 * Real.pi * Complex.I * e b k)
          = 2 * Real.pi * Complex.I * ∑ b, (D : ℂ) * ((e b k : ℂ) * (c b : ℂ)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun b _ => ?_)
            have := congrArg (fun r : ℚ => (r : ℂ)) (hn b)
            simp only [Rat.cast_intCast, Rat.cast_mul, Rat.cast_natCast] at this
            rw [this]; ring
        _ = 0 := by rw [hk, mul_zero]
    have hs0 := hinj _ hsum hzero
    have hrelQ : ∑ b, ((D : ℚ) * c b) • (b : N → ℚ) = 0 := by
      funext j
      have := congrFun hs0 j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      have hq := congrArg (fun z : ℤ => (z : ℚ)) this
      simp only [Int.cast_sum, Int.cast_mul, Int.cast_zero] at hq
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← hq]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [← hn b, ← hs b]
    have := Fintype.linearIndependent_iff.mp ht_li _ hrelQ
    funext b
    have hb := this b
    simpa [hD] using hb
  obtain ⟨B, hB⟩ := exists_leftInv (fun k b => e b k) hφ
  -- the vectors `Ψ(s_b)` are ℂ-independent
  have hli : LinearIndependent ℂ (fun b : t => Ψ (fun j => (s b j : ℂ))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg b
    have hk : ∀ k, ∑ b, (e b k : ℂ) * g b = 0 := by
      intro k
      have := congrFun hg k
      simp only [Finset.sum_apply, Pi.smul_apply, he, smul_eq_mul, Pi.zero_apply] at this
      have h' : 2 * Real.pi * Complex.I * ∑ b, (e b k : ℂ) * g b = 0 := by
        rw [← this, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      exact (mul_eq_zero.mp h').resolve_left h2pi
    rw [← hB g b]
    simp [hk]
  calc Fintype.card t
      = Module.finrank ℂ ↥(Submodule.span ℂ (Set.range fun b : t => Ψ (fun j => (s b j : ℂ)))) :=
        (finrank_span_eq_card hli).symm
    _ ≤ Module.finrank ℂ ↥(LinearMap.range Ψ) := by
        apply Submodule.finrank_mono
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        exact LinearMap.mem_range_self Ψ _
