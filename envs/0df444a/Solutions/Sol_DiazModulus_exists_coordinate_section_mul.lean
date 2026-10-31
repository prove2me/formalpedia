-- Prove2me | solution 1 for DiazModulus.exists_coordinate_section_mul
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:00:54.429669+00:00
-- url     : https://prove2.me/submissions/57bcb4ce-fa1a-41c3-9fae-1030ae01097c

import Mathlib

open Complex ComplexConjugate

/-! # A coordinate section of a subgroup of `ℤ^{A₁}`

Among the subsets `J ⊆ A₁` with `Φ ∩ ℤ^J = 0` (no nonzero `φ ∈ Φ` supported on `J`; `J = ∅` qualifies) take one
of largest size. For `i ∉ J` the larger set `J ∪ {i}` fails, which gives a nonzero `ψ_i ∈ Φ` supported on
`J ∪ {i}`; its `i`-th entry is nonzero, since otherwise `ψ_i ∈ Φ ∩ ℤ^J = 0`. Put `ψ_i = 0` for `i ∈ J`. The system
`⟨ψ_i, v⟩ = 0` is triangular in the coordinates outside `J`: for `i ∉ J` it reads
`ψ_i(i) v_i + Σ_{i′∈J} ψ_i(i′) v_{i′} = 0`. Hence the restriction `L → ℂ^J` is injective (a solution vanishing on
`J` vanishes) and onto (solve for `v_i`, `i ∉ J`), so it is a linear bijection and `dim L = |J|`. -/

namespace C13_G5

/-- `Φ ∩ ℤ^J = 0`. -/
def Free {A₁ : Type*} (Φ : AddSubgroup (A₁ → ℤ)) (J : Finset A₁) : Prop :=
  ∀ φ ∈ Φ, (∀ i ∉ J, φ i = 0) → φ = 0

/-- A largest `J` with `Φ ∩ ℤ^J = 0`. -/
theorem exists_max_free {A₁ : Type*} [Fintype A₁] (Φ : AddSubgroup (A₁ → ℤ)) :
    ∃ J : Finset A₁, Free Φ J ∧ ∀ J' : Finset A₁, Free Φ J' → J'.card ≤ J.card := by
  classical
  obtain ⟨J, hJ, hmax⟩ := Finset.exists_max_image
    ((Finset.univ : Finset (Finset A₁)).filter (fun J => Free Φ J)) Finset.card
    ⟨∅, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; intro φ _ h; funext i; exact h i (by simp)⟩
  exact ⟨J, (Finset.mem_filter.mp hJ).2, fun J' hJ' => hmax J' (by simp [hJ'])⟩

/-- Restricting a solution of a triangular system: the dimension is the number of free coordinates. -/
theorem finrank_eq_card {A₁ : Type*} [Fintype A₁] (L : Submodule ℂ (A₁ → ℂ)) (J : Finset A₁)
    (hinj : ∀ v ∈ L, (∀ i ∈ J, v i = 0) → v = 0) (hsurj : ∀ x : A₁ → ℂ, ∃ v ∈ L, ∀ i ∈ J, v i = x i) :
    Module.finrank ℂ ↥L = J.card := by
  classical
  let π : ↥L →ₗ[ℂ] (↥J → ℂ) :=
    { toFun := fun v i => (v : A₁ → ℂ) i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hbij : Function.Bijective π := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      exact Subtype.ext (hinj v v.2 (fun i hi => congrFun hv ⟨i, hi⟩))
    · intro x
      obtain ⟨v, hv, hvx⟩ := hsurj (fun a => if ha : a ∈ J then x ⟨a, ha⟩ else 0)
      exact ⟨⟨v, hv⟩, funext fun i => by simp [π, hvx i i.2]⟩
  rw [(LinearEquiv.ofBijective π hbij).finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

/-- The `i`-th equation, `i ∉ J`, splits into the `J` part and the diagonal entry. -/
theorem sum_split {A₁ : Type*} [Fintype A₁] [DecidableEq A₁] (J : Finset A₁) (ψ : A₁ → ℤ) (v : A₁ → ℂ)
    (i : A₁) (hi : i ∉ J) (hψ : ∀ i' ∉ J, i' ≠ i → ψ i' = 0) :
    ∑ i', (ψ i' : ℂ) * v i' = ∑ i' ∈ J, (ψ i' : ℂ) * v i' + (ψ i : ℂ) * v i := by
  rw [← Finset.sum_add_sum_compl J, Finset.sum_eq_single_of_mem i (Finset.mem_compl.mpr hi)]
  intro b hb hbi
  rw [hψ b (Finset.mem_compl.mp hb) hbi]; simp

end C13_G5

open C13_G5 in
theorem solution {A₁ : Type*} [Fintype A₁] (Φ : AddSubgroup (A₁ → ℤ)) :
    ∃ (J : Finset A₁) (ψ : A₁ → A₁ → ℤ), (∀ φ ∈ Φ, (∀ i ∉ J, φ i = 0) → φ = 0) ∧ (∀ i, ψ i ∈ Φ) ∧
      (∀ i ∈ J, ψ i = 0) ∧ (∀ i ∉ J, ψ i i ≠ 0 ∧ ∀ i' ∉ J, i' ≠ i → ψ i i' = 0) ∧
      ∀ L : Submodule ℂ (A₁ → ℂ), (∀ v, v ∈ L ↔ ∀ i, ∑ i', (ψ i i' : ℂ) * v i' = 0) → Module.finrank ℂ ↥L = J.card := by
  classical
  obtain ⟨J, hJ, hmax⟩ := exists_max_free Φ
  -- for `i ∉ J`, the failure of `J ∪ {i}`
  have hex : ∀ i, i ∉ J → ∃ φ ∈ Φ, (∀ i' ∉ insert i J, φ i' = 0) ∧ φ ≠ 0 := by
    intro i hi
    by_contra h
    have := hmax (insert i J) (fun φ hφ hs => by_contra fun hne => h ⟨φ, hφ, hs, hne⟩)
    rw [Finset.card_insert_of_notMem hi] at this
    omega
  choose! φ hφΦ hφs hφne using hex
  have hdiag : ∀ i, i ∉ J → φ i i ≠ 0 := by
    intro i hi h0
    refine hφne i hi (hJ _ (hφΦ i hi) fun i' hi' => ?_)
    by_cases h : i' = i
    · rw [h]; exact h0
    · exact hφs i hi i' (by simp [h, hi'])
  have hoff : ∀ i, i ∉ J → ∀ i' ∉ J, i' ≠ i → φ i i' = 0 :=
    fun i hi i' hi' hne => hφs i hi i' (by simp [hne, hi'])
  refine ⟨J, fun i => if i ∈ J then 0 else φ i, hJ, ?_, ?_, ?_, ?_⟩
  · intro i; by_cases hi : i ∈ J
    · simp [hi, Φ.zero_mem]
    · simp [hi, hφΦ i hi]
  · intro i hi; simp [hi]
  · intro i hi
    simp only [hi, if_false]
    exact ⟨hdiag i hi, hoff i hi⟩
  · intro L hL
    apply finrank_eq_card L J
    · intro v hv hvJ
      funext i
      by_cases hi : i ∈ J
      · exact hvJ i hi
      · have h := (hL v).mp hv i
        simp only [hi, if_false] at h
        rw [sum_split J (φ i) v i hi (hoff i hi), Finset.sum_eq_zero (fun i' hi' => by rw [hvJ i' hi', mul_zero]),
          zero_add] at h
        exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hdiag i hi)
    · intro x
      refine ⟨fun i => if i ∈ J then x i else -(∑ i' ∈ J, (φ i i' : ℂ) * x i') / (φ i i : ℂ), ?_, ?_⟩
      · rw [hL]
        intro i
        by_cases hi : i ∈ J
        · simp [hi]
        · simp only [hi, if_false]
          rw [sum_split J (φ i) _ i hi (hoff i hi), if_neg hi]
          have hne : (φ i i : ℂ) ≠ 0 := by exact_mod_cast hdiag i hi
          rw [Finset.sum_congr rfl (fun i' hi' => by rw [if_pos hi'])]
          field_simp
          ring
      · intro i hi; simp [hi]
