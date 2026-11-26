-- Prove2me | solution 1 for Erdos287.finite_distance_avoiding_distribution_with_prescribed_marginals
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T08:32:33.427807+00:00
-- url     : https://prove2.me/submissions/f74c3ae0-edac-44c6-bd9e-7756f0bdecf9

import Mathlib

open Finset

set_option autoImplicit false

private def coinMass (b : ℝ) (c : Bool) : ℝ := if c = true then b else 1 - b

private theorem coin_mass_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ℝ) (U : Finset ι) :
    (∑ C : ι → Bool, if ∀ i ∈ U, C i = true then ∏ i, coinMass b (C i) else 0) =
      b ^ U.card := by
  classical
  let q (i : ι) (c : Bool) : ℝ :=
    if i ∈ U ∧ c = false then 0 else coinMass b c
  have hprod (C : ι → Bool) :
      (if ∀ i ∈ U, C i = true then ∏ i, coinMass b (C i) else 0) = ∏ i, q i (C i) := by
    by_cases h : ∀ i ∈ U, C i = true
    · rw [if_pos h]
      apply prod_congr rfl
      intro i _
      by_cases hi : i ∈ U
      · simp [q, hi, h i hi]
      · simp [q, hi]
    · rw [if_neg h]
      push Not at h
      obtain ⟨i, hi, hci⟩ := h
      have hfalse : C i = false := by cases h' : C i <;> simp_all
      exact (prod_eq_zero (mem_univ i) (by simp [q, hi, hfalse])).symm
  calc
    _ = ∑ C : ι → Bool, ∏ i, q i (C i) := sum_congr rfl fun C _ => hprod C
    _ = ∏ i, ∑ c : Bool, q i c := (Fintype.prod_sum q).symm
    _ = ∏ i, if i ∈ U then b else 1 := by
      apply prod_congr rfl
      intro i _
      rw [Fintype.sum_bool]
      by_cases hi : i ∈ U <;> simp [q, hi, coinMass]
    _ = _ := by rw [Fintype.prod_ite_mem]; simp

private theorem strip_card (u v g : ℕ) (hu : 0 < u) :
    #{t : Fin (u + v) | (g + (t : ℕ)) % (u + v) < u} = u := by
  let P := u + v
  have hP : 0 < P := by omega
  let f (t : Fin P) : Fin P :=
    ⟨(g + (t : ℕ)) % P, Nat.mod_lt _ hP⟩
  have hf : Function.Injective f := by
    intro s t heq
    have he : g + (s : ℕ) ≡ g + (t : ℕ) [MOD P] := congrArg Fin.val heq
    have hc := Nat.ModEq.add_left_cancel' g he
    apply Fin.ext
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt s.isLt, Nat.mod_eq_of_lt t.isLt] using hc
  have hs := Finite.surjective_of_injective hf
  calc
    _ = (range u).card := by
      apply card_bij (fun t _ => (f t : ℕ))
      · intro t ht
        exact mem_range.mpr (mem_filter.mp ht).2
      · intro s _ t _ h
        exact hf (Fin.ext h)
      · intro z hz
        have hzP : z < P := (mem_range.mp hz).trans_le (by omega)
        obtain ⟨t, ht⟩ := hs ⟨z, hzP⟩
        have hval : (f t : ℕ) = z := congrArg Fin.val ht
        have ht' : (g + (t : ℕ)) % P < u := by
          change (f t : ℕ) < u
          exact hval.trans_lt (mem_range.mp hz)
        exact ⟨t, mem_filter.mpr ⟨mem_univ _, ht'⟩, hval⟩
    _ = _ := card_range _

/-- A uniform periodic strip with independent thinning avoids distances in [u,v].
Within one group, every nonempty joint inclusion has the specified probability. -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℕ) (u v : ℕ) (hu : 0 < u) (b : ℝ) (hb : 0 ≤ b) (hb₁ : b ≤ 1) :
    ∃ (w : Fin (u + v) × (ι → Bool) → ℝ)
      (C : Fin (u + v) × (ι → Bool) → Finset ι),
      (∀ z, 0 ≤ w z) ∧ (∑ z, w z) = 1 ∧
      (∀ z i, i ∈ C z → ∀ j, j ∈ C z → g i ≤ g j →
        ¬ (u ≤ g j - g i ∧ g j - g i ≤ v)) ∧
      ∀ T : Finset ι, T.Nonempty →
        let mass := ∑ z ∈ Finset.univ.filter (fun z => T ⊆ C z), w z
        let bound := ((u : ℝ) / ((u + v : ℕ) : ℝ)) * b ^ T.card
        mass ≤ bound ∧ ((∀ i ∈ T, ∀ j ∈ T, g i = g j) → mass = bound) := by
  classical
  let P := u + v
  have hPn : 0 < P := by omega
  have hP : (P : ℝ) ≠ 0 := by exact_mod_cast hPn.ne'
  let C (z : Fin P × (ι → Bool)) : Finset ι :=
    univ.filter fun i => (g i + (z.1 : ℕ)) % P < u ∧ z.2 i = true
  let w (z : Fin P × (ι → Bool)) : ℝ := (P : ℝ)⁻¹ * ∏ i, coinMass b (z.2 i)
  have hcoin : (∑ c : ι → Bool, ∏ i, coinMass b (c i)) = 1 := by
    simpa using coin_mass_sum b (∅ : Finset ι)
  have hwn (z : Fin P × (ι → Bool)) : 0 ≤ w z := by
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    exact prod_nonneg fun i _ => by unfold coinMass; split <;> linarith
  refine ⟨w, C, hwn, ?_, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    dsimp only [w]
    simp only [← mul_sum, hcoin, mul_one, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    change (P : ℝ) * (P : ℝ)⁻¹ = 1
    exact mul_inv_cancel₀ hP
  · intro z i hi j hj hij h
    have hix := (mem_filter.mp hi).2.1
    have hjx := (mem_filter.mp hj).2.1
    let d := g j - g i
    have he : g j + (z.1 : ℕ) = (g i + (z.1 : ℕ)) + d := by omega
    have hbound : (g i + (z.1 : ℕ)) % P + d < P := by omega
    have hdP : d < P := by omega
    rw [he, Nat.add_mod, Nat.mod_eq_of_lt hdP, Nat.mod_eq_of_lt hbound] at hjx
    omega
  · intro T hT
    dsimp only
    obtain ⟨j, hj⟩ := hT
    let D : Finset (Fin P × (ι → Bool)) := univ.filter fun z =>
      (g j + (z.1 : ℕ)) % P < u ∧ ∀ i ∈ T, z.2 i = true
    have hD : (∑ z ∈ D, w z) =
        ((u : ℝ) / ((u + v : ℕ) : ℝ)) * b ^ T.card := by
      dsimp only [D]
      rw [sum_filter, Fintype.sum_prod_type]
      have hsplit (s : Fin P) :
          (∑ c : ι → Bool,
            if (g j + (s : ℕ)) % P < u ∧ ∀ i ∈ T, c i = true then w (s, c) else 0) =
          if (g j + (s : ℕ)) % P < u then (P : ℝ)⁻¹ * b ^ T.card else 0 := by
        by_cases hgood : (g j + (s : ℕ)) % P < u
        · simp only [hgood, true_and, ite_true, w]
          calc
            _ = ∑ c : ι → Bool, (P : ℝ)⁻¹ *
                (if ∀ i ∈ T, c i = true then ∏ i, coinMass b (c i) else 0) := by
              apply sum_congr rfl
              intro c _
              split <;> simp_all
            _ = _ := by rw [← mul_sum, coin_mass_sum]
        · simp [hgood]
      simp_rw [hsplit]
      rw [← sum_filter, sum_const, nsmul_eq_mul, strip_card u v (g j) hu]
      rw [div_eq_mul_inv, mul_assoc]
    have hsub : univ.filter (fun z => T ⊆ C z) ⊆ D := by
      intro z hz
      obtain ⟨_, hTz⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp (hTz hj)).2.1,
        fun i hi => (mem_filter.mp (hTz hi)).2.2⟩
    constructor
    · exact (sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hwn z)).trans_eq hD
    · intro hsame
      have heq : univ.filter (fun z => T ⊆ C z) = D := by
        refine Subset.antisymm hsub ?_
        intro z hz
        obtain ⟨_, hstrip, hcoins⟩ := mem_filter.mp hz
        apply mem_filter.mpr ⟨mem_univ _, ?_⟩
        intro i hi
        exact mem_filter.mpr ⟨mem_univ _, by simpa only [hsame i hi j hj] using hstrip,
          hcoins i hi⟩
      rw [heq, hD]

