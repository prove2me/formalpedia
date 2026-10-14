-- Prove2me | solution 1 for DEpenoux.LinearProgram.strict_vectorial_maximum
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:31:28.055993+00:00
-- url     : https://prove2.me/submissions/816801a0-8e45-48cc-ad4f-a4d31811ef5b

import Mathlib
import Definitions.Def_DEpenoux_LinearProgram_Model



namespace DEpenoux.LinearProgram

lemma e25_mem_adm {σ : ℕ} (i j : Fin (σ + 1)) : j ∈ admissible σ i ↔ i ≤ j := by
  simp [admissible]

lemma e25_nonempty {σ : ℕ} (i : Fin (σ + 1)) : (admissible σ i).Nonempty :=
  ⟨i, (e25_mem_adm i i).2 le_rfl⟩

lemma e25_bellman_apply (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1) (lam : ℝ)
    (u : Fin (σ + 1) → ℝ) (i : Fin (σ + 1)) :
    BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam u i =
      (admissible σ i).inf' (e25_nonempty i)
        (fun j => d i j + lam * ∑ s, p j s * u s) := rfl

lemma e25_Uij_eq {σ : ℕ} (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ) (lam : ℝ)
    (u : Fin (σ + 1) → ℝ) (i j : Fin (σ + 1)) :
    Uij p d lam u i j = u i - (d i j + lam * ∑ s, p j s * u s) := by
  unfold Uij; ring

lemma e25_bellman_iff (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1) (lam : ℝ)
    (u : Fin (σ + 1) → ℝ) :
    BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam u = u ↔
      u ∈ setA p d lam ∧ u ∈ setB p d lam := by
  constructor
  · intro h
    have hi : ∀ i, (admissible σ i).inf' (e25_nonempty i)
        (fun j => d i j + lam * ∑ s, p j s * u s) = u i := by
      intro i
      rw [← e25_bellman_apply σ p d hp0 hp1 lam u i, h]
    refine ⟨?_, ?_⟩
    · intro i j hij
      have hj : j ∈ admissible σ i := (e25_mem_adm i j).2 hij
      have := Finset.inf'_le (fun j => d i j + lam * ∑ s, p j s * u s) hj
      rw [hi i] at this
      rw [e25_Uij_eq]; linarith
    · intro i
      obtain ⟨j, hj, hj'⟩ := Finset.exists_mem_eq_inf' ((e25_nonempty i) :
        (admissible σ i).Nonempty) (fun j => d i j + lam * ∑ s, p j s * u s)
      rw [hi i] at hj'
      apply Finset.prod_eq_zero hj
      rw [e25_Uij_eq]; linarith
  · rintro ⟨hA, hB⟩
    funext i
    rw [e25_bellman_apply]
    apply le_antisymm
    · obtain ⟨j, hj, hj0⟩ := Finset.prod_eq_zero_iff.1 (hB i)
      rw [e25_Uij_eq] at hj0
      have := Finset.inf'_le (fun j => d i j + lam * ∑ s, p j s * u s) hj
      linarith
    · rw [Finset.le_inf'_iff]
      intro j hj
      have := hA i j ((e25_mem_adm i j).1 hj)
      rw [e25_Uij_eq] at this
      linarith

lemma e25_B_iff (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1) (lam : ℝ)
    (u : Fin (σ + 1) → ℝ) :
    u ∈ setB p d lam ↔
        ∃ J : Fin (σ + 1) → Fin (σ + 1), IsStrategy J ∧
          BertsekasDiscountedPolicyOp (model σ p d hp0 hp1) lam J u = u := by
  have key : ∀ J : Fin (σ + 1) → Fin (σ + 1), ∀ i,
      BertsekasDiscountedPolicyOp (model σ p d hp0 hp1) lam J u i = u i ↔
        Uij p d lam u i (J i) = 0 := by
    intro J i
    have : BertsekasDiscountedPolicyOp (model σ p d hp0 hp1) lam J u i =
        d i (J i) + lam * ∑ s, p (J i) s * u s := rfl
    rw [this, e25_Uij_eq]
    constructor <;> intro h <;> linarith
  constructor
  · intro hB
    have : ∀ i, ∃ j, j ∈ admissible σ i ∧ Uij p d lam u i j = 0 := fun i =>
      Finset.prod_eq_zero_iff.1 (hB i)
    choose J hJ hJ0 using this
    refine ⟨J, fun i => (e25_mem_adm i (J i)).1 (hJ i), ?_⟩
    funext i
    exact (key J i).2 (hJ0 i)
  · rintro ⟨J, hJ, hu⟩ i
    exact Finset.prod_eq_zero ((e25_mem_adm i (J i)).2 (hJ i)) ((key J i).1 (congrFun hu i))

lemma e25_AleB (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∀ ua ∈ setA p d lam, ∀ ub ∈ setB p d lam, ua ≤ ub := by
  intro ua hA ub hB
  by_contra hcon
  simp only [Pi.le_def, not_forall, not_le] at hcon
  obtain ⟨i0, hi0⟩ := hcon
  -- w = ua - ub, take a maximizer
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun i => ua i - ub i)
    ⟨i0, Finset.mem_univ _⟩
  have hkpos : 0 < ua k - ub k := lt_of_lt_of_le (by linarith) (hk i0 (Finset.mem_univ _))
  obtain ⟨j, hj, hj0⟩ := Finset.prod_eq_zero_iff.1 (hB k)
  have hjk : k ≤ j := (e25_mem_adm k j).1 hj
  have h1 := hA k j hjk
  rw [e25_Uij_eq] at h1 hj0
  have hsum : ∑ s, p j s * (ua s - ub s) ≤ ∑ s, p j s * (ua k - ub k) :=
    Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hk s (Finset.mem_univ _)) (hp0 j s)
  have hsum2 : ∑ s, p j s * (ua k - ub k) = ua k - ub k := by
    rw [← Finset.sum_mul, hp1 j, one_mul]
  have hsum3 : ∑ s, p j s * (ua s - ub s) = ∑ s, p j s * ua s - ∑ s, p j s * ub s := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun s _ => by ring
  nlinarith

lemma e25_strict (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hirr : ∀ J : Fin (σ + 1) → Fin (σ + 1), IsStrategy J →
      ∀ i k, ∃ n : ℕ, 0 < (stratMatrix p J ^ n) i k)
    (uStar : Fin (σ + 1) → ℝ)
    (huStar : BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam uStar = uStar)
    (u : Fin (σ + 1) → ℝ) (hu : u ∈ setA p d lam) (hne : u ≠ uStar) :
    ∀ i, u i < uStar i := by
  obtain ⟨hA', hB'⟩ := (e25_bellman_iff σ p d hp0 hp1 lam uStar).1 huStar
  have hle : u ≤ uStar := e25_AleB σ p d hp0 hp1 lam hlam0 hlam1 u hu uStar hB'
  obtain ⟨J, hJ, hJu⟩ := (e25_B_iff σ p d hp0 hp1 lam uStar).1 hB'
  have hpol : ∀ i, uStar i = d i (J i) + lam * ∑ s, p (J i) s * uStar s := fun i =>
    (congrFun hJu i).symm
  have hw : ∀ i, 0 ≤ uStar i - u i := fun i => sub_nonneg.2 (hle i)
  -- w i ≥ lam * ∑ p w
  have hstep : ∀ i, lam * ∑ s, p (J i) s * (uStar s - u s) ≤ uStar i - u i := by
    intro i
    have h1 := hu i (J i) (hJ i)
    rw [e25_Uij_eq] at h1
    have h3 : ∑ s, p (J i) s * (uStar s - u s)
        = ∑ s, p (J i) s * uStar s - ∑ s, p (J i) s * u s := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun s _ => by ring
    have := hpol i
    rw [h3]; nlinarith
  -- zero set is closed under P
  have hclosed : ∀ n : ℕ, ∀ k m, uStar k - u k = 0 → 0 < (stratMatrix p J ^ n) k m →
      uStar m - u m = 0 := by
    intro n
    induction n with
    | zero =>
      intro k m hk hpos
      by_cases hkm : k = m
      · subst hkm; exact hk
      · simp [Matrix.one_apply_ne hkm] at hpos
    | succ n ih =>
      intro k m hk hpos
      rw [pow_succ', Matrix.mul_apply] at hpos
      obtain ⟨s, -, hs⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
        (f := fun _ => (0:ℝ)) (g := fun s => stratMatrix p J k s * (stratMatrix p J ^ n) s m)
        (by simpa using hpos)
      have hps : 0 < stratMatrix p J k s := by
        have h0 : 0 ≤ stratMatrix p J k s := hp0 _ _
        rcases h0.lt_or_eq with h | h
        · exact h
        · rw [← h] at hs; simp at hs
      have hpn : 0 < (stratMatrix p J ^ n) s m := by
        by_contra hc
        push_neg at hc
        have := mul_nonpos_of_nonneg_of_nonpos hps.le hc
        linarith
      have hz : ∑ t, p (J k) t * (uStar t - u t) = 0 := by
        have h0 : 0 ≤ ∑ t, p (J k) t * (uStar t - u t) :=
          Finset.sum_nonneg fun t _ => mul_nonneg (hp0 _ _) (hw t)
        have := hstep k
        rw [hk] at this
        nlinarith
      have hz' := (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => mul_nonneg (hp0 (J k) t) (hw t))).1 hz s
        (Finset.mem_univ _)
      have hps' : 0 < p (J k) s := hps
      have hws : uStar s - u s = 0 := by
        rcases mul_eq_zero.1 hz' with h | h
        · linarith
        · exact h
      exact ih s m hws hpn
  intro i
  by_contra hcon
  have hi0 : uStar i - u i = 0 := le_antisymm (by linarith [not_lt.1 hcon]) (hw i)
  apply hne
  funext m
  obtain ⟨n, hn⟩ := hirr J hJ i m
  have := hclosed n i m hi0 hn
  linarith

end DEpenoux.LinearProgram

open DEpenoux.LinearProgram


theorem solution (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hirr : ∀ J : Fin (σ + 1) → Fin (σ + 1), IsStrategy J →
      ∀ i k, ∃ n : ℕ, 0 < (stratMatrix p J ^ n) i k)
    (uStar : Fin (σ + 1) → ℝ)
    (huStar : BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam uStar = uStar)
    (u : Fin (σ + 1) → ℝ) (hu : u ∈ setA p d lam) (hne : u ≠ uStar) :
    ∀ i, u i < uStar i := by
  exact e25_strict σ p d hp0 hp1 lam hlam0 hlam1 hirr uStar huStar u hu hne
