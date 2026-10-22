-- Prove2me | solution 1 for DQI.Imperfect.lemma_10_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:17:43.403083+00:00
-- url     : https://prove2.me/submissions/f8de9283-b17c-4f7d-9959-a315df020812

import Mathlib
import Definitions.Def_DQI_Imperfect_Setting

set_option autoImplicit false
open Finset DQI.Imperfect

lemma mm_zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

lemma mm_sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases mm_zmod2_cases a with rfl | rfl <;> rcases mm_zmod2_cases b with rfl | rfl <;>
    simp [sgn, h11] <;> norm_num

lemma mm_char_sum {n : ℕ} (a : Fin n → ZMod 2) :
    ∑ x : Fin n → ZMod 2, sgn (a ⬝ᵥ x) = if a = 0 then (2:ℝ)^n else 0 := by
  classical
  by_cases ha : a = 0
  · subst ha
    simp [sgn, Fintype.card_fun, ZMod.card]
  · rw [if_neg ha]
    obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
      by_contra h; push Not at h; exact ha (funext h)
    set e : Fin n → ZMod 2 := Pi.single j 1 with he
    have h1 : ∑ x : Fin n → ZMod 2, sgn (a ⬝ᵥ x) = ∑ x : Fin n → ZMod 2, sgn (a ⬝ᵥ (x + e)) :=
      (Fintype.sum_equiv (Equiv.addRight e) (fun x => sgn (a ⬝ᵥ (x + e))) (fun x => sgn (a ⬝ᵥ x))
        (fun x => by simp [Equiv.coe_addRight])).symm
    have h2 : ∀ x : Fin n → ZMod 2, sgn (a ⬝ᵥ (x + e)) = - sgn (a ⬝ᵥ x) := by
      intro x
      rw [dotProduct_add, mm_sgn_add, he, dotProduct_single, mul_one]
      have : sgn (a j) = -1 := by simp [sgn, hj]
      rw [this]; ring
    simp_rw [h2] at h1
    rw [Finset.sum_neg_distrib] at h1
    linarith

lemma mm_had_sq {n : ℕ} (ψ : (Fin n → ZMod 2) → ℝ) (x : Fin n → ZMod 2) :
    hadamard ψ x ^ 2 = (1 / (2:ℝ)^n) * ∑ s, ∑ s', sgn ((s + s') ⬝ᵥ x) * (ψ s * ψ s') := by
  unfold hadamard
  rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (by positivity), sq, Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun s' _ => ?_))
  rw [add_dotProduct, mm_sgn_add]; ring

lemma mm_had_sgn {n : ℕ} (ψ : (Fin n → ZMod 2) → ℝ) (b : Fin n → ZMod 2) :
    ∑ x, hadamard ψ x ^ 2 * sgn (b ⬝ᵥ x) =
      ∑ s, ∑ s', if s + s' + b = 0 then ψ s * ψ s' else 0 := by
  have h1 : ∀ x : Fin n → ZMod 2, hadamard ψ x ^ 2 * sgn (b ⬝ᵥ x) =
      (1 / (2:ℝ)^n) * ∑ s, ∑ s', (ψ s * ψ s') * sgn ((s + s' + b) ⬝ᵥ x) := by
    intro x
    rw [mm_had_sq, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun s' _ => ?_)
    simp only [add_dotProduct, mm_sgn_add]; ring
  simp_rw [h1]
  rw [← Finset.mul_sum]
  have h3 : ∑ x : Fin n → ZMod 2, ∑ s, ∑ s', (ψ s * ψ s') * sgn ((s + s' + b) ⬝ᵥ x)
      = ∑ s, ∑ s', ∑ x : Fin n → ZMod 2, (ψ s * ψ s') * sgn ((s + s' + b) ⬝ᵥ x) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun s _ => Finset.sum_comm)
  rw [h3, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s' _ => ?_)
  rw [← Finset.mul_sum, mm_char_sum]
  split_ifs
  · field_simp
  · simp

lemma mm_add_eq_zero {n : ℕ} (s s' : Fin n → ZMod 2) : s + s' = 0 ↔ s = s' := by
  constructor
  · intro h
    funext i
    have := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply] at this
    revert this
    generalize s i = a; generalize s' i = b
    revert a b; decide
  · rintro rfl
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize s i = a
    revert a; decide

lemma mm_parseval {n : ℕ} (ψ : (Fin n → ZMod 2) → ℝ) :
    ∑ x, hadamard ψ x ^ 2 = ∑ s, ψ s ^ 2 := by
  have h := mm_had_sgn ψ 0
  simp only [zero_dotProduct, add_zero] at h
  have h0 : sgn (0 : ZMod 2) = 1 := by simp [sgn]
  simp only [h0, mul_one] at h
  rw [h]
  simp_rw [mm_add_eq_zero]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.sum_ite_eq]
  simp [sq]

lemma mm_collapse {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] (σ : ι → κ) (c : ι → ℝ)
    (ψ : κ → ℝ) (hψ : ∀ s, ψ s = ∑ p, if σ p = s then c p else 0) (F : κ → ℝ) :
    ∑ s, F s * ψ s = ∑ p, c p * F (σ p) := by
  simp_rw [hψ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp [mul_ite, mul_comm]

lemma mm_quad {n : ℕ} {ι : Type*} [Fintype ι] (σ : ι → (Fin n → ZMod 2)) (c : ι → ℝ)
    (ψ : (Fin n → ZMod 2) → ℝ) (hψ : ∀ s, ψ s = ∑ p, if σ p = s then c p else 0)
    (b : Fin n → ZMod 2) :
    ∑ s, ∑ s', (if s + s' + b = 0 then ψ s * ψ s' else 0) =
      ∑ p, ∑ q, if σ p + σ q + b = 0 then c p * c q else 0 := by
  classical
  have h1 : ∀ s : Fin n → ZMod 2, ∑ s', (if s + s' + b = 0 then ψ s * ψ s' else 0)
      = ∑ q, c q * (if s + σ q + b = 0 then ψ s else 0) := by
    intro s
    have := mm_collapse σ c ψ hψ (fun s' => if s + s' + b = 0 then ψ s else 0)
    rw [← this]
    refine Finset.sum_congr rfl (fun s' _ => ?_)
    split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  have := mm_collapse σ c ψ hψ (fun s => if s + σ q + b = 0 then (1:ℝ) else 0)
  simp_rw [← Finset.mul_sum]
  have h2 : ∑ s, (if s + σ q + b = 0 then ψ s else 0) = ∑ p, c p * (if σ p + σ q + b = 0 then (1:ℝ) else 0) := by
    rw [← this]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs <;> simp
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs <;> simp [mul_comm]

/-- generic state with index family `G`. -/
noncomputable def mmPt {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin m → ZMod 2)
    (G : ℕ → Finset (Fin m → ZMod 2)) (ℓ : ℕ) (w : Fin (ℓ + 1) → ℝ)
    (s : Fin n → ZMod 2) : ℝ :=
  ∑ k : Fin (ℓ + 1),
    (w k / Real.sqrt (Nat.choose m k.val : ℝ)) *
      ∑ y ∈ (G k.val).filter (fun y => B.transpose.mulVec y = s),
        sgn (v ⬝ᵥ y)

/-- generic matrix with index family `G`. -/
noncomputable def mmAbar {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin m → ZMod 2)
    (G : ℕ → Finset (Fin m → ZMod 2)) (ℓ : ℕ) :
    Matrix (Fin (ℓ + 1)) (Fin (ℓ + 1)) ℝ :=
  fun k k' =>
    (1 / Real.sqrt ((Nat.choose m k.val : ℝ) * (Nat.choose m k'.val : ℝ))) *
      ∑ i : Fin m,
        ∑ yy ∈ ((G k.val) ×ˢ (G k'.val)).filter
            (fun yy => B.transpose.mulVec (yy.1 + yy.2 + Pi.single i 1) = 0),
          sgn (v i + v ⬝ᵥ (yy.1 + yy.2))

lemma mm_obj_expand {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin m → ZMod 2)
    (x : Fin n → ZMod 2) :
    obj B v x = ∑ i, sgn (v i) * sgn ((B.transpose.mulVec (Pi.single i 1)) ⬝ᵥ x) := by
  unfold obj
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [add_comm, mm_sgn_add]
  congr 2
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, single_dotProduct, one_mul]

lemma mm_reorder {α β γ β' δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype β'] [Fintype δ]
    (T : α → β → γ → β' → δ → ℝ) :
    ∑ i, ∑ k, ∑ y, ∑ k', ∑ y', T i k y k' y' = ∑ k, ∑ k', ∑ i, ∑ y, ∑ y', T i k y k' y' := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  calc ∑ i, ∑ y, ∑ k', ∑ y', T i k y k' y' = ∑ i, ∑ k', ∑ y, ∑ y', T i k y k' y' :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ k', ∑ i, ∑ y, ∑ y', T i k y k' y' := Finset.sum_comm

lemma mm_sum_pairs {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2)) (Gk Gk' : Finset (Fin m → ZMod 2))
    (i : Fin m) (f : (Fin m → ZMod 2) → (Fin m → ZMod 2) → ℝ) :
    ∑ yy ∈ (Gk ×ˢ Gk').filter (fun yy => B.transpose.mulVec (yy.1 + yy.2 + Pi.single i 1) = 0),
        f yy.1 yy.2 =
      ∑ y, ∑ y', if (y ∈ Gk ∧ y' ∈ Gk' ∧ B.transpose.mulVec (y + y' + Pi.single i 1) = 0)
        then f y y' else 0 := by
  classical
  have : (Gk ×ˢ Gk').filter (fun yy => B.transpose.mulVec (yy.1 + yy.2 + Pi.single i 1) = 0) =
      Finset.univ.filter (fun yy : (Fin m → ZMod 2) × (Fin m → ZMod 2) =>
        yy.1 ∈ Gk ∧ yy.2 ∈ Gk' ∧ B.transpose.mulVec (yy.1 + yy.2 + Pi.single i 1) = 0) := by
    ext yy; simp [Finset.mem_product, and_assoc]
  rw [this, Finset.sum_filter, Fintype.sum_prod_type]

lemma mm_core {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin m → ZMod 2)
    (G : ℕ → Finset (Fin m → ZMod 2)) (ℓ : ℕ) (w : Fin (ℓ + 1) → ℝ) :
    ∑ x, hadamard (mmPt B v G ℓ w) x ^ 2 * obj B v x = w ⬝ᵥ (mmAbar B v G ℓ).mulVec w := by
  classical
  set a : Fin (ℓ + 1) → ℝ := fun k => w k / Real.sqrt (Nat.choose m k.val : ℝ) with ha
  set c : Fin (ℓ + 1) × (Fin m → ZMod 2) → ℝ :=
    fun p => if p.2 ∈ G p.1.val then a p.1 * sgn (v ⬝ᵥ p.2) else 0 with hc
  have hψ : ∀ s, mmPt B v G ℓ w s = ∑ p : Fin (ℓ + 1) × (Fin m → ZMod 2),
      if B.transpose.mulVec p.2 = s then c p else 0 := by
    intro s
    unfold mmPt
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum, Finset.sum_filter]
    have : ∀ y : Fin m → ZMod 2, (if B.transpose.mulVec (k, y).2 = s then c (k, y) else 0) =
        if y ∈ G k.val then (if B.transpose.mulVec y = s then a k * sgn (v ⬝ᵥ y) else 0) else 0 := by
      intro y
      simp only [hc]
      split_ifs <;> simp
    simp_rw [this]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hL : ∑ x, hadamard (mmPt B v G ℓ w) x ^ 2 * obj B v x
      = ∑ i, sgn (v i) * ∑ x, hadamard (mmPt B v G ℓ w) x ^ 2 *
          sgn ((B.transpose.mulVec (Pi.single i 1)) ⬝ᵥ x) := by
    simp_rw [mm_obj_expand, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring
  rw [hL]
  simp_rw [mm_had_sgn, mm_quad _ c _ hψ]
  -- target normal form
  let T : Fin m → Fin (ℓ + 1) → (Fin m → ZMod 2) → Fin (ℓ + 1) → (Fin m → ZMod 2) → ℝ :=
    fun i k y k' y' => if (y ∈ G k.val ∧ y' ∈ G k'.val ∧
        B.transpose.mulVec (y + y' + Pi.single i 1) = 0)
      then a k * a k' * sgn (v i + v ⬝ᵥ (y + y')) else 0
  have hLd : (∑ i, sgn (v i) * ∑ p, ∑ q, if B.transpose.mulVec p.2 + B.transpose.mulVec q.2 +
        B.transpose.mulVec (Pi.single i 1) = 0 then c p * c q else 0)
      = ∑ i, ∑ k, ∑ y, ∑ k', ∑ y', T i k y k' y' := by
    simp only [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ =>
      Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun k' _ =>
        Finset.sum_congr rfl (fun y' _ => ?_)))))
    have hlin : B.transpose.mulVec (y + y' + Pi.single i 1) =
        B.transpose.mulVec y + B.transpose.mulVec y' + B.transpose.mulVec (Pi.single i 1) := by
      simp [Matrix.mulVec_add]
    have hs : sgn (v i + v ⬝ᵥ (y + y')) = sgn (v i) * sgn (v ⬝ᵥ y) * sgn (v ⬝ᵥ y') := by
      rw [dotProduct_add, mm_sgn_add, mm_sgn_add]; ring
    simp only [T, hc]
    rw [← hlin, hs]
    by_cases h1 : y ∈ G k.val <;> by_cases h2 : y' ∈ G k'.val <;>
      by_cases h3 : B.transpose.mulVec (y + y' + Pi.single i 1) = 0 <;> simp [h1, h2, h3] <;> ring
  have hR : w ⬝ᵥ (mmAbar B v G ℓ).mulVec w = ∑ k, ∑ k', ∑ i, ∑ y, ∑ y', T i k y k' y' := by
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k' _ => ?_)
    have hT : ∀ i y y', T i k y k' y' = a k * a k' *
        (if (y ∈ G k.val ∧ y' ∈ G k'.val ∧ B.transpose.mulVec (y + y' + Pi.single i 1) = 0)
          then sgn (v i + v ⬝ᵥ (y + y')) else 0) := by
      intro i y y'
      simp only [T]
      split_ifs <;> simp
    simp_rw [hT, ← Finset.mul_sum]
    have hp : ∀ i : Fin m, ∑ yy ∈ ((G k.val) ×ˢ (G k'.val)).filter
            (fun yy => B.transpose.mulVec (yy.1 + yy.2 + Pi.single i 1) = 0),
          sgn (v i + v ⬝ᵥ (yy.1 + yy.2)) = ∑ y, ∑ y', if (y ∈ G k.val ∧ y' ∈ G k'.val ∧
            B.transpose.mulVec (y + y' + Pi.single i 1) = 0)
          then sgn (v i + v ⬝ᵥ (y + y')) else 0 :=
      fun i => mm_sum_pairs B (G k.val) (G k'.val) i (fun y y' => sgn (v i + v ⬝ᵥ (y + y')))
    simp only [mmAbar, hp]
    rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    simp only [ha]
    ring
  rw [hLd, mm_reorder, hR]

lemma mm_shell_card (m k : ℕ) : (shell m k).card = Nat.choose m k := by
  classical
  have : (shell m k).card = (Finset.powersetCard k (Finset.univ : Finset (Fin m))).card := by
    refine Finset.card_nbij' (fun y => Finset.univ.filter (fun i => y i ≠ 0))
      (fun S => fun i => if i ∈ S then 1 else 0) ?_ ?_ ?_ ?_
    · intro y hy
      rw [Finset.mem_coe] at hy
      rw [Finset.mem_coe]
      have hy' : wt y = k := by
        simpa [shell] using hy
      simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
      exact hy'
    · intro S hS
      rw [Finset.mem_coe, Finset.mem_powersetCard] at hS
      rw [Finset.mem_coe]
      have : (Finset.univ.filter (fun i : Fin m => (if i ∈ S then (1 : ZMod 2) else 0) ≠ 0)) = S := by
        ext i; simp
      show _ ∈ shell m k
      unfold shell
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show wt _ = k
      unfold wt
      rw [this]; exact hS.2
    · intro y hy
      funext i
      by_cases h : y i = 0
      · simp [h]
      · have : y i = 1 := by
          revert h; generalize y i = a; revert a; decide
        simp [h, this]
    · intro S hS
      ext i; simp
  rw [this, Finset.card_powersetCard]; simp

lemma mm_sq_sum {ι κ : Type*} [Fintype κ] [DecidableEq κ] (T : Finset ι) (f : ι → κ) (a : ι → ℝ)
    (hf : Set.InjOn f T) :
    ∑ s : κ, (∑ i ∈ T, if f i = s then a i else 0) ^ 2 = ∑ i ∈ T, a i ^ 2 := by
  classical
  have h1 : ∀ s : κ, (∑ i ∈ T, if f i = s then a i else 0) ^ 2
      = ∑ i ∈ T, ∑ j ∈ T, (if f i = s then a i else 0) * (if f j = s then a j else 0) := by
    intro s; rw [sq, Finset.sum_mul_sum]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single i]
  · simp [sq]
  · intro j hj hji
    refine Finset.sum_eq_zero (fun s _ => ?_)
    by_cases h : f j = s
    · by_cases h' : f i = s
      · exact absurd (hf hj hi (h.trans h'.symm)) hji
      · simp [h']
    · simp [h]
  · intro h; exact absurd hi h

lemma mm_sgn_sq (a : ZMod 2) : sgn a ^ 2 = 1 := by
  unfold sgn; split_ifs <;> norm_num


lemma mm_norm (m n ℓ : ℕ) (hℓ : ℓ ≤ m)
    (B : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin m → ZMod 2) (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (w : Fin (ℓ + 1) → ℝ) :
    (∑ s, (PtD B v dec ℓ w s) ^ 2) =
        (∑ k, (w k) ^ 2 * (1 - epsk B dec k.val)) := by
  classical
  have hcard : ∀ k : Fin (ℓ + 1), ((Dset B dec k.val).card : ℝ) + (Fset B dec k.val).card = (Nat.choose m k.val : ℝ) := by
    intro k
    have : (Dset B dec k.val).card + (Fset B dec k.val).card = Nat.choose m k.val := by
      rw [← mm_shell_card]
      exact Finset.card_filter_add_card_filter_not _
    exact_mod_cast this
  have hpos : ∀ k : Fin (ℓ + 1), (0 : ℝ) < (Nat.choose m k.val : ℝ) := by
    intro k
    exact_mod_cast Nat.choose_pos (by omega)
  have key : ∀ k : Fin (ℓ + 1), (w k) ^ 2 * (1 - epsk B dec k.val)
      = ∑ y ∈ Dset B dec k.val, (w k / Real.sqrt (Nat.choose m k.val : ℝ) * sgn (v ⬝ᵥ y)) ^ 2 := by
    intro k
    have hC := hpos k
    have h2 := hcard k
    simp_rw [mul_pow, mul_comm _ (sgn _ ^ 2), mm_sgn_sq, one_mul]
    rw [Finset.sum_const, nsmul_eq_mul, div_pow, Real.sq_sqrt hC.le]
    unfold epsk
    have hD : ((Dset B dec k.val).card : ℝ) = (Nat.choose m k.val : ℝ) - (Fset B dec k.val).card := by linarith
    rw [hD]
    field_simp
  set T : Finset (Fin (ℓ + 1) × (Fin m → ZMod 2)) :=
    Finset.univ.filter (fun p => p.2 ∈ Dset B dec p.1.val) with hT
  have hPt : ∀ s, PtD B v dec ℓ w s = ∑ p ∈ T, if B.transpose.mulVec p.2 = s
      then w p.1 / Real.sqrt (Nat.choose m p.1.val : ℝ) * sgn (v ⬝ᵥ p.2) else 0 := by
    intro s
    unfold PtD
    rw [hT, Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    dsimp only
    simp only [Finset.sum_ite_mem, Finset.univ_inter]
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    split_ifs <;> simp
  have hinj : Set.InjOn (fun p : Fin (ℓ + 1) × (Fin m → ZMod 2) => B.transpose.mulVec p.2) T := by
    intro p hp q hq hpq
    simp only [hT, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp hq
    have h1 : dec (B.transpose.mulVec p.2) = p.2 := (Finset.mem_filter.1 hp).2
    have h2 : dec (B.transpose.mulVec q.2) = q.2 := (Finset.mem_filter.1 hq).2
    have h3 : p.2 = q.2 := by rw [← h1, ← h2]; exact congrArg dec hpq
    have h4 : wt p.2 = p.1.val := by simpa [shell] using (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2
    have h5 : wt q.2 = q.1.val := by simpa [shell] using (Finset.mem_filter.1 (Finset.mem_filter.1 hq).1).2
    refine Prod.ext (Fin.ext ?_) h3
    rw [← h4, ← h5, h3]
  simp_rw [hPt]
  rw [mm_sq_sum T _ _ hinj]
  simp_rw [key]
  rw [hT, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  dsimp only
  simp only [Finset.sum_ite_mem, Finset.univ_inter]

lemma mm_vsum {m : ℕ} (i : Fin m) (z : Fin m → ZMod 2) :
    ∑ v : Fin m → ZMod 2, sgn (v i + v ⬝ᵥ z) = if z + Pi.single i 1 = 0 then (2:ℝ)^m else 0 := by
  rw [← mm_char_sum (z + Pi.single i 1)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  congr 1
  rw [dotProduct_comm (z + Pi.single i 1) v, dotProduct_add, dotProduct_single, mul_one, add_comm]

lemma mm_avg {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2)) (G : ℕ → Finset (Fin m → ZMod 2))
    (ℓ : ℕ) (k k' : Fin (ℓ + 1)) :
    (1 / (2:ℝ)^m) * ∑ v, mmAbar B v G ℓ k k' =
    (1 / Real.sqrt ((Nat.choose m k.val : ℝ) * (Nat.choose m k'.val : ℝ))) *
      ∑ i : Fin m, ((((G k.val) ×ˢ (G k'.val)).filter
        (fun yy => yy.1 + yy.2 + Pi.single i 1 = 0)).card : ℝ) := by
  classical
  simp only [mmAbar]
  rw [← Finset.mul_sum, mul_left_comm]
  congr 1
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  have h1 : ∀ yy : (Fin m → ZMod 2) × (Fin m → ZMod 2),
      ∑ v : Fin m → ZMod 2, sgn (v i + v ⬝ᵥ (yy.1 + yy.2)) =
        (2:ℝ)^m * (if yy.1 + yy.2 + Pi.single i 1 = 0 then 1 else 0) := by
    intro yy
    rw [mm_vsum]; split_ifs <;> simp
  simp_rw [h1]
  rw [← Finset.mul_sum, Finset.sum_boole]
  have hm : (2:ℝ)^m ≠ 0 := by positivity
  rw [← mul_assoc, one_div, inv_mul_cancel₀ hm, one_mul]
  congr 2
  ext yy
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    refine ⟨⟨h1, ?_⟩, h3⟩
    rw [h3]; simp

lemma mm_wt_add_single {m : ℕ} (y : Fin m → ZMod 2) (i : Fin m) :
    (y i = 0 → wt (y + Pi.single i 1) = wt y + 1) ∧ (y i ≠ 0 → wt (y + Pi.single i 1) + 1 = wt y) := by
  classical
  have key : ∀ j, (y + (Pi.single i 1 : Fin m → ZMod 2)) j ≠ 0 ↔ (if j = i then y i = 0 else y j ≠ 0) := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, Pi.single_eq_same, if_true]
      rcases mm_zmod2_cases (y j) with h | h <;> simp [h]
      decide
    · simp [hj]
  constructor
  · intro h
    unfold wt
    have : Finset.univ.filter (fun j => (y + (Pi.single i 1 : Fin m → ZMod 2)) j ≠ 0) =
        insert i (Finset.univ.filter (fun j => y j ≠ 0)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, key]
      by_cases hj : j = i
      · subst hj; simp [h]
      · simp [hj]
    rw [this, Finset.card_insert_of_notMem]
    simp [h]
  · intro h
    unfold wt
    have : Finset.univ.filter (fun j => y j ≠ 0) =
        insert i (Finset.univ.filter (fun j => (y + (Pi.single i 1 : Fin m → ZMod 2)) j ≠ 0)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, key]
      by_cases hj : j = i
      · subst hj; simp [h]
      · simp [hj]
    rw [this, Finset.card_insert_of_notMem]
    have h1 : y i = 1 := (mm_zmod2_cases _).resolve_left h
    have h11 : (1:ZMod 2) + 1 = 0 := by decide
    simp [h1, h11]

lemma mm_card_pairs {m : ℕ} (A Bs : Finset (Fin m → ZMod 2)) (i : Fin m) :
    ((A ×ˢ Bs).filter (fun yy => yy.1 + yy.2 + Pi.single i 1 = 0)).card
      = (A.filter (fun y => y + (Pi.single i 1 : Fin m → ZMod 2) ∈ Bs)).card := by
  classical
  have key : ∀ y y' : Fin m → ZMod 2, y + y' + (Pi.single i 1 : Fin m → ZMod 2) = 0 ↔
      y' = y + Pi.single i 1 := by
    intro y y'
    have h3 : ∀ a b c : ZMod 2, a + b + c = 0 ↔ b = a + c := by decide
    constructor
    · intro h; funext j
      have := congrFun h j
      simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
      exact (h3 _ _ _).1 this
    · intro h; funext j
      have := congrFun h j
      simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
      exact (h3 _ _ _).2 this
  refine Finset.card_nbij' (fun yy => yy.1) (fun y => (y, y + Pi.single i 1)) ?_ ?_ ?_ ?_
  · intro yy hyy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hyy ⊢
    refine ⟨hyy.1.1, ?_⟩
    rw [(key _ _).1 hyy.2] at hyy; exact hyy.1.2
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hy ⊢
    exact ⟨⟨hy.1, hy.2⟩, (key _ _).2 rfl⟩
  · intro yy hyy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hyy
    exact Prod.ext rfl ((key _ _).1 hyy.2).symm
  · intro y hy; rfl

lemma mm_count_y {m : ℕ} (k k' : ℕ) (y : Fin m → ZMod 2) (hy : wt y = k) :
    ∑ i : Fin m, (if y + (Pi.single i 1 : Fin m → ZMod 2) ∈ shell m k' then 1 else 0 : ℕ)
      = (if k' = k + 1 then m - k else 0) + (if k = k' + 1 then k else 0) := by
  classical
  have hz : (Finset.univ.filter (fun i => y i = 0)).card = m - k := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun i => y i = 0)
    have h2 : (Finset.univ.filter (fun i => ¬ y i = 0)).card = k := hy
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  have step : ∀ i : Fin m, (if y + (Pi.single i 1 : Fin m → ZMod 2) ∈ shell m k' then 1 else 0 : ℕ) =
      (if y i = 0 ∧ k' = k + 1 then 1 else 0) + (if y i ≠ 0 ∧ k = k' + 1 then 1 else 0) := by
    intro i
    obtain ⟨h1, h2⟩ := mm_wt_add_single y i
    have hmem : y + (Pi.single i 1 : Fin m → ZMod 2) ∈ shell m k' ↔ wt (y + Pi.single i 1) = k' := by
      simp [shell]
    by_cases h : y i = 0
    · have := h1 h
      rw [if_congr hmem rfl rfl]
      by_cases hk : k' = k + 1
      · simp [h, hk, this, hy]
      · have : ¬ wt (y + (Pi.single i 1 : Fin m → ZMod 2)) = k' := by omega
        simp [h, hk, this]
    · have := h2 h
      rw [if_congr hmem rfl rfl]
      by_cases hk : k = k' + 1
      · have : wt (y + (Pi.single i 1 : Fin m → ZMod 2)) = k' := by omega
        simp [h, hk, this]
      · have : ¬ wt (y + (Pi.single i 1 : Fin m → ZMod 2)) = k' := by omega
        simp [h, hk, this]
  simp_rw [step]
  rw [Finset.sum_add_distrib]
  have e1 : ∑ i : Fin m, (if y i = 0 ∧ k' = k + 1 then 1 else 0 : ℕ) =
      if k' = k + 1 then m - k else 0 := by
    by_cases hk : k' = k + 1
    · simp only [hk, and_true, if_true]
      rw [Finset.sum_boole, hz]; simp
    · simp [hk]
  have e2 : ∑ i : Fin m, (if y i ≠ 0 ∧ k = k' + 1 then 1 else 0 : ℕ) =
      if k = k' + 1 then k else 0 := by
    by_cases hk : k = k' + 1
    · simp only [hk, and_true, if_true]
      rw [Finset.sum_boole]
      have h2 : (Finset.univ.filter (fun i => y i ≠ 0)).card = k := hy
      rw [← hk] at *
      simp [h2]
    · simp [hk]
  rw [e1, e2]

lemma mm_shell_total {m : ℕ} (k k' : ℕ) :
    ∑ i : Fin m, (((shell m k ×ˢ shell m k').filter
        (fun yy => yy.1 + yy.2 + (Pi.single i 1 : Fin m → ZMod 2) = 0)).card)
      = Nat.choose m k * ((if k' = k + 1 then m - k else 0) + (if k = k' + 1 then k else 0)) := by
  classical
  simp_rw [mm_card_pairs, Finset.card_filter]
  rw [Finset.sum_comm]
  have : ∀ y ∈ shell m k, ∑ i : Fin m, (if y + (Pi.single i 1 : Fin m → ZMod 2) ∈ shell m k' then 1 else 0 : ℕ)
      = (if k' = k + 1 then m - k else 0) + (if k = k' + 1 then k else 0) := by
    intro y hy
    exact mm_count_y k k' y (by simpa [shell] using hy)
  rw [Finset.sum_congr rfl this, Finset.sum_const, mm_shell_card, smul_eq_mul]

lemma mm_hrel (m j : ℕ) (hj : j + 1 ≤ m) :
    (Nat.choose m (j + 1) : ℝ) * ((j : ℝ) + 1) = (Nat.choose m j : ℝ) * ((m : ℝ) - j) := by
  have := Nat.choose_succ_right_eq m j
  have h2 : (Nat.choose m (j + 1) : ℝ) * ((j : ℝ) + 1) = (Nat.choose m j : ℝ) * ((m - j : ℕ) : ℝ) := by
    exact_mod_cast this
  rw [h2, Nat.cast_sub (by omega)]

lemma mm_ratio (m j : ℕ) (hj : j + 1 ≤ m) :
    ((Nat.choose m j : ℝ) * ((m : ℝ) - j)) / Real.sqrt ((Nat.choose m j : ℝ) * (Nat.choose m (j + 1) : ℝ))
      = Real.sqrt (((j : ℝ) + 1) * ((m : ℝ) - j)) := by
  have hC : (0 : ℝ) < (Nat.choose m j : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hC' : (0 : ℝ) < (Nat.choose m (j + 1) : ℝ) := by exact_mod_cast Nat.choose_pos hj
  have ha : (0 : ℝ) < (m : ℝ) - j := by
    have : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
    linarith
  have hb : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hrel := mm_hrel m j hj
  have hs : Real.sqrt ((Nat.choose m j : ℝ) * (Nat.choose m (j + 1) : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos hC hC')).ne'
  rw [div_eq_iff hs, ← Real.sqrt_mul (by positivity)]
  have : ((j : ℝ) + 1) * ((m : ℝ) - j) * ((Nat.choose m j : ℝ) * (Nat.choose m (j + 1) : ℝ)) =
      ((Nat.choose m j : ℝ) * ((m : ℝ) - j)) ^ 2 := by
    have : ((Nat.choose m j : ℝ) * ((m : ℝ) - j)) ^ 2 =
        ((Nat.choose m j : ℝ) * ((m : ℝ) - j)) * ((Nat.choose m (j + 1) : ℝ) * ((j : ℝ) + 1)) := by
      rw [hrel]; ring
    rw [this]; ring
  rw [this, Real.sqrt_sq (by positivity)]

lemma mm_avg_shell {m ℓ : ℕ} (hℓ : ℓ ≤ m) (k k' : Fin (ℓ + 1)) :
    (1 / Real.sqrt ((Nat.choose m k.val : ℝ) * (Nat.choose m k'.val : ℝ))) *
      ((∑ i : Fin m, ((shell m k.val ×ˢ shell m k'.val).filter
        (fun yy => yy.1 + yy.2 + (Pi.single i 1 : Fin m → ZMod 2) = 0)).card : ℕ) : ℝ)
      = DQI.Semicircle.Atri m ℓ 0 k k' := by
  classical
  rw [mm_shell_total]
  have hk := k.2; have hk' := k'.2
  unfold DQI.Semicircle.Atri
  by_cases h1 : (k : ℕ) = k'
  · have h2 : ¬ (k' : ℕ) = k + 1 := by omega
    have h3 : ¬ (k : ℕ) = k' + 1 := by omega
    rw [if_pos h1, if_neg h2, if_neg h3]
    simp
  · by_cases h2 : (k' : ℕ) = k + 1
    · have h3 : ¬ (k : ℕ) = k' + 1 := by omega
      rw [if_neg h1, if_pos h2, if_neg h3, if_pos h2]
      rw [h2]
      push_cast [Nat.cast_sub (show (k:ℕ) ≤ m by omega)]
      rw [← mm_ratio m k (by omega)]
      ring
    · by_cases h3 : (k : ℕ) = k' + 1
      · rw [if_neg h1, if_neg h2, if_pos h3, if_neg h2, if_pos h3]
        rw [h3]
        push_cast
        have hj : (k' : ℕ) + 1 ≤ m := by omega
        have hs : Real.sqrt ((Nat.choose m ((k' : ℕ) + 1) : ℝ) * (Nat.choose m k' : ℝ)) =
            Real.sqrt ((Nat.choose m k' : ℝ) * (Nat.choose m ((k' : ℕ) + 1) : ℝ)) := by rw [mul_comm]
        rw [hs, ← mm_ratio m k' hj]
        have := mm_hrel m k' hj
        rw [← this]
        ring
      · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h2, if_neg h3]
        simp

lemma mm_split {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (k k' : ℕ) (i : Fin m) :
    (((shell m k) ×ˢ (shell m k')).filter
        (fun yy => yy.1 + yy.2 + (Pi.single i 1 : Fin m → ZMod 2) = 0)).card =
      (((Dset B dec k) ×ˢ (Dset B dec k')).filter
        (fun yy => yy.1 + yy.2 + (Pi.single i 1 : Fin m → ZMod 2) = 0)).card +
      (((((shell m k) ×ˢ (Fset B dec k')) ∪ ((Fset B dec k) ×ˢ (shell m k'))).filter
        (fun yy => yy.1 + yy.2 + (Pi.single i 1 : Fin m → ZMod 2) = 0))).card := by
  classical
  have hsplit : (shell m k) ×ˢ (shell m k') = ((Dset B dec k) ×ˢ (Dset B dec k')) ∪
      (((shell m k) ×ˢ (Fset B dec k')) ∪ ((Fset B dec k) ×ˢ (shell m k'))) := by
    ext yy
    simp only [Finset.mem_product, Finset.mem_union, Dset, Fset, Finset.mem_filter]
    by_cases h1 : dec (B.transpose.mulVec yy.1) = yy.1 <;> by_cases h2 : dec (B.transpose.mulVec yy.2) = yy.2 <;>
      simp [h1, h2]
  have hdisj : Disjoint ((Dset B dec k) ×ˢ (Dset B dec k'))
      (((shell m k) ×ˢ (Fset B dec k')) ∪ ((Fset B dec k) ×ˢ (shell m k'))) := by
    rw [Finset.disjoint_left]
    intro yy h1 h2
    simp only [Finset.mem_product, Finset.mem_union, Dset, Fset, Finset.mem_filter] at h1 h2
    rcases h2 with h2 | h2
    · exact h2.2.2 h1.2.2
    · exact h2.1.2 h1.1.2
  conv_lhs => rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]

theorem solution (m n ℓ : ℕ) (hℓ : ℓ ≤ m)
    (B : Matrix (Fin m) (Fin n) (ZMod 2)) (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) :
    ((1 / ((2 : ℝ) ^ m)) •
      (∑ v : Fin m → ZMod 2, AbarD B v dec ℓ)) =
      DQI.Semicircle.Atri m ℓ 0 - Emat B dec ℓ := by
  ext k k'
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Matrix.sub_apply]
  have h := mm_avg B (fun k => Dset B dec k) ℓ k k'
  have h2 := mm_avg_shell hℓ k k'
  rw [← h2]
  have e1 : (∑ i : Fin m, ((shell m k.val ×ˢ shell m k'.val).filter
        (fun yy => yy.1 + yy.2 + (Pi.single i 1 : Fin m → ZMod 2) = 0)).card : ℕ) =
      (∑ i : Fin m, (((Dset B dec k.val) ×ˢ (Dset B dec k'.val)).filter
        (fun yy => yy.1 + yy.2 + (Pi.single i 1 : Fin m → ZMod 2) = 0)).card) +
      ∑ i : Fin m, (((((shell m k.val) ×ˢ (Fset B dec k'.val)) ∪ ((Fset B dec k.val) ×ˢ (shell m k'.val))).filter
        (fun yy => yy.1 + yy.2 + (Pi.single i 1 : Fin m → ZMod 2) = 0))).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => mm_split B dec k.val k'.val i)
  rw [e1, Nat.cast_add, mul_add]
  show (1 / (2:ℝ)^m) * ∑ v, mmAbar B v (fun k => Dset B dec k) ℓ k k' = _
  rw [h]
  simp only [Nat.cast_sum, Emat]
  ring
