-- Prove2me | solution 1 for Disjunctive.IntroDuality.disjunctive_duality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:31:03.86627+00:00
-- url     : https://prove2.me/submissions/96efbe67-0b09-426a-b65c-831e44bbc3ca

import Mathlib
import Definitions.Def_Disjunctive_IntroDuality_PolyhedralSystems
import Definitions.Def_Disjunctive_IntroDuality_RegularityCondition
import Definitions.Def_Disjunctive_IntroDuality_OptimalValue

set_option autoImplicit false

namespace DJ824

open Matrix

lemma exists_between_fin {ι : Type} (s r : Finset ι) (L U : ι → ℝ)
    (h : ∀ q ∈ s, ∀ p ∈ r, L q ≤ U p) :
    ∃ t : ℝ, (∀ q ∈ s, L q ≤ t) ∧ ∀ p ∈ r, t ≤ U p := by
  by_cases hs : s.Nonempty
  · refine ⟨s.sup' hs L, fun q hq => Finset.le_sup' L hq, fun p hp => ?_⟩
    exact Finset.sup'_le hs L (fun q hq => h q hq p hp)
  · by_cases hr : r.Nonempty
    · exact ⟨r.inf' hr U, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => Finset.inf'_le U hp⟩
    · exact ⟨0, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => absurd ⟨p, hp⟩ hr⟩

/-- Theorem of alternatives (Fourier–Motzkin), variables indexed by `Fin n`. -/
theorem fm_alt (n : ℕ) : ∀ {ι : Type} [Fintype ι] (a : ι → Fin n → ℝ) (b : ι → ℝ),
    (∃ x : Fin n → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i) ∨
    (∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, ∑ i, l i * a i s = 0) ∧ ∑ i, l i * b i < 0) := by
  induction n with
  | zero =>
    intro ι _ a b
    classical
    by_cases h : ∀ i, 0 ≤ b i
    · left; exact ⟨0, fun i => by simpa using h i⟩
    · right
      push Not at h
      obtain ⟨i, hi⟩ := h
      refine ⟨fun j => if j = i then 1 else 0, fun j => ?_, fun s => s.elim0, ?_⟩
      · dsimp only; split_ifs <;> norm_num
      · simpa using hi
  | succ n ih =>
    intro ι _ a b
    classical
    let W : ι ⊕ (ι × ι) → ι → ℝ := Sum.elim (fun z i => if a z 0 = 0 ∧ i = z then 1 else 0)
      (fun pq i => if 0 < a pq.1 0 ∧ a pq.2 0 < 0 then
        (if i = pq.1 then -a pq.2 0 else 0) + (if i = pq.2 then a pq.1 0 else 0) else 0)
    have hW0 : ∀ k i, 0 ≤ W k i := by
      intro k i
      rcases k with z | ⟨p, q⟩
      · simp only [W, Sum.elim_inl]; split_ifs <;> norm_num
      · simp only [W, Sum.elim_inr]
        split_ifs with h1 h2 h3 h3 <;> subst_vars <;> first | linarith [h1.1, h1.2] | norm_num
    let C : ι ⊕ (ι × ι) → Fin (n + 1) → ℝ := fun k s => ∑ i, W k i * a i s
    let D : ι ⊕ (ι × ι) → ℝ := fun k => ∑ i, W k i * b i
    have hC0 : ∀ k, C k 0 = 0 := by
      intro k
      rcases k with z | ⟨p, q⟩
      · by_cases hz : a z 0 = 0
        · simp [C, W, hz]
        · simp [C, W, hz]
      · by_cases h : 0 < a p 0 ∧ a q 0 < 0
        · simp only [C, W, Sum.elim_inr, if_pos h, add_mul, ite_mul, zero_mul,
            Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        · simp [C, W, h]
    rcases ih (fun k s => C k s.succ) D with ⟨y, hy⟩ | ⟨μ, hμ0, hμ1, hμ2⟩
    · left
      let r : ι → ℝ := fun i => b i - ∑ s : Fin n, a i s.succ * y s
      have key : ∀ k, 0 ≤ ∑ i, W k i * r i := by
        intro k
        have e : ∑ i, W k i * r i = D k - ∑ s, C k s.succ * y s := by
          simp only [r, D, C, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul,
            mul_assoc]
          congr 1
          exact Finset.sum_comm
        rw [e]; linarith [hy k]
      have kinl : ∀ z, a z 0 = 0 → 0 ≤ r z := by
        intro z hz
        have := key (Sum.inl z)
        simpa [W, hz] using this
      have kinr : ∀ p q, 0 < a p 0 → a q 0 < 0 → 0 ≤ -a q 0 * r p + a p 0 * r q := by
        intro p q hp hq
        have := key (Sum.inr (p, q))
        simp only [W, Sum.elim_inr, if_pos (And.intro hp hq), add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
        exact this
      obtain ⟨t, ht1, ht2⟩ := exists_between_fin (Finset.univ.filter (fun q => a q 0 < 0))
        (Finset.univ.filter (fun p => 0 < a p 0)) (fun q => r q / a q 0) (fun p => r p / a p 0)
        (by
          intro q hq p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq hp
          have h := kinr p q hp hq
          have e : -a q 0 * r p + a p 0 * r q =
              -(a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0)) := by
            have h1 : r p = (r p / a p 0) * a p 0 := (div_mul_cancel₀ _ hp.ne').symm
            have h2 : r q = (r q / a q 0) * a q 0 := (div_mul_cancel₀ _ hq.ne).symm
            set U := r p / a p 0
            set V := r q / a q 0
            rw [h1, h2]; ring
          by_contra hc
          push Not at hc
          have hpq : 0 < a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0) :=
            mul_pos (mul_pos hp (neg_pos.2 hq)) (sub_pos.2 hc)
          linarith)
      refine ⟨Fin.cons t y, fun i => ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have hr : r i = b i - ∑ s : Fin n, a i s.succ * y s := rfl
      suffices a i 0 * t ≤ r i by linarith
      rcases lt_trichotomy (a i 0) 0 with hneg | hz | hpos
      · have := ht1 i (by simp [hneg])
        rw [div_le_iff_of_neg hneg] at this
        linarith
      · rw [hz, zero_mul]; exact kinl i hz
      · have := ht2 i (by simp [hpos])
        rw [le_div_iff₀ hpos] at this
        linarith
    · right
      refine ⟨fun i => ∑ k, μ k * W k i, fun i => Finset.sum_nonneg
        (fun k _ => mul_nonneg (hμ0 k) (hW0 k i)), fun s => ?_, ?_⟩
      · have e : ∑ i, (∑ k, μ k * W k i) * a i s = ∑ k, μ k * C k s := by
          simp only [C, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]
        refine Fin.cases ?_ (fun s => ?_) s
        · simp [hC0]
        · exact hμ1 s
      · have e : ∑ i, (∑ k, μ k * W k i) * b i = ∑ k, μ k * D k := by
          simp only [D, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]; exact hμ2

/-- Theorem of alternatives over an arbitrary finite variable type. -/
theorem fm_alt' {σ ι : Type} [Fintype σ] [Fintype ι] (a : ι → σ → ℝ) (b : ι → ℝ) :
    (∃ x : σ → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i) ∨
    (∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, ∑ i, l i * a i s = 0) ∧ ∑ i, l i * b i < 0) := by
  classical
  let e := Fintype.equivFin σ
  rcases fm_alt _ (fun i k => a i (e.symm k)) b with ⟨x, hx⟩ | ⟨l, h0, h1, h2⟩
  · left
    refine ⟨fun s => x (e s), fun i => ?_⟩
    rw [Fintype.sum_equiv e _ (fun k => a i (e.symm k) * x k) (fun s => by simp)]
    exact hx i
  · right
    exact ⟨l, h0, fun s => by simpa using h1 (e s), h2⟩

section LP

variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)

lemma weak {x : Fin n → ℝ} {u : Fin m → ℝ} (hx : x ∈ Disjunctive.IntroDuality.PolyNonneg A b)
    (hu : u ∈ Disjunctive.IntroDuality.DualPoly A c) : u ⬝ᵥ b ≤ c ⬝ᵥ x := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hu1, hu2⟩ := hu
  calc u ⬝ᵥ b ≤ u ⬝ᵥ (A *ᵥ x) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx1 i) (hu2 i)
    _ = (u ᵥ* A) ⬝ᵥ x := dotProduct_mulVec u A x
    _ ≤ c ⬝ᵥ x := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hu1 j) (hx2 j)

lemma primal_unbdd (hX : (Disjunctive.IntroDuality.PolyNonneg A b).Nonempty)
    (hU : ¬ (Disjunctive.IntroDuality.DualPoly A c).Nonempty) :
    ∀ M : ℝ, ∃ x ∈ Disjunctive.IntroDuality.PolyNonneg A b, c ⬝ᵥ x < M := by
  classical
  rcases fm_alt' (σ := Fin m) (ι := Fin n ⊕ Fin m)
      (Sum.elim (fun j i => A i j) (fun i' i => if i = i' then -1 else 0)) (Sum.elim c 0) with
    ⟨u, hu⟩ | ⟨l, h0, h1, h2⟩
  · exfalso
    apply hU
    refine ⟨u, fun j => ?_, fun i => ?_⟩
    · have := hu (Sum.inl j)
      simpa [Matrix.vecMul, dotProduct, mul_comm] using this
    · have := hu (Sum.inr i)
      simp at this
      simpa using this
  · let d : Fin n → ℝ := fun j => l (Sum.inl j)
    have hd0 : ∀ j, 0 ≤ d j := fun j => h0 _
    have hAd : ∀ i, 0 ≤ (A *ᵥ d) i := by
      intro i
      have := h1 i
      simp [Fintype.sum_sum_type] at this
      have e : (A *ᵥ d) i = l (Sum.inr i) := by
        simp only [Matrix.mulVec, dotProduct, d]
        rw [Finset.sum_congr rfl (fun j _ => mul_comm (A i j) (l (Sum.inl j)))]
        linarith
      rw [e]; exact h0 _
    have hcd : c ⬝ᵥ d < 0 := by
      have := h2
      simp [Fintype.sum_sum_type] at this
      simp only [dotProduct, d]
      rw [Finset.sum_congr rfl (fun j _ => mul_comm (c j) (l (Sum.inl j)))]
      exact this
    intro M
    obtain ⟨x0, hx1, hx2⟩ := hX
    set δ := -(c ⬝ᵥ d) with hδ
    have hδ0 : 0 < δ := by linarith
    set t := (|c ⬝ᵥ x0| + |M| + 1) / δ with ht
    have ht0 : 0 ≤ t := div_nonneg (by positivity) hδ0.le
    have htd : t * δ = |c ⬝ᵥ x0| + |M| + 1 := div_mul_cancel₀ _ hδ0.ne'
    refine ⟨x0 + t • d, ⟨fun i => ?_, fun j => ?_⟩, ?_⟩
    · rw [mulVec_add, mulVec_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hx1 i, hAd i, mul_nonneg ht0 (hAd i)]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact add_nonneg (hx2 j) (mul_nonneg ht0 (hd0 j))
    · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      have h3 : t * (c ⬝ᵥ d) = -(|c ⬝ᵥ x0| + |M| + 1) := by rw [← htd, hδ]; ring
      rw [h3]
      have := le_abs_self (c ⬝ᵥ x0)
      have := neg_abs_le M
      linarith

lemma dual_unbdd (hX : ¬ (Disjunctive.IntroDuality.PolyNonneg A b).Nonempty)
    (hU : (Disjunctive.IntroDuality.DualPoly A c).Nonempty) :
    ∀ M : ℝ, ∃ u ∈ Disjunctive.IntroDuality.DualPoly A c, M < u ⬝ᵥ b := by
  classical
  rcases fm_alt' (σ := Fin n) (ι := Fin m ⊕ Fin n)
      (Sum.elim (fun i j => -A i j) (fun j' j => if j = j' then -1 else 0))
      (Sum.elim (fun i => -b i) 0) with
    ⟨x, hx⟩ | ⟨l, h0, h1, h2⟩
  · exfalso
    apply hX
    refine ⟨x, fun i => ?_, fun j => ?_⟩
    · have := hx (Sum.inl i)
      simp only [Sum.elim_inl, neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff] at this
      simpa [Matrix.mulVec, dotProduct] using this
    · have := hx (Sum.inr j)
      simp at this
      simpa using this
  · let y : Fin m → ℝ := fun i => l (Sum.inl i)
    have hy0 : ∀ i, 0 ≤ y i := fun i => h0 _
    have hyA : ∀ j, (y ᵥ* A) j ≤ 0 := by
      intro j
      have := h1 j
      simp [Fintype.sum_sum_type] at this
      have e : (y ᵥ* A) j = -l (Sum.inr j) := by
        simp only [Matrix.vecMul, dotProduct, y]
        linarith
      rw [e]; linarith [h0 (Sum.inr j)]
    have hyb : 0 < y ⬝ᵥ b := by
      have := h2
      simp [Fintype.sum_sum_type] at this
      simp only [dotProduct, y]
      linarith
    intro M
    obtain ⟨u0, hu1, hu2⟩ := hU
    set δ := y ⬝ᵥ b with hδ
    set t := (|u0 ⬝ᵥ b| + |M| + 1) / δ with ht
    have ht0 : 0 ≤ t := div_nonneg (by positivity) hyb.le
    have htd : t * δ = |u0 ⬝ᵥ b| + |M| + 1 := div_mul_cancel₀ _ hyb.ne'
    refine ⟨u0 + t • y, ⟨fun j => ?_, fun i => ?_⟩, ?_⟩
    · rw [add_vecMul, smul_vecMul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hu1 j, hyA j, mul_nonneg ht0 (neg_nonneg.2 (hyA j))]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact add_nonneg (hu2 i) (mul_nonneg ht0 (hy0 i))
    · rw [add_dotProduct, smul_dotProduct, smul_eq_mul, htd]
      have := neg_abs_le (u0 ⬝ᵥ b)
      have := le_abs_self M
      linarith

lemma strong (hX : (Disjunctive.IntroDuality.PolyNonneg A b).Nonempty)
    (hU : (Disjunctive.IntroDuality.DualPoly A c).Nonempty) :
    ∃ x ∈ Disjunctive.IntroDuality.PolyNonneg A b, ∃ u ∈ Disjunctive.IntroDuality.DualPoly A c,
      c ⬝ᵥ x ≤ u ⬝ᵥ b := by
  classical
  rcases fm_alt' (σ := Fin n ⊕ Fin m) (ι := Fin m ⊕ (Fin n ⊕ (Fin n ⊕ (Fin m ⊕ Unit))))
      (Sum.elim (fun i => Sum.elim (fun j => -A i j) 0)
        (Sum.elim (fun j' => Sum.elim (fun j => if j = j' then -1 else 0) 0)
          (Sum.elim (fun j' => Sum.elim 0 (fun i => A i j'))
            (Sum.elim (fun i' => Sum.elim 0 (fun i => if i = i' then -1 else 0))
              (fun _ => Sum.elim c (fun i => -b i))))))
      (Sum.elim (fun i => -b i) (Sum.elim 0 (Sum.elim c (Sum.elim 0 0)))) with
    ⟨z, hz⟩ | ⟨l, h0, h1, h2⟩
  · let x : Fin n → ℝ := fun j => z (Sum.inl j)
    let u : Fin m → ℝ := fun i => z (Sum.inr i)
    refine ⟨x, ⟨fun i => ?_, fun j => ?_⟩, u, ⟨fun j => ?_, fun i => ?_⟩, ?_⟩
    · have := hz (Sum.inl i)
      simp [Fintype.sum_sum_type] at this
      simp only [Matrix.mulVec, dotProduct, x]
      linarith
    · have := hz (Sum.inr (Sum.inl j))
      simp [Fintype.sum_sum_type] at this
      simp only [x, Pi.zero_apply]
      linarith
    · have := hz (Sum.inr (Sum.inr (Sum.inl j)))
      simp [Fintype.sum_sum_type] at this
      simp only [Matrix.vecMul, dotProduct, u]
      rw [Finset.sum_congr rfl (fun i _ => mul_comm (z (Sum.inr i)) (A i j))]
      linarith
    · have := hz (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
      simp [Fintype.sum_sum_type] at this
      simp only [u, Pi.zero_apply]
      linarith
    · have := hz (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))
      simp [Fintype.sum_sum_type] at this
      simp only [dotProduct, x, u]
      rw [Finset.sum_congr rfl (fun i _ => mul_comm (z (Sum.inr i)) (b i))]
      linarith
  · exfalso
    obtain ⟨x0, hx1, hx2⟩ := hX
    obtain ⟨u0, hu1, hu2⟩ := hU
    let l1 : Fin m → ℝ := fun i => l (Sum.inl i)
    let l3 : Fin n → ℝ := fun j => l (Sum.inr (Sum.inr (Sum.inl j)))
    let τ : ℝ := l (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))
    have hl1 : ∀ i, 0 ≤ l1 i := fun i => h0 _
    have hl3 : ∀ j, 0 ≤ l3 j := fun j => h0 _
    have hτ : 0 ≤ τ := h0 _
    have E1 : ∀ j, (l1 ᵥ* A) j ≤ τ * c j := by
      intro j
      have := h1 (Sum.inl j)
      have h2' := h0 (Sum.inr (Sum.inl j))
      simp [Fintype.sum_sum_type] at this
      simp only [Matrix.vecMul, dotProduct, l1, τ]
      linarith
    have E2 : ∀ i, τ * b i ≤ (A *ᵥ l3) i := by
      intro i
      have := h1 (Sum.inr i)
      have h2' := h0 (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
      simp [Fintype.sum_sum_type] at this
      simp only [Matrix.mulVec, dotProduct, l3, τ]
      rw [Finset.sum_congr rfl (fun j _ => mul_comm (A i j) (l (Sum.inr (Sum.inr (Sum.inl j)))))]
      linarith
    have R : c ⬝ᵥ l3 < l1 ⬝ᵥ b := by
      have := h2
      simp [Fintype.sum_sum_type] at this
      simp only [dotProduct, l1, l3]
      rw [Finset.sum_congr rfl (fun j _ => mul_comm (c j) (l (Sum.inr (Sum.inr (Sum.inl j)))))]
      linarith
    -- l1 ⬝ b ≤ τ * (c ⬝ x0)
    have K1 : l1 ⬝ᵥ b ≤ τ * (c ⬝ᵥ x0) := by
      calc l1 ⬝ᵥ b ≤ l1 ⬝ᵥ (A *ᵥ x0) :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx1 i) (hl1 i)
        _ = (l1 ᵥ* A) ⬝ᵥ x0 := dotProduct_mulVec l1 A x0
        _ ≤ (τ • c) ⬝ᵥ x0 := Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (by simpa using E1 j) (hx2 j)
        _ = τ * (c ⬝ᵥ x0) := by rw [smul_dotProduct, smul_eq_mul]
    have K2 : τ * (u0 ⬝ᵥ b) ≤ c ⬝ᵥ l3 := by
      calc τ * (u0 ⬝ᵥ b) = u0 ⬝ᵥ (τ • b) := by rw [dotProduct_smul, smul_eq_mul]
        _ ≤ u0 ⬝ᵥ (A *ᵥ l3) := Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (by simpa using E2 i) (hu2 i)
        _ = (u0 ᵥ* A) ⬝ᵥ l3 := dotProduct_mulVec u0 A l3
        _ ≤ c ⬝ᵥ l3 := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hu1 j) (hl3 j)
    have K3 : τ * (l1 ⬝ᵥ b) ≤ τ * (c ⬝ᵥ l3) := by
      calc τ * (l1 ⬝ᵥ b) = l1 ⬝ᵥ (τ • b) := by rw [dotProduct_smul, smul_eq_mul]
        _ ≤ l1 ⬝ᵥ (A *ᵥ l3) := Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (by simpa using E2 i) (hl1 i)
        _ = (l1 ᵥ* A) ⬝ᵥ l3 := dotProduct_mulVec l1 A l3
        _ ≤ (τ • c) ⬝ᵥ l3 := Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (by simpa using E1 j) (hl3 j)
        _ = τ * (c ⬝ᵥ l3) := by rw [smul_dotProduct, smul_eq_mul]
    rcases hτ.lt_or_eq with hpos | hzero
    · have := (mul_le_mul_iff_of_pos_left hpos).1 K3
      linarith
    · rw [← hzero] at K1 K2
      simp at K1 K2
      linarith

end LP

end DJ824

open Disjunctive.IntroDuality in
theorem solution {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) (c : Fin n → ℝ)
    (hReg : RegularityCondition
              (FeasibleIndices (fun h => PolyNonneg (A h) (b h)))
              (FeasibleIndices (fun h => DualPoly (A h) c))) :
    Xor
      (∃ v : ℝ,
        IsLeast ((fun x => dotProduct c x) '' (⋃ h : Q, PolyNonneg (A h) (b h))) v ∧
        IsGreatest {w : ℝ | ∃ u : (h : Q) → Fin (m h) → ℝ,
                              ∀ h, u h ∈ DualPoly (A h) c ∧
                                w ≤ dotProduct (u h) (b h)} v)
      (((¬ (⋃ h : Q, PolyNonneg (A h) (b h)).Nonempty) ∧
          ((¬ ∃ w : ℝ, ∃ u : (h : Q) → Fin (m h) → ℝ,
                ∀ h, u h ∈ DualPoly (A h) c ∧ w ≤ dotProduct (u h) (b h)) ∨
           UnboundedAboveOn {w : ℝ | ∃ u : (h : Q) → Fin (m h) → ℝ,
                                       ∀ h, u h ∈ DualPoly (A h) c ∧
                                         w ≤ dotProduct (u h) (b h)} id))
       ∨
       ((¬ ∃ w : ℝ, ∃ u : (h : Q) → Fin (m h) → ℝ,
              ∀ h, u h ∈ DualPoly (A h) c ∧ w ≤ dotProduct (u h) (b h)) ∧
          ((¬ (⋃ h : Q, PolyNonneg (A h) (b h)).Nonempty) ∨
           UnboundedBelowOn (⋃ h : Q, PolyNonneg (A h) (b h)) (fun x => dotProduct c x)))) := by
  classical
  unfold Xor
  by_cases hXne : (⋃ h : Q, PolyNonneg (A h) (b h)).Nonempty
  · by_cases hUall : ∀ h, (DualPoly (A h) c).Nonempty
    · have key : ∀ h, (PolyNonneg (A h) (b h)).Nonempty →
          ∃ x ∈ PolyNonneg (A h) (b h), ∃ u ∈ DualPoly (A h) c, dotProduct c x ≤ dotProduct u (b h) :=
        fun h hx => DJ824.strong (A h) (b h) c hx (hUall h)
      choose xs hxs us hus hxu using key
      obtain ⟨x1, hx1⟩ := hXne
      rw [Set.mem_iUnion] at hx1
      obtain ⟨h1, hx1⟩ := hx1
      have : Nonempty {h // (PolyNonneg (A h) (b h)).Nonempty} := ⟨⟨h1, x1, hx1⟩⟩
      obtain ⟨⟨h0, hh0⟩, hmin⟩ := Finite.exists_min
        (fun hh : {h // (PolyNonneg (A h) (b h)).Nonempty} => dotProduct c (xs hh.1 hh.2))
      have hlow : ∀ h x, x ∈ PolyNonneg (A h) (b h) → dotProduct c (xs h0 hh0) ≤ dotProduct c x := by
        intro h x hx
        have e1 := hmin ⟨h, x, hx⟩
        have e2 := DJ824.weak (A h) (b h) c hx (hus h ⟨x, hx⟩)
        have e3 := hxu h ⟨x, hx⟩
        simp only at e1
        linarith
      have hdual : ∀ h, ∃ u ∈ DualPoly (A h) c, dotProduct c (xs h0 hh0) ≤ dotProduct u (b h) := by
        intro h
        by_cases hX : (PolyNonneg (A h) (b h)).Nonempty
        · exact ⟨us h hX, hus h hX, le_trans (hmin ⟨h, hX⟩) (hxu h hX)⟩
        · obtain ⟨u, hu, hlt⟩ := DJ824.dual_unbdd (A h) (b h) c hX (hUall h)
            (dotProduct c (xs h0 hh0))
          exact ⟨u, hu, hlt.le⟩
      choose uu huu hvu using hdual
      refine Or.inl ⟨⟨dotProduct c (xs h0 hh0),
        ⟨⟨xs h0 hh0, Set.mem_iUnion.2 ⟨h0, hxs h0 hh0⟩, rfl⟩, ?_⟩,
        ⟨⟨uu, fun h => ⟨huu h, hvu h⟩⟩, ?_⟩⟩, ?_⟩
      · rintro _ ⟨x, hx, rfl⟩
        rw [Set.mem_iUnion] at hx
        obtain ⟨h, hx⟩ := hx
        exact hlow h x hx
      · rintro w ⟨u, hu⟩
        exact le_trans (hu h0).2 (DJ824.weak (A h0) (b h0) c (hxs h0 hh0) (hu h0).1)
      · rintro (⟨hne, _⟩ | ⟨hno, _⟩)
        · exact hne ⟨x1, Set.mem_iUnion.2 ⟨h1, hx1⟩⟩
        · exact hno ⟨_, uu, fun h => ⟨huu h, hvu h⟩⟩
    · obtain ⟨h1, hU1⟩ := not_forall.1 hUall
      have hQs : (FeasibleIndices (fun h => PolyNonneg (A h) (b h))).Nonempty := by
        obtain ⟨x, hx⟩ := hXne
        rw [Set.mem_iUnion] at hx
        obtain ⟨h, hx⟩ := hx
        exact ⟨h, x, hx⟩
      obtain ⟨h2, hX2, hU2⟩ := hReg ⟨hQs, ⟨h1, hU1⟩⟩
      have hnoD : ¬ ∃ w : ℝ, ∃ u : (h : Q) → Fin (m h) → ℝ,
          ∀ h, u h ∈ DualPoly (A h) c ∧ w ≤ dotProduct (u h) (b h) := by
        rintro ⟨w, u, hu⟩
        exact hU1 ⟨u h1, (hu h1).1⟩
      refine Or.inr ⟨Or.inr ⟨hnoD, Or.inr ⟨hXne, fun M => ?_⟩⟩, ?_⟩
      · obtain ⟨x, hx, hlt⟩ := DJ824.primal_unbdd (A h2) (b h2) c hX2 hU2 M
        exact ⟨x, Set.mem_iUnion.2 ⟨h2, hx⟩, hlt⟩
      · rintro ⟨v, _, hv⟩
        exact hnoD ⟨v, hv.1⟩
  · have hXh : ∀ h, ¬ (PolyNonneg (A h) (b h)).Nonempty := fun h ⟨x, hx⟩ =>
      hXne ⟨x, Set.mem_iUnion.2 ⟨h, hx⟩⟩
    refine Or.inr ⟨Or.inl ⟨hXne, ?_⟩, ?_⟩
    · by_cases hD : ∃ w : ℝ, ∃ u : (h : Q) → Fin (m h) → ℝ,
          ∀ h, u h ∈ DualPoly (A h) c ∧ w ≤ dotProduct (u h) (b h)
      · right
        refine ⟨hD, fun M => ?_⟩
        obtain ⟨w, u, hu⟩ := hD
        have : ∀ h, ∃ u' ∈ DualPoly (A h) c, M + 1 < dotProduct u' (b h) := fun h =>
          DJ824.dual_unbdd (A h) (b h) c (hXh h) ⟨u h, (hu h).1⟩ (M + 1)
        choose u' hu' hlt using this
        exact ⟨M + 1, ⟨u', fun h => ⟨hu' h, (hlt h).le⟩⟩, by simp⟩
      · left; exact hD
    · rintro ⟨v, hv, _⟩
      obtain ⟨x, hx, _⟩ := hv.1
      exact hXne ⟨x, hx⟩
