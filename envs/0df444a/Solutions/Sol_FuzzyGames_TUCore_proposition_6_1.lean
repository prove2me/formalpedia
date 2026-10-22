-- Prove2me | solution 1 for FuzzyGames.TUCore.proposition_6_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T11:51:40.960991+00:00
-- url     : https://prove2.me/submissions/6ef84862-4857-4037-acdd-19c5220a7032

import Mathlib
import Definitions.Def_FuzzyGames_TUCore_Basic

set_option autoImplicit false

namespace FG41ef

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


open FuzzyGames.NTUCore

lemma sum_coal_mul {n : ℕ} (A : Finset (Fin n)) (x : Fin n → ℝ) :
    ∑ s, coal A s * x s = ∑ s ∈ A, x s := by
  simp [coal, ite_mul, Finset.sum_ite_mem]

/-- Weak duality: a vector satisfying every coalition constraint bounds every balance. -/
lemma bal_le {n : ℕ} (𝒞 : CoalFamily n) (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (hc : ∀ A ∈ 𝒞.C, ∑ i ∈ A, c i ≥ v A) (τ : Fin n → ℝ) (m : Finset (Fin n) → ℝ)
    (hm : m ∈ balances 𝒞 τ) :
    ∑ A ∈ 𝒞.C, m A * v A ≤ ∑ i, τ i * c i := by
  obtain ⟨h0, -, hsum⟩ := hm
  calc ∑ A ∈ 𝒞.C, m A * v A ≤ ∑ A ∈ 𝒞.C, m A * ∑ i ∈ A, c i :=
        Finset.sum_le_sum (fun A hA => mul_le_mul_of_nonneg_left (hc A hA) (h0 A))
    _ = ∑ A ∈ 𝒞.C, ∑ i, if i ∈ A then m A * c i else 0 := by
        refine Finset.sum_congr rfl (fun A _ => ?_)
        rw [Finset.mul_sum, ← Finset.sum_filter]
        congr 1
        ext i
        simp
    _ = ∑ i, c i * ∑ A ∈ 𝒞.C.filter (fun A => i ∈ A), m A := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl (fun A _ => ?_)
        split_ifs <;> ring
    _ = ∑ i, τ i * c i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hsum i, mul_comm]

lemma bdd {n : ℕ} (𝒞 : CoalFamily n) (v : Finset (Fin n) → ℝ) (τ : Fin n → ℝ) :
    BddAbove ((fun m => ∑ A ∈ 𝒞.C, m A * v A) '' balances 𝒞 τ) := by
  refine ⟨∑ A ∈ 𝒞.C, (∑ j, |τ j|) * |v A|, ?_⟩
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨h0, -, hsum⟩ := hm
  refine Finset.sum_le_sum (fun A hA => ?_)
  have hne : A.Nonempty := by
    rcases A.eq_empty_or_nonempty with h | h
    · exact absurd (h ▸ hA) 𝒞.empty_not_mem
    · exact h
  obtain ⟨i, hi⟩ := hne
  have h1 : m A ≤ τ i := by
    rw [← hsum i]
    exact Finset.single_le_sum (f := m) (fun B _ => h0 B)
      (Finset.mem_filter.2 ⟨hA, hi⟩)
  have h2 : τ i ≤ ∑ j, |τ j| :=
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |τ j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  calc m A * v A ≤ m A * |v A| := mul_le_mul_of_nonneg_left (le_abs_self _) (h0 A)
    _ ≤ (∑ j, |τ j|) * |v A| := mul_le_mul_of_nonneg_right (h1.trans h2) (abs_nonneg _)

lemma unit_mem {n : ℕ} (𝒞 : CoalFamily n) (A : Finset (Fin n)) (hA : A ∈ 𝒞.C) :
    (fun B => if B = A then (1:ℝ) else 0) ∈ balances 𝒞 (coal A) := by
  refine ⟨fun B => by dsimp only; split_ifs <;> norm_num, fun B hB => ?_, fun i => ?_⟩
  · have : B ≠ A := fun h => hB (h ▸ hA)
    simp [this]
  · rw [Finset.sum_ite_eq']
    simp [coal, Finset.mem_filter, hA]

lemma le_piV {n : ℕ} (𝒞 : CoalFamily n) (v : Finset (Fin n) → ℝ) (A : Finset (Fin n))
    (hA : A ∈ 𝒞.C) : v A ≤ FuzzyGames.TUCore.piV 𝒞 v (coal A) := by
  refine le_csSup (bdd 𝒞 v _) ⟨_, unit_mem 𝒞 A hA, ?_⟩
  simp only
  rw [Finset.sum_eq_single A]
  · simp
  · intro B _ hB; simp [hB]
  · intro h; exact absurd hA h

lemma bal_nonempty {n : ℕ} (𝒞 : CoalFamily n) (τ : Fin n → ℝ) (hτ : 0 ≤ τ) :
    (balances 𝒞 τ).Nonempty := by
  refine ⟨fun B => if B.card = 1 then ∑ j ∈ B, τ j else 0, fun B => ?_, fun B hB => ?_,
    fun i => ?_⟩
  · dsimp only
    split_ifs
    · exact Finset.sum_nonneg (fun j _ => hτ j)
    · exact le_refl _
  · dsimp only
    rw [if_neg]
    intro h
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
    exact hB (𝒞.singleton_mem a)
  · rw [Finset.sum_eq_single ({i} : Finset (Fin n))]
    · simp
    · intro B hB hBi
      rw [if_neg]
      intro h
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
      have : i ∈ ({a} : Finset (Fin n)) := (Finset.mem_filter.1 hB).2
      rw [Finset.mem_singleton] at this
      exact hBi (by rw [this])
    · intro h
      exact absurd (Finset.mem_filter.2 ⟨𝒞.singleton_mem i, Finset.mem_singleton_self i⟩) h

lemma piV_le {n : ℕ} (𝒞 : CoalFamily n) (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (hc : ∀ A ∈ 𝒞.C, ∑ i ∈ A, c i ≥ v A) (τ : Fin n → ℝ) (hτ : 0 ≤ τ) :
    FuzzyGames.TUCore.piV 𝒞 v τ ≤ ∑ i, τ i * c i := by
  obtain ⟨m0, hm0⟩ := bal_nonempty 𝒞 τ hτ
  refine csSup_le ⟨_, m0, hm0, rfl⟩ ?_
  rintro _ ⟨m, hm, rfl⟩
  exact bal_le 𝒞 v c hc τ m hm

/-- Bondareva–Shapley, the hard direction, via the Fourier–Motzkin alternative. -/
lemma core_of_balanced {n : ℕ} (𝒞 : CoalFamily n) (v : Finset (Fin n) → ℝ)
    (hb : FuzzyGames.TUCore.piV 𝒞 v (coal Finset.univ) = v Finset.univ) :
    ∃ c : Fin n → ℝ, ∑ i, c i ≤ v Finset.univ ∧ ∀ A ∈ 𝒞.C, ∑ i ∈ A, c i ≥ v A := by
  classical
  let a : Option ↥𝒞.C → Fin n → ℝ := fun o => o.elim (fun _ => 1) (fun A s => -coal A.1 s)
  let b : Option ↥𝒞.C → ℝ := fun o => o.elim (v Finset.univ) (fun A => -v A.1)
  rcases fm_alt n a b with ⟨x, hx⟩ | ⟨l, hl0, hl1, hl2⟩
  · refine ⟨x, ?_, fun A hA => ?_⟩
    · simpa [a, b] using hx none
    · have := hx (some ⟨A, hA⟩)
      simp only [a, b, Option.elim, neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff] at this
      rw [sum_coal_mul] at this
      exact this
  · exfalso
    have e1 : ∀ s, ∑ A : ↥𝒞.C, l (some A) * coal A.1 s = l none := by
      intro s
      have := hl1 s
      simp only [a, Fintype.sum_option, Option.elim, mul_one, mul_neg,
        Finset.sum_neg_distrib] at this
      linarith
    have e2 : l none * v Finset.univ < ∑ A : ↥𝒞.C, l (some A) * v A.1 := by
      have := hl2
      simp only [b, Fintype.sum_option, Option.elim, mul_neg, Finset.sum_neg_distrib] at this
      linarith
    have hpos : 0 < l none := by
      rcases (hl0 none).lt_or_eq with h | h
      · exact h
      · exfalso
        have hz : ∀ A : ↥𝒞.C, l (some A) = 0 := by
          intro A
          have hne : A.1.Nonempty := by
            rcases A.1.eq_empty_or_nonempty with h' | h'
            · exact absurd (h' ▸ A.2) 𝒞.empty_not_mem
            · exact h'
          obtain ⟨s, hs⟩ := hne
          have hs0 := e1 s
          rw [← h] at hs0
          have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun B _ =>
            mul_nonneg (hl0 (some B)) (by unfold coal; split_ifs <;> norm_num))).1 hs0 A
            (Finset.mem_univ _)
          simpa [coal, hs] using hall
        rw [← h] at e2
        simp [hz] at e2
    let m : Finset (Fin n) → ℝ := fun B => if h : B ∈ 𝒞.C then l (some ⟨B, h⟩) / l none else 0
    have hm_sub : ∀ (g : Finset (Fin n) → ℝ),
        ∑ B ∈ 𝒞.C, m B * g B = (∑ A : ↥𝒞.C, l (some A) * g A.1) / l none := by
      intro g
      rw [← Finset.sum_coe_sort 𝒞.C, Finset.sum_div]
      refine Finset.sum_congr rfl (fun A _ => ?_)
      simp only [m, dif_pos A.2]
      ring
    have hm : m ∈ balances 𝒞 (coal Finset.univ) := by
      refine ⟨fun B => ?_, fun B hB => ?_, fun i => ?_⟩
      · simp only [m]
        split_ifs
        · exact div_nonneg (hl0 _) hpos.le
        · exact le_refl _
      · simp only [m, dif_neg hB]
      · have h3 : ∑ A ∈ 𝒞.C.filter (fun A => i ∈ A), m A = ∑ B ∈ 𝒞.C, m B * coal B i := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl (fun B _ => ?_)
          simp [coal]
        rw [h3, hm_sub (fun B => coal B i), e1 i, div_self hpos.ne']
        simp [coal]
    have hval : ∑ B ∈ 𝒞.C, m B * v B ≤ FuzzyGames.TUCore.piV 𝒞 v (coal Finset.univ) :=
      le_csSup (bdd 𝒞 v _) ⟨m, hm, rfl⟩
    rw [hb] at hval
    rw [hm_sub v, div_le_iff₀ hpos] at hval
    linarith

end FG41ef

open FuzzyGames.TUCore in
theorem solution {n : ℕ} (𝒞 : FuzzyGames.NTUCore.CoalFamily n) (v : Finset (Fin n) → ℝ) :
    ((core 𝒞 v).Nonempty ↔ IsBalanced 𝒞 v) ∧
      (IsBalanced 𝒞 v → core 𝒞 v = fuzzyCore (piV 𝒞 v)) := by
  have hge : v Finset.univ ≤ piV 𝒞 v (FuzzyGames.NTUCore.coal Finset.univ) :=
    FG41ef.le_piV 𝒞 v _ 𝒞.univ_mem
  have hone : (0 : Fin n → ℝ) ≤ FuzzyGames.NTUCore.coal Finset.univ := by
    intro i; simp [FuzzyGames.NTUCore.coal]
  refine ⟨⟨fun ⟨c, hc1, hc2⟩ => ?_, fun hb => ?_⟩, fun hb => ?_⟩
  · show piV 𝒞 v (FuzzyGames.NTUCore.coal Finset.univ) = v Finset.univ
    refine le_antisymm ?_ hge
    have := FG41ef.piV_le 𝒞 v c hc2 _ hone
    rw [FG41ef.sum_coal_mul, hc1] at this
    exact this
  · obtain ⟨c, hc1, hc2⟩ := FG41ef.core_of_balanced 𝒞 v hb
    exact ⟨c, le_antisymm hc1 (hc2 _ 𝒞.univ_mem), hc2⟩
  · have hb' : piV 𝒞 v (FuzzyGames.NTUCore.coal Finset.univ) = v Finset.univ := hb
    ext c
    constructor
    · rintro ⟨hc1, hc2⟩
      refine ⟨by rw [hc1]; exact hb'.symm, fun τ hτ => ?_⟩
      exact FG41ef.piV_le 𝒞 v c hc2 τ (show τ ∈ Set.Icc 0 1 from hτ).1
    · rintro ⟨hc1, hc2⟩
      refine ⟨by rw [hc1]; exact hb', fun A hA => ?_⟩
      have hcube : FuzzyGames.NTUCore.coal A ∈ FuzzyGames.NTUCore.cube n := by
        show _ ∈ Set.Icc _ _
        constructor <;> intro i <;> simp only [FuzzyGames.NTUCore.coal, Pi.zero_apply,
          Pi.one_apply] <;> split_ifs <;> norm_num
      have h1 := hc2 _ hcube
      rw [FG41ef.sum_coal_mul] at h1
      exact le_trans (FG41ef.le_piV 𝒞 v A hA) h1
