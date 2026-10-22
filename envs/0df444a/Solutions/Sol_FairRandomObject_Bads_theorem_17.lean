-- Prove2me | solution 1 for FairRandomObject.Bads.theorem_17
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T01:51:22.133989+00:00
-- url     : https://prove2.me/submissions/87a77f7a-b890-4417-ae37-89edfd16e930

import Mathlib
import Definitions.Def_FairRandomObject_Bads_Setting
import Definitions.Def_FairRandomObject_Bads_BottomHeavy
import Theorems.Thm_FairRandomObject_Bads_prop_14_delta
import Theorems.Thm_FairRandomObject_Bads_step_1

open FairRandomObject.Bads

namespace Bads17Aux

open Classical

/-- generic Abel-type lemma. -/
theorem key_le {ι : Type*} (x e : ι → ℝ) :
    ∀ (s : Finset ι), (∀ k ∈ s, 0 ≤ ∑ j ∈ s.filter (fun j => x j ≤ x k), e j) →
      ∀ M : ℝ, (∀ j ∈ s, x j ≤ M) → ∑ j ∈ s, e j * x j ≤ M * ∑ j ∈ s, e j := by
  intro s
  induction h : s.card using Nat.strong_induction_on generalizing s with
  | _ N ih =>
  intro hpre M hM
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hs]
  obtain ⟨a, ha, hamax⟩ := s.exists_max_image x hs
  set m := x a
  set s' := s.filter (fun j => x j < m) with hs'
  have hsplit : ∀ f : ι → ℝ, ∑ j ∈ s, f j =
      ∑ j ∈ s', f j + ∑ j ∈ s.filter (fun j => ¬ x j < m), f j := by
    intro f; rw [Finset.sum_filter_add_sum_filter_not]
  have htop : ∑ j ∈ s.filter (fun j => ¬ x j < m), e j * x j =
      m * ∑ j ∈ s.filter (fun j => ¬ x j < m), e j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_filter] at hj
    have : x j = m := le_antisymm (hamax j hj.1) (not_lt.mp hj.2)
    rw [this]; ring
  have hcard : s'.card < N := by
    rw [← h]
    apply Finset.card_lt_card
    refine ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
    have := hsub ha
    simp only [s', Finset.mem_filter] at this
    exact lt_irrefl _ this.2
  have hpre' : ∀ k ∈ s', 0 ≤ ∑ j ∈ s'.filter (fun j => x j ≤ x k), e j := by
    intro k hk
    have hk' : x k < m := (Finset.mem_filter.mp hk).2
    have : s'.filter (fun j => x j ≤ x k) = s.filter (fun j => x j ≤ x k) := by
      ext j; simp only [s', Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, lt_of_le_of_lt h3 hk'⟩, h3⟩
    rw [this]; exact hpre k (Finset.mem_filter.mp hk).1
  have IH := ih _ hcard s' rfl hpre' m (fun j hj => le_of_lt (Finset.mem_filter.mp hj).2)
  have htot : 0 ≤ ∑ j ∈ s, e j := by
    have := hpre a ha
    have hf : s.filter (fun j => x j ≤ x a) = s := by
      ext j; simp only [Finset.mem_filter]; exact ⟨fun h => h.1, fun h => ⟨h, hamax j h⟩⟩
    rwa [hf] at this
  have hmM : m ≤ M := hM a ha
  rw [hsplit (fun j => e j * x j), htop]
  calc ∑ j ∈ s', e j * x j + m * ∑ j ∈ s.filter (fun j => ¬ x j < m), e j
      ≤ m * ∑ j ∈ s', e j + m * ∑ j ∈ s.filter (fun j => ¬ x j < m), e j := by linarith
    _ = m * ∑ j ∈ s, e j := by rw [hsplit e]; ring
    _ ≤ M * ∑ j ∈ s, e j := mul_le_mul_of_nonneg_right hmM htot

theorem key_lt {ι : Type*} (x e : ι → ℝ) (s : Finset ι)
    (hpre : ∀ k ∈ s, 0 ≤ ∑ j ∈ s.filter (fun j => x j ≤ x k), e j)
    (M : ℝ) (hM : ∀ j ∈ s, x j ≤ M) (k : ι) (_hk : k ∈ s) (l : ι) (hl : l ∈ s)
    (hkl : x k < x l) (hpos : 0 < ∑ j ∈ s.filter (fun j => x j ≤ x k), e j) :
    ∑ j ∈ s, e j * x j < M * ∑ j ∈ s, e j := by
  set s1 := s.filter (fun j => x j ≤ x k) with hs1
  set s2 := s.filter (fun j => ¬ x j ≤ x k) with hs2
  set D1 := ∑ j ∈ s1, e j with hD1
  have hs2ne : s2.Nonempty := ⟨l, by simp [s2, hl, hkl]⟩
  obtain ⟨b, hb, hbmin⟩ := s2.exists_min_image x hs2ne
  have hbk : x k < x b := by
    have := (Finset.mem_filter.mp hb).2; exact lt_of_not_ge this
  -- part 1
  have hpre1 : ∀ k' ∈ s1, 0 ≤ ∑ j ∈ s1.filter (fun j => x j ≤ x k'), e j := by
    intro k' hk'
    have hk'' : x k' ≤ x k := (Finset.mem_filter.mp hk').2
    have : s1.filter (fun j => x j ≤ x k') = s.filter (fun j => x j ≤ x k') := by
      ext j; simp only [s1, Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, le_trans h3 hk''⟩, h3⟩
    rw [this]; exact hpre k' (Finset.mem_filter.mp hk').1
  have P1 := key_le x e s1 hpre1 (x k) (fun j hj => (Finset.mem_filter.mp hj).2)
  -- part 2
  set e' : ι → ℝ := fun j => e j + if j = b then D1 else 0 with he'
  have hsum' : ∀ T : Finset ι, b ∈ T → ∑ j ∈ T, e' j = ∑ j ∈ T, e j + D1 := by
    intro T hT
    simp only [e', Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hT]
  have hsumx' : ∑ j ∈ s2, e' j * x j = ∑ j ∈ s2, e j * x j + D1 * x b := by
    simp only [e', add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq', if_pos hb]
  have hpre2 : ∀ k' ∈ s2, 0 ≤ ∑ j ∈ s2.filter (fun j => x j ≤ x k'), e' j := by
    intro k' hk'
    have hbk' : x b ≤ x k' := hbmin k' hk'
    have hbin : b ∈ s2.filter (fun j => x j ≤ x k') := Finset.mem_filter.mpr ⟨hb, hbk'⟩
    rw [hsum' _ hbin]
    have hk'k : x k < x k' := lt_of_lt_of_le hbk hbk'
    have hsp := Finset.sum_filter_add_sum_filter_not (s.filter (fun j => x j ≤ x k'))
      (fun j => x j ≤ x k) e
    have hA : (s.filter (fun j => x j ≤ x k')).filter (fun j => x j ≤ x k) = s1 := by
      ext j; simp only [s1, Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, le_trans h3 hk'k.le⟩, h3⟩
    have hB : (s.filter (fun j => x j ≤ x k')).filter (fun j => ¬ x j ≤ x k) =
        s2.filter (fun j => x j ≤ x k') := by
      ext j; simp only [s2, Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
      · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩
    rw [hA, hB] at hsp
    have := hpre k' (Finset.mem_filter.mp hk').1
    linarith
  have P2 := key_le x e' s2 hpre2 M (fun j hj => hM j (Finset.mem_filter.mp hj).1)
  rw [hsumx', hsum' _ hb] at P2
  have hs : ∑ j ∈ s, e j = D1 + ∑ j ∈ s2, e j := (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hsx : ∑ j ∈ s, e j * x j = ∑ j ∈ s1, e j * x j + ∑ j ∈ s2, e j * x j :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hs, hsx]
  have : D1 * x k < D1 * x b := mul_lt_mul_of_pos_left hbk hpos
  nlinarith

/-- prefix sum over a lower set. -/
noncomputable def pre {n : ℕ} (x p : Fin n → ℝ) (v : ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => x j ≤ v), p j

theorem dom_le {n : ℕ} (x p q : Fin n → ℝ) (hp : ∑ j, p j = 1) (hq : ∑ j, q j = 1)
    (hpre : ∀ k, pre x p (x k) ≤ pre x q (x k)) :
    ∑ j, q j * x j ≤ ∑ j, p j * x j := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · simp
  obtain ⟨a, -, hamax⟩ := (Finset.univ : Finset (Fin n)).exists_max_image x Finset.univ_nonempty
  have := key_le x (fun j => q j - p j) Finset.univ (fun k _ => by
      have := hpre k; unfold pre at this; rw [Finset.sum_sub_distrib]; linarith)
    (x a) (fun j _ => hamax j (Finset.mem_univ _))
  simp only [Finset.sum_sub_distrib, sub_mul, hp, hq, sub_self, mul_zero] at this
  linarith

theorem dom_lt {n : ℕ} (x p q : Fin n → ℝ) (hp : ∑ j, p j = 1) (hq : ∑ j, q j = 1)
    (hpre : ∀ k, pre x p (x k) ≤ pre x q (x k))
    (hpt : ∀ i j, x i = x j → p i = p j) (hqt : ∀ i j, x i = x j → q i = q j)
    (hne : p ≠ q) :
    ∑ j, q j * x j < ∑ j, p j * x j := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · exact absurd (funext fun i => (hn.false i).elim) hne
  obtain ⟨a, -, hamax⟩ := (Finset.univ : Finset (Fin n)).exists_max_image x Finset.univ_nonempty
  set e : Fin n → ℝ := fun j => q j - p j with he
  have hpre' : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ ∑ j ∈ Finset.univ.filter (fun j => x j ≤ x k), e j := by
    intro k _
    have := hpre k; unfold pre at this; simp only [e, Finset.sum_sub_distrib]; linarith
  have hes : ∑ j, e j = 0 := by simp [e, Finset.sum_sub_distrib, hp, hq]
  by_cases hex : ∃ k l, x k < x l ∧ 0 < ∑ j ∈ Finset.univ.filter (fun j => x j ≤ x k), e j
  · obtain ⟨k, l, hkl, hpos⟩ := hex
    have := key_lt x e Finset.univ hpre' (x a) (fun j _ => hamax j (Finset.mem_univ _))
      k (Finset.mem_univ _) l (Finset.mem_univ _) hkl hpos
    simp only [e, Finset.sum_sub_distrib, sub_mul, hp, hq, sub_self, mul_zero] at this
    linarith
  · exfalso
    push Not at hex
    apply hne
    have hD0 : ∀ k l, x k < x l → ∑ j ∈ Finset.univ.filter (fun j => x j ≤ x k), e j = 0 :=
      fun k l hkl => le_antisymm (hex k l hkl) (hpre' k (Finset.mem_univ _))
    funext i
    have hDi : ∑ j ∈ Finset.univ.filter (fun j => x j ≤ x i), e j = 0 := by
      by_cases hl : ∃ l, x i < x l
      · obtain ⟨l, hl⟩ := hl; exact hD0 i l hl
      · push Not at hl
        have : Finset.univ.filter (fun j => x j ≤ x i) = Finset.univ := by
          ext j; simp [hl j]
        rw [this, hes]
    have hL : ∑ j ∈ Finset.univ.filter (fun j => x j < x i), e j = 0 := by
      rcases (Finset.univ.filter (fun j => x j < x i)).eq_empty_or_nonempty with hL | hL
      · rw [hL, Finset.sum_empty]
      obtain ⟨b, hb, hbmax⟩ := (Finset.univ.filter (fun j => x j < x i)).exists_max_image x hL
      have hbi : x b < x i := (Finset.mem_filter.mp hb).2
      have : Finset.univ.filter (fun j => x j < x i) = Finset.univ.filter (fun j => x j ≤ x b) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hj; exact hbmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
        · intro hj; exact lt_of_le_of_lt hj hbi
      rw [this]; exact hD0 b i hbi
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter (fun j => x j ≤ x i)) (fun j => x j < x i) e
    have hA : (Finset.univ.filter (fun j => x j ≤ x i)).filter (fun j => x j < x i) =
        Finset.univ.filter (fun j => x j < x i) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
    have hB : (Finset.univ.filter (fun j => x j ≤ x i)).filter (fun j => ¬ x j < x i) =
        Finset.univ.filter (fun j => x j = x i) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩; exact le_antisymm h1 (not_lt.mp h2)
      · intro h; exact ⟨h.le, not_lt.mpr h.ge⟩
    rw [hA, hB, hL, hDi, zero_add] at hsplit
    have hC : ∑ j ∈ Finset.univ.filter (fun j => x j = x i), e j =
        ((Finset.univ.filter (fun j => x j = x i)).card : ℝ) * e i := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : x j = x i := (Finset.mem_filter.mp hj).2
      simp only [e, hpt j i hj', hqt j i hj']
    have hcpos : (0 : ℝ) < ((Finset.univ.filter (fun j => x j = x i)).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨i, by simp⟩
    rw [hC] at hsplit
    have : e i = 0 := by
      rcases mul_eq_zero.mp hsplit with h | h
      · linarith
      · exact h
    simp only [e] at this; linarith

theorem pre_le_one {n : ℕ} (x p : Fin n → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp : ∑ j, p j = 1) (v : ℝ) :
    pre x p v ≤ 1 := by
  rw [← hp]; unfold pre
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => hp0 j)

theorem pre_full {n : ℕ} (x q : Fin n → ℝ) (hq : ∑ j, q j = 1) (v : ℝ)
    (h0 : ∀ j, v < x j → q j = 0) : pre x q v = 1 := by
  rw [← hq]; unfold pre
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => x j ≤ v) q]
  have : ∑ j ∈ Finset.univ.filter (fun j => ¬ x j ≤ v), q j = 0 := by
    apply Finset.sum_eq_zero; intro j hj
    exact h0 j (lt_of_not_ge (Finset.mem_filter.mp hj).2)
  rw [this, add_zero]

theorem bh_tie {n : ℕ} (θ : ℝ) (x : Fin n → ℝ) (i j : Fin n) (h : x i = x j) :
    bottomHeavy n θ x i = bottomHeavy n θ x j := by
  simp only [bottomHeavy, psi, h]

theorem bh_pos_eq {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) (i : Fin n) :
    bottomHeavy n 1 x i = if prefixMass n 1 x (x i) ≤ 1 then psi n 1 x i
      else if (∀ j, x j < x i → prefixMass n 1 x (x j) ≤ 1) then
        (1 - ∑ j ∈ Finset.univ.filter (fun j => prefixMass n 1 x (x j) ≤ 1), psi n 1 x j) /
          ((Finset.univ.filter (fun j => x j = x i)).card : ℝ)
      else 0 := by
  have : ¬ (0 < (1:ℝ) ∧ ∃ j, x j = 0) := fun ⟨_, j, hj⟩ => (hx j).ne' hj
  simp only [bottomHeavy, if_neg this]

theorem S_mono {n : ℕ} (x : Fin n → ℝ) (hψ : ∀ j, 0 ≤ psi n 1 x j) {v w : ℝ} (h : v ≤ w) :
    prefixMass n 1 x v ≤ prefixMass n 1 x w := by
  unfold prefixMass
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun j _ _ => hψ j)
  intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; intro hj; linarith

theorem lower_le_one {n : ℕ} (x : Fin n → ℝ) (i : Fin n)
    (hcond : ∀ j, x j < x i → prefixMass n 1 x (x j) ≤ 1) :
    ∑ j ∈ Finset.univ.filter (fun j => x j < x i), psi n 1 x j ≤ 1 := by
  rcases (Finset.univ.filter (fun j => x j < x i)).eq_empty_or_nonempty with hL | hL
  · rw [hL, Finset.sum_empty]; norm_num
  obtain ⟨b, hb, hbmax⟩ := (Finset.univ.filter (fun j => x j < x i)).exists_max_image x hL
  have hbi : x b < x i := (Finset.mem_filter.mp hb).2
  have : Finset.univ.filter (fun j => x j < x i) = Finset.univ.filter (fun j => x j ≤ x b) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj; exact hbmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
    · intro hj; exact lt_of_le_of_lt hj hbi
  rw [this]; exact hcond b hbi

theorem B_eq {n : ℕ} (x : Fin n → ℝ) (hψ : ∀ j, 0 ≤ psi n 1 x j) (i : Fin n)
    (hSi : ¬ prefixMass n 1 x (x i) ≤ 1)
    (hcond : ∀ j, x j < x i → prefixMass n 1 x (x j) ≤ 1) :
    Finset.univ.filter (fun j => prefixMass n 1 x (x j) ≤ 1) =
      Finset.univ.filter (fun j => x j < x i) := by
  ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hj; by_contra h
    exact hSi (le_trans (S_mono x hψ (not_lt.mp h)) hj)
  · exact hcond j

theorem split_le {n : ℕ} (x f : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ Finset.univ.filter (fun j => x j ≤ x i), f j =
      ∑ j ∈ Finset.univ.filter (fun j => x j < x i), f j +
        ∑ j ∈ Finset.univ.filter (fun j => x j = x i), f j := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (fun j => x j ≤ x i))
    (fun j => x j < x i) f]
  congr 1
  · congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
  · congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact le_antisymm h1 (not_lt.mp h2)
    · intro h; exact ⟨h.le, not_lt.mpr h.ge⟩

theorem sum_tie {n : ℕ} (x f : Fin n → ℝ) (i : Fin n) (hf : ∀ j, x j = x i → f j = f i) :
    ∑ j ∈ Finset.univ.filter (fun j => x j = x i), f j =
      ((Finset.univ.filter (fun j => x j = x i)).card : ℝ) * f i := by
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro j hj; exact hf j (Finset.mem_filter.mp hj).2

theorem card_tie_pos {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    (0 : ℝ) < ((Finset.univ.filter (fun j => x j = x i)).card : ℝ) := by
  exact_mod_cast Finset.card_pos.mpr ⟨i, by simp⟩

theorem bh_pos_nonneg {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hψ : ∀ j, 0 ≤ psi n 1 x j) (i : Fin n) : 0 ≤ bottomHeavy n 1 x i := by
  rw [bh_pos_eq x hx i]
  split_ifs with h1 h2
  · exact hψ i
  · rw [B_eq x hψ i h1 h2]
    apply div_nonneg _ (card_tie_pos x i).le
    linarith [lower_le_one x i h2]
  · exact le_refl 0

theorem bh_pos_le_psi {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hψ : ∀ j, 0 ≤ psi n 1 x j) (i : Fin n) : bottomHeavy n 1 x i ≤ psi n 1 x i := by
  rw [bh_pos_eq x hx i]
  split_ifs with h1 h2
  · exact le_refl _
  · rw [B_eq x hψ i h1 h2]
    have hS : prefixMass n 1 x (x i) = ∑ j ∈ Finset.univ.filter (fun j => x j < x i), psi n 1 x j
        + ((Finset.univ.filter (fun j => x j = x i)).card : ℝ) * psi n 1 x i := by
      unfold prefixMass
      rw [split_le x (psi n 1 x) i, sum_tie x (psi n 1 x) i]
      intro j hj; simp only [psi, hj]
    rw [div_le_iff₀ (card_tie_pos x i)]
    push Not at h1
    linarith
  · exact hψ i

theorem bh_pos_sum {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    ∑ j, bottomHeavy n 1 x j = 1 := by
  obtain ⟨hψ, hsumψ, -⟩ := step_1 hn 1 zero_le_one le_rfl x hx
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  by_cases hB : ∀ j, prefixMass n 1 x (x j) ≤ 1
  · have : ∀ j, bottomHeavy n 1 x j = psi n 1 x j := by
      intro j; rw [bh_pos_eq x hx j, if_pos (hB j)]
    simp only [this]
    obtain ⟨a, -, hamax⟩ := (Finset.univ : Finset (Fin n)).exists_max_image x hne
    have hSa : prefixMass n 1 x (x a) = ∑ j, psi n 1 x j := by
      unfold prefixMass
      congr 1; ext j; simp [hamax j]
    have := hB a
    linarith
  · push Not at hB
    have hne2 : (Finset.univ.filter (fun j => 1 < prefixMass n 1 x (x j))).Nonempty := by
      obtain ⟨j, hj⟩ := hB; exact ⟨j, by simp [hj]⟩
    obtain ⟨i0, hi0, hi0min⟩ :=
      (Finset.univ.filter (fun j => 1 < prefixMass n 1 x (x j))).exists_min_image x hne2
    have hSi0 : ¬ prefixMass n 1 x (x i0) ≤ 1 := not_le.mpr (Finset.mem_filter.mp hi0).2
    have hcond : ∀ j, x j < x i0 → prefixMass n 1 x (x j) ≤ 1 := by
      intro j hj; by_contra h
      have := hi0min j (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; linarith)
      linarith
    set L := ∑ j ∈ Finset.univ.filter (fun j => x j < x i0), psi n 1 x j
    set c := (1 - L) / ((Finset.univ.filter (fun j => x j = x i0)).card : ℝ)
    have hval : ∀ j, bottomHeavy n 1 x j =
        if x j < x i0 then psi n 1 x j else if x j = x i0 then c else 0 := by
      intro j
      rw [bh_pos_eq x hx j]
      by_cases hj1 : x j < x i0
      · rw [if_pos (hcond j hj1), if_pos hj1]
      · rw [if_neg hj1]
        by_cases hj2 : x j = x i0
        · rw [if_pos hj2, hj2, if_neg hSi0, if_pos hcond, B_eq x hψ i0 hSi0 hcond]
        · rw [if_neg hj2]
          have hlt : x i0 < x j := lt_of_le_of_ne (not_lt.mp hj1) (Ne.symm hj2)
          have h1 : ¬ prefixMass n 1 x (x j) ≤ 1 := fun h =>
            hSi0 (le_trans (S_mono x hψ hlt.le) h)
          rw [if_neg h1, if_neg]
          intro h; exact hSi0 (h i0 hlt)
    simp only [hval]
    rw [Finset.sum_ite, Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hf1 : Finset.univ.filter (fun j => x j < x i0) = Finset.univ.filter (fun j => x j < x i0) := rfl
    have hf2 : (Finset.univ.filter (fun j => ¬ x j < x i0)).filter (fun j => x j = x i0) =
        Finset.univ.filter (fun j => x j = x i0) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨not_lt.mpr h.ge, h⟩⟩
    rw [hf2]
    have hcp := card_tie_pos x i0
    simp only [c]
    field_simp
    ring

theorem bh_zero_eq {n : ℕ} (x : Fin n → ℝ) (hz : ∃ j, x j = 0) (i : Fin n) :
    bottomHeavy n 1 x i =
      if x i = 0 then 1 / ((Finset.univ.filter (fun j => x j = 0)).card : ℝ) else 0 := by
  simp only [bottomHeavy, if_pos (And.intro one_pos hz)]

theorem bh_zero_sum {n : ℕ} (x : Fin n → ℝ) (hz : ∃ j, x j = 0) :
    ∑ j, bottomHeavy n 1 x j = 1 := by
  simp only [bh_zero_eq x hz]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  obtain ⟨j0, hj0⟩ := hz
  have : (0:ℝ) < ((Finset.univ.filter (fun j => x j = 0)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨j0, by simp [hj0]⟩
  field_simp

theorem bh_zero_nonneg {n : ℕ} (x : Fin n → ℝ) (hz : ∃ j, x j = 0) (i : Fin n) :
    0 ≤ bottomHeavy n 1 x i := by
  rw [bh_zero_eq x hz]; split_ifs
  · positivity
  · exact le_refl 0

theorem sum_t_nonneg {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) (k : Fin n) :
    0 ≤ ∑ j ∈ Finset.univ.filter (fun j => x j ≤ x k), (mean x / x j - 1) := by
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hnpos : (0:ℝ) < n := by linarith
  have hall : 0 ≤ ∑ j, (mean x / x j - 1) := by
    obtain ⟨-, h1, -⟩ := step_1 hn 1 zero_le_one le_rfl x hx
    unfold psi at h1
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum] at h1
    have : (n:ℝ) * (1 / n) = 1 := by field_simp
    rw [this] at h1
    have h2 : 0 ≤ 1 / ((n:ℝ) - 1) * ∑ j, (mean x / x j - 1) := by linarith
    rcases le_or_gt 0 (∑ j, (mean x / x j - 1)) with h' | h'
    · exact h'
    · have : 1 / ((n:ℝ) - 1) * ∑ j, (mean x / x j - 1) < 0 :=
        mul_neg_of_pos_of_neg (by positivity) h'
      linarith
  by_cases hk : x k ≤ mean x
  · apply Finset.sum_nonneg
    intro j hj
    have hjk : x j ≤ x k := (Finset.mem_filter.mp hj).2
    have : 1 ≤ mean x / x j := by rw [le_div_iff₀ (hx j)]; linarith
    linarith
  · push Not at hk
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => x j ≤ x k)] at hall
    have : ∑ j ∈ Finset.univ.filter (fun j => ¬ x j ≤ x k), (mean x / x j - 1) ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      have hjk : x k < x j := lt_of_not_ge (Finset.mem_filter.mp hj).2
      have : mean x / x j ≤ 1 := by rw [div_le_iff₀ (hx j)]; linarith
      linarith
    linarith

theorem pre_psi {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) (δ : ℝ)
    (hδ : δ ≤ 1 / ((n:ℝ) - 1)) (k : Fin n) :
    ∑ j ∈ Finset.univ.filter (fun j => x j ≤ x k), (1 / (n:ℝ) + δ * (mean x / x j - 1)) ≤
      prefixMass n 1 x (x k) := by
  unfold prefixMass psi
  have hT := sum_t_nonneg hn x hx k
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, one_div] at *
  have : δ * ∑ j ∈ Finset.univ.filter (fun j => x j ≤ x k), (mean x / x j - 1) ≤
      ((n:ℝ) - 1)⁻¹ * ∑ j ∈ Finset.univ.filter (fun j => x j ≤ x k), (mean x / x j - 1) :=
    mul_le_mul_of_nonneg_right hδ hT
  linarith

section perm
variable {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ)

theorem mean_perm : mean (fun j => x (σ j)) = mean x := by
  unfold mean; rw [Equiv.sum_comp σ x]

theorem psi_perm (θ : ℝ) (j : Fin n) : psi n θ (fun j => x (σ j)) j = psi n θ x (σ j) := by
  unfold psi; rw [mean_perm]

theorem pm_perm (θ v : ℝ) : prefixMass n θ (fun j => x (σ j)) v = prefixMass n θ x v := by
  unfold prefixMass
  simp only [Finset.sum_filter, psi_perm]
  exact Equiv.sum_comp σ (fun j => if x j ≤ v then psi n θ x j else 0)

theorem card_perm (p : ℝ → Prop) [DecidablePred p] :
    ((Finset.univ.filter (fun j => p (x (σ j)))).card : ℝ) =
      ((Finset.univ.filter (fun j => p (x j))).card : ℝ) := by
  simp only [Finset.card_filter, Nat.cast_sum]
  exact Equiv.sum_comp σ (fun j => ((if p (x j) then 1 else 0 : ℕ) : ℝ))

theorem bh_perm (i : Fin n) :
    bottomHeavy n 1 (fun j => x (σ j)) i = bottomHeavy n 1 x (σ i) := by
  have hex : (∃ j, x (σ j) = 0) ↔ ∃ j, x j = 0 :=
    ⟨fun ⟨j, h⟩ => ⟨σ j, h⟩, fun ⟨j, h⟩ => ⟨σ.symm j, by simp [h]⟩⟩
  have hall : (∀ j, x (σ j) < x (σ i) → prefixMass n 1 x (x (σ j)) ≤ 1) ↔
      (∀ j, x j < x (σ i) → prefixMass n 1 x (x j) ≤ 1) :=
    ⟨fun h j => by simpa using h (σ.symm j), fun h j => h (σ j)⟩
  have hB : ∑ j ∈ Finset.univ.filter (fun j => prefixMass n 1 x (x (σ j)) ≤ 1),
      psi n 1 x (σ j) = ∑ j ∈ Finset.univ.filter (fun j => prefixMass n 1 x (x j) ≤ 1),
      psi n 1 x j := by
    simp only [Finset.sum_filter]
    exact Equiv.sum_comp σ (fun j => if prefixMass n 1 x (x j) ≤ 1 then psi n 1 x j else 0)
  have hc1 := card_perm σ x (fun v => v = 0)
  have hc2 := card_perm σ x (fun v => v = x (σ i))
  simp only [bottomHeavy, pm_perm, psi_perm, hex, hall, hB, hc1, hc2]

end perm

theorem psi_meas {n : ℕ} (j : Fin n) : Measurable fun x : Fin n → ℝ => psi n 1 x j := by
  unfold psi mean; fun_prop

theorem pm_meas {n : ℕ} (g : (Fin n → ℝ) → ℝ) (hg : Measurable g) :
    Measurable fun x => prefixMass n 1 x (g x) := by
  unfold prefixMass
  simp only [Finset.sum_filter]
  apply Finset.measurable_sum; intro j _
  exact Measurable.ite (measurableSet_le (measurable_pi_apply j) hg) (psi_meas j) measurable_const

theorem card_meas {n : ℕ} (g : (Fin n → ℝ) → ℝ) (hg : Measurable g) :
    Measurable fun x : Fin n → ℝ => ((Finset.univ.filter (fun j => x j = g x)).card : ℝ) := by
  simp only [Finset.card_filter, Nat.cast_sum]
  apply Finset.measurable_sum; intro j _
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply j) hg) measurable_const
    measurable_const

theorem bh_meas {n : ℕ} : Measurable (bottomHeavy n 1) := by
  apply measurable_pi_lambda
  intro i
  unfold bottomHeavy
  have hz : MeasurableSet {x : Fin n → ℝ | 0 < (1:ℝ) ∧ ∃ j, x j = 0} := by
    apply measurableSet_setOfPred.mpr
    apply Measurable.and measurable_const
    apply Measurable.exists; intro j
    exact measurableSet_setOfPred.mp (measurableSet_eq_fun (measurable_pi_apply j) measurable_const)
  have hc : MeasurableSet {x : Fin n → ℝ |
      ∀ j, x j < x i → prefixMass n 1 x (x j) ≤ 1} := by
    apply measurableSet_setOfPred.mpr
    apply Measurable.forall; intro j
    apply Measurable.imp
    · exact measurableSet_setOfPred.mp (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i))
    · exact measurableSet_setOfPred.mp (measurableSet_le (pm_meas _ (measurable_pi_apply j))
        measurable_const)
  apply Measurable.ite hz
  · apply Measurable.ite (measurableSet_eq_fun (measurable_pi_apply i) measurable_const)
    · exact (card_meas (fun _ => 0) measurable_const).const_div 1
    · exact measurable_const
  · apply Measurable.ite (measurableSet_le (pm_meas _ (measurable_pi_apply i)) measurable_const)
    · exact psi_meas i
    · apply Measurable.ite hc
      · apply Measurable.div
        · apply Measurable.sub measurable_const
          simp only [Finset.sum_filter]
          apply Finset.measurable_sum; intro j _
          exact Measurable.ite (measurableSet_le (pm_meas _ (measurable_pi_apply j))
            measurable_const) (psi_meas j) measurable_const
        · exact card_meas _ (measurable_pi_apply i)
      · exact measurable_const

theorem pos_of_nozero {n : ℕ} (x : Fin n → ℝ) (hx : 0 ≤ x) (hz : ¬ ∃ j, x j = 0) (i : Fin n) :
    0 < x i := lt_of_le_of_ne (hx i) (fun h => hz ⟨i, h.symm⟩)

theorem bh_simplex {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : 0 ≤ x) :
    bottomHeavy n 1 x ∈ stdSimplex ℝ (Fin n) := by
  by_cases hz : ∃ j, x j = 0
  · exact ⟨bh_zero_nonneg x hz, bh_zero_sum x hz⟩
  · have hp := pos_of_nozero x hx hz
    obtain ⟨hψ, -, -⟩ := step_1 hn 1 zero_le_one le_rfl x hp
    exact ⟨bh_pos_nonneg x hp hψ, bh_pos_sum hn x hp⟩

theorem bh_cost_bound {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : 0 ≤ x) (i : Fin n) :
    0 ≤ bottomHeavy n 1 x i * x i ∧
      bottomHeavy n 1 x i * x i ≤ (∑ j, x j - x i) / ((n:ℝ) * ((n:ℝ) - 1)) := by
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hnpos : (0:ℝ) < n := by linarith
  have hrest : 0 ≤ ∑ j, x j - x i := by
    have := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i); linarith
  have hR : 0 ≤ (∑ j, x j - x i) / ((n:ℝ) * ((n:ℝ) - 1)) := by positivity
  have hsimp := bh_simplex hn x hx
  have h0 : 0 ≤ bottomHeavy n 1 x i * x i := mul_nonneg (hsimp.1 i) (hx i)
  refine ⟨h0, ?_⟩
  by_cases hz : ∃ j, x j = 0
  · rw [bh_zero_eq x hz]
    split_ifs with h
    · have hxi : x i = 0 := h
      rw [hxi, mul_zero]; rw [hxi] at hR; exact hR
    · rw [zero_mul]; exact hR
  · have hp := pos_of_nozero x hx hz
    obtain ⟨hψ, -, -⟩ := step_1 hn 1 zero_le_one le_rfl x hp
    have h1 : bottomHeavy n 1 x i * x i ≤ psi n 1 x i * x i :=
      mul_le_mul_of_nonneg_right (bh_pos_le_psi x hp hψ i) (hx i)
    have h2 : psi n 1 x i * x i = (∑ j, x j - x i) / ((n:ℝ) * ((n:ℝ) - 1)) := by
      unfold psi mean
      have := hp i
      field_simp
      ring
    linarith

theorem bh_fairshare {n : ℕ} (hn : 2 ≤ n) : FairShareBad (bottomHeavy n 1) := by
  intro μ hμ i
  obtain ⟨hprob, hnull, hint⟩ := hμ
  have hae : ∀ᵐ x ∂μ, 0 ≤ x := MeasureTheory.ae_iff.mpr hnull
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hnpos : (0:ℝ) < n := by linarith
  have hgi : MeasureTheory.Integrable
      (fun x : Fin n → ℝ => (∑ j, x j - x i) / ((n:ℝ) * ((n:ℝ) - 1))) μ := by
    apply MeasureTheory.Integrable.div_const
    apply MeasureTheory.Integrable.sub
    · exact MeasureTheory.integrable_finsetSum _ (fun j _ => (hint j).1)
    · exact (hint i).1
  have hle := MeasureTheory.integral_mono_of_nonneg
    (f := fun x => bottomHeavy n 1 x i * x i) (by filter_upwards [hae] with x hx using
      (bh_cost_bound hn x hx i).1) hgi (by filter_upwards [hae] with x hx using
      (bh_cost_bound hn x hx i).2)
  refine le_trans hle (le_of_eq ?_)
  rw [MeasureTheory.integral_div, MeasureTheory.integral_sub
    (MeasureTheory.integrable_finsetSum _ (fun j _ => (hint j).1)) (hint i).1,
    MeasureTheory.integral_finsetSum _ (fun j _ => (hint j).1)]
  simp only [fun j => (hint j).2, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  field_simp

theorem phi_tie {n : ℕ} (ϕ : Rule n) (hsym : IsSymmetric ϕ) (x : Fin n → ℝ) (hx : 0 ≤ x)
    (i j : Fin n) (h : x i = x j) : ϕ x i = ϕ x j := by
  have := hsym (Equiv.swap i j) x hx i
  have hx' : (fun l => x ((Equiv.swap i j).symm l)) = x := by
    funext l
    rw [Equiv.symm_swap, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, h]
    · rw [h2, h]
    · rfl
  rw [hx', Equiv.swap_apply_left] at this
  exact this.symm

end Bads17Aux

open Bads17Aux in
theorem solution {n : ℕ} (hn : 2 ≤ n) :
    (IsAPIRule (bottomHeavy n 1) ∧ IsSymmetric (bottomHeavy n 1) ∧
        FairShareBad (bottomHeavy n 1)) ∧
      ∀ ϕ : Rule n, IsAPIRule ϕ → IsSymmetric ϕ → FairShareBad ϕ →
        (∃ x : Fin n → ℝ, 0 ≤ x ∧ ϕ x ≠ bottomHeavy n 1 x) →
        DominatesBad (bottomHeavy n 1) ϕ := by
  refine ⟨⟨⟨bh_meas, fun x hx => bh_simplex hn x hx⟩, ?_, bh_fairshare hn⟩, ?_⟩
  · intro π x _ i
    rw [bh_perm π.symm x (π i), Equiv.symm_apply_apply]
  intro ϕ hϕ hsym hfs ⟨x0, hx0, hne⟩
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hnpos : (0:ℝ) < n := by linarith
  obtain ⟨δ, hδ0, hδ⟩ := prop_14_delta hn ϕ hϕ hsym hfs
  have hδ1 : δ ≤ 1 / ((n:ℝ) - 1) := by
    set i0 : Fin n := ⟨0, by omega⟩
    set e : Fin n → ℝ := fun j => if j = i0 then 1 else 0 with he
    have he0 : 0 ≤ e := fun j => by simp only [e]; split_ifs <;> norm_num
    have hei : 0 < e i0 := by simp [e]
    have h := hδ e he0 i0 hei
    have hm : mean e = 1 / n := by
      unfold mean; simp [e]
    have hϕ0 : 0 ≤ ϕ e i0 := (hϕ.2 e he0).1 i0
    rw [hm] at h
    simp only [e, if_pos rfl, div_one] at h
    rw [le_div_iff₀ hn1]
    have : 0 ≤ 1 / (n:ℝ) + δ * (1 / n - 1) := le_trans hϕ0 h
    have h2 : 0 ≤ 1 + δ * (1 - n) := by
      have := mul_nonneg hnpos.le this
      have e1 : (n:ℝ) * (1 / n + δ * (1 / n - 1)) = 1 + δ * (1 - n) := by field_simp
      linarith
    nlinarith
  have hpre : ∀ x : Fin n → ℝ, 0 ≤ x → ∀ k,
      pre x (ϕ x) (x k) ≤ pre x (bottomHeavy n 1 x) (x k) := by
    intro x hx k
    have hps := hϕ.2 x hx
    by_cases hz : ∃ j, x j = 0
    · rw [pre_full x _ (bh_zero_sum x hz) (x k) (fun j hj => by
        rw [bh_zero_eq x hz, if_neg]; intro h0; have : (0:ℝ) ≤ x k := hx k; linarith)]
      exact pre_le_one x _ hps.1 hps.2 _
    · have hp := pos_of_nozero x hx hz
      obtain ⟨hψ, -, -⟩ := step_1 hn 1 zero_le_one le_rfl x hp
      by_cases hS : prefixMass n 1 x (x k) ≤ 1
      · have hq : pre x (bottomHeavy n 1 x) (x k) = prefixMass n 1 x (x k) := by
          unfold pre prefixMass
          apply Finset.sum_congr rfl
          intro j hj
          have hjk : x j ≤ x k := (Finset.mem_filter.mp hj).2
          rw [bh_pos_eq x hp j, if_pos (le_trans (S_mono x hψ hjk) hS)]
        rw [hq]
        refine le_trans ?_ (pre_psi hn x hp δ hδ1 k)
        unfold pre
        exact Finset.sum_le_sum (fun j _ => hδ x hx j (hp j))
      · rw [pre_full x _ (bh_pos_sum hn x hp) (x k) (fun j hj => by
          rw [bh_pos_eq x hp j, if_neg (fun h => hS (le_trans (S_mono x hψ hj.le) h)), if_neg]
          intro h; exact hS (h k hj))]
        exact pre_le_one x _ hps.1 hps.2 _
  refine ⟨fun x hx => ?_, ⟨x0, hx0, ?_⟩⟩
  · unfold cost
    exact dom_le x (ϕ x) (bottomHeavy n 1 x) (hϕ.2 x hx).2 (bh_simplex hn x hx).2 (hpre x hx)
  · unfold cost
    exact dom_lt x0 (ϕ x0) (bottomHeavy n 1 x0) (hϕ.2 x0 hx0).2 (bh_simplex hn x0 hx0).2
      (hpre x0 hx0) (fun i j h => phi_tie ϕ hsym x0 hx0 i j h)
      (fun i j h => bh_tie 1 x0 i j h) hne
