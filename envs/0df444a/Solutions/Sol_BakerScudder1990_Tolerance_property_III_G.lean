-- Prove2me | solution 1 for BakerScudder1990.Tolerance.property_III_G
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T11:28:12.800127+00:00
-- url     : https://prove2.me/submissions/c815a369-f56c-4181-8f68-86948fe5d41b

import Mathlib
import Definitions.Def_BakerScudder1990_Tolerance_Instance



namespace BakerScudder1990.Tolerance

open Instance

lemma bs_window {n : ℕ} (I : Instance n) (i j : Fin n) (hij : i < j) :
    I.C i + I.u i < I.C j - I.v j := by
  have hsplit : I.C j = I.C i + ∑ l ∈ (Finset.univ.filter (fun l : Fin n => l ≤ j)).filter
      (fun l => ¬ l ≤ i), I.p l := by
    unfold Instance.C
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (fun l : Fin n => l ≤ j))
      (fun l => l ≤ i)]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨le_trans h hij.le, h⟩
  have hpos : ∀ l ∈ (Finset.univ.filter (fun l : Fin n => l ≤ j)).filter (fun l => ¬ l ≤ i),
      0 ≤ I.p l := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hl
    have := I.htol i l (ne_of_lt hl.2)
    linarith [I.hu i, I.hv l]
  have hjmem : j ∈ (Finset.univ.filter (fun l : Fin n => l ≤ j)).filter (fun l => ¬ l ≤ i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]; exact ⟨le_rfl, hij⟩
  have h1 := Finset.single_le_sum hpos hjmem
  have h2 := I.htol i j (ne_of_lt hij)
  linarith

/-- per-job penalty -/
noncomputable def bs_term {n : ℕ} (I : Instance n) (d : ℝ) (j : Fin n) : ℝ :=
  I.α j * I.earliness d j + I.β j * I.tardiness d j

lemma bs_cost_eq {n : ℕ} (I : Instance n) (d : ℝ) : I.cost d = ∑ j, bs_term I d j := rfl

lemma bs_tE (a b c u v d d' : ℝ) (ha : 0 < a) (hb : 0 < b) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : c + u ≤ d) :
    a * (d' - d) ≤ (a * max 0 (d' - c - u) + b * max 0 (c - d' - v)) -
      (a * max 0 (d - c - u) + b * max 0 (c - d - v)) := by
  rw [max_eq_right (by linarith : (0:ℝ) ≤ d - c - u), max_eq_left (by linarith : c - d - v ≤ 0)]
  have h1 := le_max_right 0 (d' - c - u)
  have h2 := le_max_left 0 (c - d' - v)
  nlinarith

lemma bs_tT (a b c u v d d' : ℝ) (ha : 0 < a) (hb : 0 < b) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : d ≤ c - v) :
    -b * (d' - d) ≤ (a * max 0 (d' - c - u) + b * max 0 (c - d' - v)) -
      (a * max 0 (d - c - u) + b * max 0 (c - d - v)) := by
  rw [max_eq_left (by linarith : d - c - u ≤ 0), max_eq_right (by linarith : (0:ℝ) ≤ c - d - v)]
  have h1 := le_max_left 0 (d' - c - u)
  have h2 := le_max_right 0 (c - d' - v)
  nlinarith

lemma bs_tM1 (a b c u v d d' s : ℝ) (ha : 0 < a) (hb : 0 < b) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : d = c - v) (hs1 : -b ≤ s) (hs2 : s ≤ 0) :
    s * (d' - d) ≤ (a * max 0 (d' - c - u) + b * max 0 (c - d' - v)) -
      (a * max 0 (d - c - u) + b * max 0 (c - d - v)) := by
  subst h
  rw [max_eq_left (by linarith : c - v - c - u ≤ 0), max_eq_left (by linarith : c - (c - v) - v ≤ 0)]
  have h1 := le_max_left 0 (d' - c - u)
  have h2 := le_max_left 0 (c - d' - v)
  have h3 := le_max_right 0 (c - d' - v)
  rcases le_total d' (c - v) with hd | hd
  · nlinarith
  · nlinarith

lemma bs_tM2 (a b c u v d d' s : ℝ) (ha : 0 < a) (hb : 0 < b) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : d = c + u) (hs1 : 0 ≤ s) (hs2 : s ≤ a) :
    s * (d' - d) ≤ (a * max 0 (d' - c - u) + b * max 0 (c - d' - v)) -
      (a * max 0 (d - c - u) + b * max 0 (c - d - v)) := by
  subst h
  rw [max_eq_left (by linarith : c + u - c - u ≤ 0), max_eq_left (by linarith : c - (c + u) - v ≤ 0)]
  have h1 := le_max_left 0 (d' - c - u)
  have h2 := le_max_left 0 (c - d' - v)
  have h3 := le_max_right 0 (d' - c - u)
  rcases le_total d' (c + u) with hd | hd
  · nlinarith
  · nlinarith

lemma bs_lower {n : ℕ} (I : Instance n) (k : Fin n) (d s : ℝ)
    (hlo : I.C k - I.v k ≤ d) (hhi : d ≤ I.C k + I.u k)
    (hk : ∀ d', s * (d' - d) ≤ bs_term I d' k - bs_term I d k) (d' : ℝ) :
    ((∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) -
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) + s) * (d' - d) ≤
      I.cost d' - I.cost d := by
  rw [bs_cost_eq, bs_cost_eq, ← Finset.sum_sub_distrib, Finset.sum_filter, Finset.sum_filter]
  have key : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      ((if j < k then I.α j else 0) - (if k < j then I.β j else 0) + (if j = k then s else 0))
        * (d' - d) ≤ bs_term I d' j - bs_term I d j := by
    intro j _
    rcases lt_trichotomy j k with hj | hj | hj
    · have hw := bs_window I j k hj
      simp only [hj, if_true, not_lt.mpr hj.le, if_false, ne_of_lt hj, sub_zero, add_zero]
      exact bs_tE _ _ _ _ _ _ _ (I.hα j) (I.hβ j) (I.hu j) (I.hv j) (by linarith)
    · subst hj
      simp only [lt_irrefl, if_false, if_true, sub_zero, zero_add]
      exact hk d'
    · have hw := bs_window I k j hj
      simp only [hj, if_true, not_lt.mpr hj.le, if_false, (ne_of_lt hj).symm, zero_sub, add_zero]
      exact bs_tT _ _ _ _ _ _ _ (I.hα j) (I.hβ j) (I.hu j) (I.hv j) (by linarith)
  refine le_trans ?_ (Finset.sum_le_sum key)
  rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp

lemma bs_ge_split {n : ℕ} (f : Fin n → ℝ) (k : Fin n) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i), f i) =
      f k + ∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), f i := by
  have : Finset.univ.filter (fun i : Fin n => k ≤ i) =
      insert k (Finset.univ.filter (fun i : Fin n => k < i)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h; rcases eq_or_lt_of_le h with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact h ▸ le_rfl
      · exact h.le
  rw [this, Finset.sum_insert (by simp)]

lemma bs_le_split {n : ℕ} (f : Fin n → ℝ) (k : Fin n) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ k), f i) =
      f k + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), f i := by
  have : Finset.univ.filter (fun i : Fin n => i ≤ k) =
      insert k (Finset.univ.filter (fun i : Fin n => i < k)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h; rcases eq_or_lt_of_le h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact h ▸ le_rfl
      · exact h.le
  rw [this, Finset.sum_insert (by simp)]

theorem bs_opt_core {n : ℕ} (I : Instance n) (k : Fin n) :
    ((∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) <
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i), I.β i) ∧
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ≤
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) →
      I.IsLeastOptimalDueDate (I.C k - I.v k)) ∧
    ((∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) <
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ∧
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ≤
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ k), I.α i) →
      I.IsLeastOptimalDueDate (I.C k + I.u k)) := by
  rw [bs_ge_split, bs_le_split]
  set A := ∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i
  set B := ∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i
  have hlo1 : I.C k - I.v k ≤ I.C k - I.v k := le_rfl
  have hhi1 : I.C k - I.v k ≤ I.C k + I.u k := by linarith [I.hu k, I.hv k]
  have hlo2 : I.C k - I.v k ≤ I.C k + I.u k := hhi1
  have hhi2 : I.C k + I.u k ≤ I.C k + I.u k := le_rfl
  constructor
  · rintro ⟨h1, h2⟩
    have hk : ∀ s, -I.β k ≤ s → s ≤ 0 → ∀ d', s * (d' - (I.C k - I.v k)) ≤
        bs_term I d' k - bs_term I (I.C k - I.v k) k := by
      intro s hs1 hs2 d'
      exact bs_tM1 _ _ _ _ _ _ _ _ (I.hα k) (I.hβ k) (I.hu k) (I.hv k) rfl hs1 hs2
    constructor
    · intro d'
      have := bs_lower I k _ (-(A - B)) hlo1 hhi1 (hk _ (by linarith) (by linarith)) d'
      have e : (A - B + -(A - B)) = 0 := by ring
      rw [e, zero_mul] at this; linarith
    · intro d' hd'
      by_contra hlt; push_neg at hlt
      have := bs_lower I k _ (-I.β k) hlo1 hhi1 (hk _ le_rfl (by linarith [I.hβ k])) d'
      have h3 := hd' (I.C k - I.v k)
      have : 0 < (A - B + -I.β k) * (d' - (I.C k - I.v k)) :=
        mul_pos_of_neg_of_neg (by linarith) (by linarith)
      linarith
  · rintro ⟨h1, h2⟩
    have hk : ∀ s, 0 ≤ s → s ≤ I.α k → ∀ d', s * (d' - (I.C k + I.u k)) ≤
        bs_term I d' k - bs_term I (I.C k + I.u k) k := by
      intro s hs1 hs2 d'
      exact bs_tM2 _ _ _ _ _ _ _ _ (I.hα k) (I.hβ k) (I.hu k) (I.hv k) rfl hs1 hs2
    constructor
    · intro d'
      have := bs_lower I k _ (B - A) hlo2 hhi2 (hk _ (by linarith) (by linarith)) d'
      have e : (A - B + (B - A)) = 0 := by ring
      rw [e, zero_mul] at this; linarith
    · intro d' hd'
      by_contra hlt; push_neg at hlt
      have := bs_lower I k _ 0 hlo2 hhi2 (hk _ le_rfl (I.hα k).le) d'
      have h3 := hd' (I.C k + I.u k)
      have : 0 < (A - B + 0) * (d' - (I.C k + I.u k)) :=
        mul_pos_of_neg_of_neg (by linarith) (by linarith)
      linarith

lemma bs_exists_k {n : ℕ} (I : Instance n) (hn : 0 < n) :
    ∃ k : Fin n, (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) <
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i), I.β i) ∧
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ≤
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ k), I.α i) := by
  classical
  let P : ℕ → Prop := fun m => ∃ h : m < n,
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => (⟨m, h⟩ : Fin n) < i), I.β i) ≤
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ ⟨m, h⟩), I.α i)
  have hex : ∃ m, P m := by
    refine ⟨n - 1, by omega, ?_⟩
    have h0 : (∑ i ∈ Finset.univ.filter (fun i : Fin n => (⟨n - 1, by omega⟩ : Fin n) < i), I.β i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hi
      omega
    rw [h0]
    exact Finset.sum_nonneg (fun i _ => (I.hα i).le)
  obtain ⟨hlt, hP⟩ := Nat.find_spec hex
  refine ⟨⟨Nat.find hex, hlt⟩, ?_, hP⟩
  by_cases h0 : Nat.find hex = 0
  · have e1 : (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < ⟨Nat.find hex, hlt⟩), I.α i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hi
      omega
    rw [e1]
    apply Finset.sum_pos (fun i _ => I.hβ i)
    exact ⟨⟨Nat.find hex, hlt⟩, by simp⟩
  · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    simp only [P, not_exists, not_le] at hmin
    have := hmin (by omega)
    have e1 : Finset.univ.filter (fun i : Fin n => i < ⟨Nat.find hex, hlt⟩) =
        Finset.univ.filter (fun i : Fin n => i ≤ ⟨Nat.find hex - 1, by omega⟩) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def]
      omega
    have e2 : Finset.univ.filter (fun i : Fin n => (⟨Nat.find hex, hlt⟩ : Fin n) ≤ i) =
        Finset.univ.filter (fun i : Fin n => (⟨Nat.find hex - 1, by omega⟩ : Fin n) < i) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def]
      omega
    rw [e1, e2]; exact this

lemma bs_card {n : ℕ} (I : Instance n) (k : Fin n) (d : ℝ)
    (hlo : I.C k - I.v k ≤ d) (hhi : d ≤ I.C k + I.u k) :
    (Finset.univ.filter (fun j : Fin n => I.tardiness d j = 0)).card = k.val + 1 := by
  have : Finset.univ.filter (fun j : Fin n => I.tardiness d j = 0) = Finset.Iic k := by
    ext j
    rw [Finset.mem_filter, Finset.mem_Iic]
    simp only [Finset.mem_univ, true_and]
    unfold Instance.tardiness
    rw [max_eq_left_iff]
    constructor
    · intro h
      by_contra hc; push_neg at hc
      have := bs_window I k j hc
      linarith
    · intro h
      rcases eq_or_lt_of_le h with h | h
      · subst h; linarith
      · have := bs_window I j k h
        linarith [I.hu j, I.hv j]
  rw [this, Fin.card_Iic]

lemma bs_unique {n : ℕ} (I : Instance n) (d d' : ℝ) (h : I.IsLeastOptimalDueDate d)
    (h' : I.IsLeastOptimalDueDate d') : d = d' :=
  le_antisymm (h.2 d' h'.1) (h'.2 d h.1)

theorem bs_IV_core {n : ℕ} (I : Instance n) (hn : 0 < n) :
    (∃ d : ℝ, I.IsLeastOptimalDueDate d) ∧
      ∀ d : ℝ, I.IsLeastOptimalDueDate d →
        ∃ k : Fin n,
          (Finset.univ.filter (fun j : Fin n => I.tardiness d j = 0)).card = k.val + 1 ∧
          ((I.C k = d + I.v k ∧
              (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) <
                (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i), I.β i) ∧
              (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ≤
                (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i)) ∨
           (I.C k = d - I.u k ∧
              (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) <
                (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ∧
              (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ≤
                (∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ k), I.α i))) := by
  obtain ⟨k, h1, h2⟩ := bs_exists_k I hn
  have hw : I.C k - I.v k ≤ I.C k + I.u k := by linarith [I.hu k, I.hv k]
  by_cases hc : (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ≤
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i)
  · have hL := (bs_opt_core I k).1 ⟨h1, hc⟩
    refine ⟨⟨_, hL⟩, fun d hd => ?_⟩
    have := bs_unique I _ _ hL hd
    subst this
    exact ⟨k, bs_card I k _ le_rfl hw, Or.inl ⟨by ring, h1, hc⟩⟩
  · push_neg at hc
    have hL := (bs_opt_core I k).2 ⟨hc, h2⟩
    refine ⟨⟨_, hL⟩, fun d hd => ?_⟩
    have := bs_unique I _ _ hL hd
    subst this
    exact ⟨k, bs_card I k _ hw le_rfl, Or.inr ⟨by ring, hc, h2⟩⟩

theorem bs_III_core {n : ℕ} (I : Instance n) (hn : 0 < n) :
    (∃ d : ℝ, I.IsLeastOptimalDueDate d) ∧
      ∀ d : ℝ, I.IsLeastOptimalDueDate d →
        ∃ k : Fin n, I.C k = d - I.u k ∨ I.C k = d + I.v k := by
  refine ⟨(bs_IV_core I hn).1, fun d hd => ?_⟩
  obtain ⟨k, -, h | h⟩ := (bs_IV_core I hn).2 d hd
  · exact ⟨k, Or.inr h.1⟩
  · exact ⟨k, Or.inl h.1⟩

end BakerScudder1990.Tolerance

open BakerScudder1990.Tolerance


theorem solution {n : ℕ} (I : Instance n) (hn : 0 < n) :
    (∃ d : ℝ, I.IsLeastOptimalDueDate d) ∧
      ∀ d : ℝ, I.IsLeastOptimalDueDate d →
        ∃ k : Fin n, I.C k = d - I.u k ∨ I.C k = d + I.v k := by
  exact bs_III_core I hn
