-- Prove2me | solution 1 for Erdos195.adenwalla_fiveAP_free
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T21:24:10.010029+00:00
-- url     : https://prove2.me/submissions/5198b16c-ae08-4709-8db3-8030b1b01c07

import Mathlib
import Definitions.Def_Erdos195_defs

-- Formalizes the construction of Adenwalla (5-AP-free permutation of Z, Theorem 1).

namespace Erdos195


/-- DEGS-type lower bound, proved directly over ℤ: every bijection `ℕ ≃ ℤ` has an increasing
monotone 3-AP `f 0, f m, 2 f m - f 0` where `m` is the first index with `f m > f 0`. -/
theorem degs_three_ap (f : ℕ ≃ ℤ) : HasMonotoneAP f 3 := by
  classical
  have hex : ∃ n, f 0 < f n := ⟨f.symm (f 0 + 1), by simp⟩
  set m := Nat.find hex with hm
  have hfm : f 0 < f m := Nat.find_spec hex
  have hbelow : ∀ i, 0 < i → i < m → f i < f 0 := by
    intro i hi him
    have h1 : ¬ f 0 < f i := Nat.find_min hex him
    have h2 : f i ≠ f 0 := by
      intro h; have := f.injective h; omega
    omega
  set j := f.symm (2 * f m - f 0) with hj
  have hfj : f j = 2 * f m - f 0 := by simp [hj]
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hfm; exact absurd hfm (lt_irrefl _)
    · exact h
  have hmj : m < j := by
    by_contra hcon
    push Not at hcon
    rcases Nat.lt_or_ge j m with h | h
    · rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0] at hfj; omega
      · have := hbelow j h0 h; omega
    · have : j = m := le_antisymm hcon h
      rw [this] at hfj; omega
  refine ⟨[0, m, j], ⟨f 0, f m - f 0, Or.inl ?_⟩, ?_⟩
  · simp [List.range_succ, hfj]
    ring
  · simp [List.pairwise_cons]
    omega



/-- Dropping one term: a monotone `(k+1)`-AP yields a monotone `k`-AP. -/
theorem hasMonotoneAP_of_succ {α β : Type*} [AddCommMonoid α] [Preorder β] (f : β → α) (k : ℕ)
    (h : HasMonotoneAP f (k + 1)) : HasMonotoneAP f k := by
  obtain ⟨l, ⟨a, d, hl | hl⟩, hp⟩ := h
  · refine ⟨l.dropLast, ⟨a, d, Or.inl ?_⟩, hp.sublist (List.dropLast_sublist l)⟩
    have h' := congrArg List.dropLast hl
    rw [List.range_succ, List.map_append, List.map_singleton, List.dropLast_concat] at h'
    rw [← h']
    simp [List.map_dropLast]
  · refine ⟨l.tail, ⟨a, d, Or.inr ?_⟩, hp.sublist (List.tail_sublist l)⟩
    have h' := congrArg List.tail hl
    rw [List.range_succ, List.reverse_append, List.map_append] at h'
    simpa [List.map_tail] using h'

theorem hasMonotoneAP_mono {α β : Type*} [AddCommMonoid α] [Preorder β] (f : β → α) {j k : ℕ}
    (hjk : j ≤ k) (h : HasMonotoneAP f k) : HasMonotoneAP f j := by
  induction k, hjk using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih (hasMonotoneAP_of_succ f n h)

/-- Reduction, assuming both bounds `3 ≤ K ≤ 4` as hypotheses. -/
theorem answer_eq_three_iff_of_bounds
    (h3 : ∀ f : ℕ ≃ ℤ, HasMonotoneAP f 3) (h5 : ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAP f 5) :
    sSup {k : ℕ | ∀ f : ℕ ≃ ℤ, HasMonotoneAP f k} = 3 ↔ ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAP f 4 := by
  set S := {k : ℕ | ∀ f : ℕ ≃ ℤ, HasMonotoneAP f k} with hS
  obtain ⟨g, hg⟩ := h5
  have hle : ∀ k ∈ S, k ≤ 4 := by
    intro k hk
    by_contra hk4
    exact hg (hasMonotoneAP_mono g (by omega) (hk g))
  have hbdd : BddAbove S := ⟨4, hle⟩
  have h3S : (3 : ℕ) ∈ S := h3
  by_cases h4 : (4 : ℕ) ∈ S
  · have : 4 ≤ sSup S := le_csSup hbdd h4
    constructor
    · intro h; omega
    · rintro ⟨f, hf⟩; exact absurd (h4 f) hf
  · have hle3 : ∀ k ∈ S, k ≤ 3 := by
      intro k hk
      by_contra hk3
      exact h4 (fun f => hasMonotoneAP_mono f (by omega) (hk f))
    have hsup : sSup S = 3 := le_antisymm (csSup_le ⟨3, h3S⟩ hle3) (le_csSup hbdd h3S)
    refine ⟨fun _ => ?_, fun _ => hsup⟩
    by_contra hne
    push Not at hne
    exact h4 hne

/-- Reduction with the DEGS lower bound discharged: only the upper bound (a 5-AP-free
permutation of ℤ, Adenwalla 2024) remains as a hypothesis. -/
theorem answer_eq_three_iff_of_fiveAP_free (h5 : ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAP f 5) :
    sSup {k : ℕ | ∀ f : ℕ ≃ ℤ, HasMonotoneAP f k} = 3 ↔ ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAP f 4 :=
  answer_eq_three_iff_of_bounds degs_three_ap h5

end Erdos195


namespace Adenwalla

def rk (p : Bool) (x : ZMod 8) : Fin 8 :=
  match p with
  | true => ![0, 4, 2, 6, 1, 5, 3, 7] x
  | false => ![7, 3, 5, 1, 6, 2, 4, 0] x

theorem rk_injective (p : Bool) : Function.Injective (rk p) := by
  cases p <;> decide

def X1 : List ℤ := [-8, -4, 4, -6, 2, -2, 6, -7, 1, -3, 5, -5, 3, 7]

/-- Level-(n+1) block as a set: [-8^(n+1), -8^n - 1] ∪ [8^n, 8^(n+1) - 1]. -/
noncomputable def S (n : ℕ) : Finset ℤ :=
  Finset.Icc (-(8:ℤ)^(n+1)) (-(8:ℤ)^n - 1) ∪ Finset.Ico ((8:ℤ)^n) ((8:ℤ)^(n+1))

theorem mem_S {n : ℕ} {z : ℤ} :
    z ∈ S n ↔ (-(8:ℤ)^(n+1) ≤ z ∧ z ≤ -(8:ℤ)^n - 1) ∨ ((8:ℤ)^n ≤ z ∧ z < (8:ℤ)^(n+1)) := by
  simp [S]

theorem div8_mem_S {n : ℕ} {z : ℤ} (h : z ∈ S (n+1)) : z / 8 ∈ S n := by
  rw [mem_S] at h ⊢
  have e1 : (8:ℤ)^(n+1) = 8 * 8^n := by ring
  have e2 : (8:ℤ)^(n+1+1) = 64 * 8^n := by ring
  rw [e2, e1] at h
  rw [e1]
  have : (0:ℤ) < 8^n := by positivity
  omega

def rankAux : ℕ → ℤ → ℕ
  | 0, z => X1.idxOf z
  | n + 1, z => (rk (n % 2 == 1) (z : ZMod 8)).val * (14 * 8 ^ n) + rankAux n (z / 8)

theorem S_zero : S 0 = {-8, -7, -6, -5, -4, -3, -2, 1, 2, 3, 4, 5, 6, 7} := by decide

theorem rankAux_lt : ∀ (n : ℕ) (z : ℤ), z ∈ S n → rankAux n z < 14 * 8 ^ n
  | 0, z, h => by
      rw [S_zero] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide
  | n + 1, z, h => by
      have ih := rankAux_lt n (z / 8) (div8_mem_S h)
      have hr := (rk (n % 2 == 1) (z : ZMod 8)).isLt
      simp only [rankAux]
      have : (rk (n % 2 == 1) (z : ZMod 8)).val * (14 * 8 ^ n) ≤ 7 * (14 * 8 ^ n) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [pow_succ]; omega

theorem rankAux_inj : ∀ (n : ℕ) (z w : ℤ), z ∈ S n → w ∈ S n → rankAux n z = rankAux n w → z = w
  | 0, z, w, hz, hw, h => by
      rw [S_zero] at hz hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz hw
      simp only [rankAux] at h
      rcases hz with hz|hz|hz|hz|hz|hz|hz|hz|hz|hz|hz|hz|hz|hz <;> subst hz <;>
      rcases hw with hw|hw|hw|hw|hw|hw|hw|hw|hw|hw|hw|hw|hw|hw <;> subst hw <;> revert h <;> decide
  | n + 1, z, w, hz, hw, h => by
      have bz := rankAux_lt n (z / 8) (div8_mem_S hz)
      have bw := rankAux_lt n (w / 8) (div8_mem_S hw)
      simp only [rankAux] at h
      set M := 14 * 8 ^ n with hM
      set a := (rk (n % 2 == 1) (z : ZMod 8)).val
      set b := (rk (n % 2 == 1) (w : ZMod 8)).val
      have hMpos : 0 < M := by positivity
      have ha : a = b := by
        have h1 : (a * M + rankAux n (z / 8)) / M = a := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hMpos, Nat.div_eq_of_lt bz, zero_add]
        have h2 : (b * M + rankAux n (w / 8)) / M = b := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hMpos, Nat.div_eq_of_lt bw, zero_add]
        rw [← h1, ← h2, h]
      have hq : rankAux n (z / 8) = rankAux n (w / 8) := by rw [ha] at h; omega
      have hq' := rankAux_inj n _ _ (div8_mem_S hz) (div8_mem_S hw) hq
      have hres : (z : ZMod 8) = (w : ZMod 8) := rk_injective _ (Fin.ext ha)
      rw [ZMod.intCast_eq_intCast_iff'] at hres
      simp only [Nat.cast_ofNat] at hres
      omega


theorem card_S (n : ℕ) : (S n).card = 14 * 8 ^ n := by
  have hdisj : Disjoint (Finset.Icc (-(8:ℤ)^(n+1)) (-(8:ℤ)^n - 1)) (Finset.Ico ((8:ℤ)^n) ((8:ℤ)^(n+1))) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Icc, Finset.mem_Ico] at hx hx'
    have : (0:ℤ) < 8^n := by positivity
    omega
  rw [S, Finset.card_union_of_disjoint hdisj, Int.card_Icc, Int.card_Ico]
  have e1 : (8:ℤ)^(n+1) = 8 * 8^n := by ring
  rw [e1]
  have hc : ((8 ^ n : ℕ) : ℤ) = (8:ℤ)^n := by push_cast; rfl
  rw [← hc]
  omega

theorem rankAux_surj (n : ℕ) (m : ℕ) (hm : m < 14 * 8 ^ n) : ∃ z ∈ S n, rankAux n z = m := by
  have := Finset.surj_on_of_inj_on_of_card_le (s := S n) (t := Finset.range (14 * 8 ^ n))
    (fun z _ => rankAux n z) (fun z hz => Finset.mem_range.2 (rankAux_lt n z hz))
    (fun z w hz hw h => rankAux_inj n z w hz hw h) (by rw [card_S, Finset.card_range])
    m (Finset.mem_range.2 hm)
  obtain ⟨z, hz, h⟩ := this
  exact ⟨z, hz, h.symm⟩

/-- every integer other than 0, -1 lies in exactly one block. -/
theorem S_disjoint {n m : ℕ} {z : ℤ} (hn : z ∈ S n) (hm : z ∈ S m) : n = m := by
  rw [mem_S] at hn hm
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : (8:ℤ)^(n+1) ≤ 8^m := pow_le_pow_right₀ (by norm_num) h
    omega
  · have : (8:ℤ)^(m+1) ≤ 8^n := pow_le_pow_right₀ (by norm_num) h
    omega

theorem exists_S {z : ℤ} (h0 : z ≠ 0) (h1 : z ≠ -1) : ∃ n, z ∈ S n := by
  rcases le_or_gt 1 z with hz | hz
  · set k := z.toNat
    have hk : (k : ℤ) = z := Int.toNat_of_nonneg (by omega)
    have hk0 : k ≠ 0 := by omega
    refine ⟨Nat.log 8 k, ?_⟩
    have a := Nat.pow_log_le_self 8 hk0
    have b := Nat.lt_pow_succ_log_self (b := 8) (by norm_num) k
    rw [mem_S]; right
    constructor
    · rw [← hk]; exact_mod_cast a
    · rw [← hk]; exact_mod_cast b
  · set k := (-z - 1).toNat
    have hk : (k : ℤ) = -z - 1 := Int.toNat_of_nonneg (by omega)
    have hk0 : k ≠ 0 := by omega
    refine ⟨Nat.log 8 k, ?_⟩
    have a : ((8 ^ Nat.log 8 k : ℕ) : ℤ) ≤ k := by exact_mod_cast Nat.pow_log_le_self 8 hk0
    have b : (k : ℤ) < ((8 ^ (Nat.log 8 k).succ : ℕ) : ℤ) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (b := 8) (by norm_num) k
    push_cast at a b
    rw [mem_S]; left
    constructor <;> omega

open Classical in
noncomputable def lev (z : ℤ) : ℕ := if h : ∃ n, z ∈ S n then Nat.find h else 0

theorem lev_eq {n : ℕ} {z : ℤ} (h : z ∈ S n) : lev z = n := by
  classical
  have hex : ∃ n, z ∈ S n := ⟨n, h⟩
  unfold lev
  rw [dif_pos hex]
  exact S_disjoint (Nat.find_spec hex) h

theorem zero_not_mem_S (n : ℕ) : (0:ℤ) ∉ S n := by
  rw [mem_S]; have : (0:ℤ) < 8^n := by positivity
  omega

theorem neg_one_not_mem_S (n : ℕ) : (-1:ℤ) ∉ S n := by
  rw [mem_S]; have : (1:ℤ) ≤ 8^n := one_le_pow₀ (by norm_num)
  omega

/-- Position of integer z in Adenwalla's sequence 0, X1, -1, X2, X3, ... -/
noncomputable def pos (z : ℤ) : ℕ :=
  if z = 0 then 0 else if z = -1 then 15 else
  if lev z = 0 then 1 + rankAux 0 z else 2 * 8 ^ (lev z) + rankAux (lev z) z

theorem pos_of_mem_S0 {z : ℤ} (h : z ∈ S 0) : pos z = 1 + rankAux 0 z := by
  have h0 : z ≠ 0 := fun e => zero_not_mem_S 0 (e ▸ h)
  have h1 : z ≠ -1 := fun e => neg_one_not_mem_S 0 (e ▸ h)
  simp [pos, h0, h1, lev_eq h]

theorem pos_of_mem_S {n : ℕ} (hn : n ≠ 0) {z : ℤ} (h : z ∈ S n) :
    pos z = 2 * 8 ^ n + rankAux n z := by
  have h0 : z ≠ 0 := fun e => zero_not_mem_S n (e ▸ h)
  have h1 : z ≠ -1 := fun e => neg_one_not_mem_S n (e ▸ h)
  simp [pos, h0, h1, lev_eq h, hn]

/-- range of positions of each kind -/
theorem pos_range {z : ℤ} :
    (z = 0 ∧ pos z = 0) ∨ (z = -1 ∧ pos z = 15) ∨
    (z ∈ S 0 ∧ 1 ≤ pos z ∧ pos z ≤ 14) ∨
    (∃ n, n ≠ 0 ∧ z ∈ S n ∧ 2 * 8 ^ n ≤ pos z ∧ pos z < 16 * 8 ^ n) := by
  by_cases h0 : z = 0
  · left; exact ⟨h0, by simp [pos, h0]⟩
  by_cases h1 : z = -1
  · right; left; exact ⟨h1, by simp [pos, h1]⟩
  obtain ⟨n, hn⟩ := exists_S h0 h1
  rcases Nat.eq_zero_or_pos n with e | e
  · subst e
    right; right; left
    have := rankAux_lt 0 z hn
    simp only [pow_zero, mul_one] at this
    refine ⟨hn, ?_, ?_⟩ <;> rw [pos_of_mem_S0 hn] <;> omega
  · right; right; right
    have := rankAux_lt n z hn
    refine ⟨n, by omega, hn, ?_, ?_⟩ <;> rw [pos_of_mem_S (by omega) hn] <;> omega

theorem pos_inj_SS {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) {z w : ℤ} (hz : z ∈ S n) (hw : w ∈ S m)
    (pz1 : 2 * 8 ^ n ≤ pos z) (pz2 : pos z < 16 * 8 ^ n)
    (pw1 : 2 * 8 ^ m ≤ pos w) (pw2 : pos w < 16 * 8 ^ m) (h : pos z = pos w) : z = w := by
  have : n = m := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have : 8 ^ (n+1) ≤ 8 ^ m := Nat.pow_le_pow_right (by norm_num) hlt
      rw [pow_succ] at this; omega
    · have : 8 ^ (m+1) ≤ 8 ^ n := Nat.pow_le_pow_right (by norm_num) hlt
      rw [pow_succ] at this; omega
  subst this
  rw [pos_of_mem_S hn hz, pos_of_mem_S hn hw] at h
  exact rankAux_inj n z w hz hw (by omega)

theorem pos_injective : Function.Injective pos := by
  intro z w h
  rcases (pos_range (z := z)) with ⟨hz, pz⟩|⟨hz, pz⟩|⟨hz, pz1, pz2⟩|⟨n, hn, hz, pz1, pz2⟩ <;>
  rcases (pos_range (z := w)) with ⟨hw, pw⟩|⟨hw, pw⟩|⟨hw, pw1, pw2⟩|⟨m, hm, hw, pw1, pw2⟩
  all_goals first
    | (subst hz; subst hw; rfl)
    | omega
    | (rw [pos_of_mem_S0 hz, pos_of_mem_S0 hw] at h; exact rankAux_inj 0 z w hz hw (by omega))
    | (have : 8 ^ 1 ≤ 8 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega); omega)
    | (have : 8 ^ 1 ≤ 8 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega); omega)
    | exact pos_inj_SS hn hm hz hw pz1 pz2 pw1 pw2 h

theorem pos_surjective : Function.Surjective pos := by
  intro m
  by_cases m0 : m = 0
  · exact ⟨0, by simp [pos, m0]⟩
  by_cases m15 : m = 15
  · exact ⟨-1, by simp [pos, m15]⟩
  by_cases hsmall : m ≤ 14
  · obtain ⟨z, hz, hr⟩ := rankAux_surj 0 (m - 1) (by simp; omega)
    exact ⟨z, by rw [pos_of_mem_S0 hz, hr]; omega⟩
  · set k := m / 2
    have hk0 : k ≠ 0 := by omega
    obtain ⟨n, hn_eq⟩ : ∃ n, n = Nat.log 8 k := ⟨_, rfl⟩
    have a : 8 ^ n ≤ k := hn_eq ▸ Nat.pow_log_le_self 8 hk0
    have b : k < 8 ^ (n + 1) := hn_eq ▸ Nat.lt_pow_succ_log_self (b := 8) (by norm_num) k
    have hn : n ≠ 0 := by
      intro e
      rw [e, zero_add, pow_one] at b
      omega
    rw [pow_succ] at b
    obtain ⟨z, hz, hr⟩ := rankAux_surj n (m - 2 * 8 ^ n) (by omega)
    exact ⟨z, by rw [pos_of_mem_S hn hz, hr]; omega⟩

theorem pos_bijective : Function.Bijective pos := ⟨pos_injective, pos_surjective⟩

/-- Adenwalla's sequence as a bijection ℕ ≃ ℤ: `aden i` is the i-th term. -/
noncomputable def aden : ℕ ≃ ℤ := (Equiv.ofBijective pos pos_bijective).symm

theorem pos_aden (i : ℕ) : pos (aden i) = i :=
  Equiv.ofBijective_apply_symm_apply pos pos_bijective i

theorem aden_pos (z : ℤ) : aden (pos z) = z :=
  Equiv.ofBijective_symm_apply_apply pos pos_bijective z

end Adenwalla


namespace Adenwalla

theorem no3AP_mod8' (p : Bool) :
    ∀ x y z : ZMod 8, rk p x < rk p y → rk p y < rk p z → x + z ≠ 2 * y := by
  cases p <;> decide

theorem digit_le {a b M r s : ℕ} (hs : s < M) (h : a * M + r < b * M + s) :
    a ≤ b ∧ (a = b → r < s) := by
  constructor
  · by_contra hc
    have h1 : (b + 1) * M ≤ a * M := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, one_mul] at h1
    omega
  · intro e; subst e; omega

theorem X1_triples : ∀ i j k : Fin 14, i < j → j < k →
    X1.get ⟨i, by simp [X1]⟩ + X1.get ⟨k, by simp [X1]⟩ ≠ 2 * X1.get ⟨j, by simp [X1]⟩ := by
  decide

theorem S0_get {z : ℤ} (h : z ∈ S 0) : ∃ hi : rankAux 0 z < X1.length, X1.get ⟨rankAux 0 z, hi⟩ = z := by
  rw [S_zero] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> exact ⟨by decide, by decide⟩

/-- L4: each block X_{n+1} is 3AP-free in its position order. -/
theorem block_no3AP : ∀ (n : ℕ) (z w u : ℤ), z ∈ S n → w ∈ S n → u ∈ S n →
    rankAux n z < rankAux n w → rankAux n w < rankAux n u → z + u ≠ 2 * w
  | 0, z, w, u, hz, hw, hu, h1, h2 => by
      obtain ⟨iz, ez⟩ := S0_get hz
      obtain ⟨iw, ew⟩ := S0_get hw
      obtain ⟨iu, eu⟩ := S0_get hu
      have := X1_triples ⟨rankAux 0 z, iz⟩ ⟨rankAux 0 w, iw⟩ ⟨rankAux 0 u, iu⟩ h1 h2
      rw [ez, ew, eu] at this
      exact this
  | n + 1, z, w, u, hz, hw, hu, h1, h2 => by
      intro hap
      have bz := rankAux_lt n (z / 8) (div8_mem_S hz)
      have bw := rankAux_lt n (w / 8) (div8_mem_S hw)
      have bu := rankAux_lt n (u / 8) (div8_mem_S hu)
      simp only [rankAux] at h1 h2
      set p := (n % 2 == 1)
      obtain ⟨d1, e1⟩ := digit_le bw h1
      obtain ⟨d2, e2⟩ := digit_le bu h2
      have hmod : (z : ZMod 8) + (u : ZMod 8) = 2 * (w : ZMod 8) := by
        have := congrArg (fun t : ℤ => (t : ZMod 8)) hap
        push_cast at this; exact this
      have res_eq : ∀ a b : ℤ, (rk p (a : ZMod 8)).val = (rk p (b : ZMod 8)).val → a % 8 = b % 8 := by
        intro a b hab
        have hres : (a : ZMod 8) = (b : ZMod 8) := rk_injective _ (Fin.ext hab)
        rw [ZMod.intCast_eq_intCast_iff'] at hres
        simpa using hres
      have all_eq : z % 8 = w % 8 ∧ w % 8 = u % 8 → False := by
        rintro ⟨q1, q2⟩
        have r1 : (rk p (z : ZMod 8)).val = (rk p (w : ZMod 8)).val := by
          have : (z : ZMod 8) = (w : ZMod 8) := by
            rw [ZMod.intCast_eq_intCast_iff']; simpa using q1
          rw [this]
        have r2 : (rk p (w : ZMod 8)).val = (rk p (u : ZMod 8)).val := by
          have : (w : ZMod 8) = (u : ZMod 8) := by
            rw [ZMod.intCast_eq_intCast_iff']; simpa using q2
          rw [this]
        exact block_no3AP n (z / 8) (w / 8) (u / 8) (div8_mem_S hz) (div8_mem_S hw) (div8_mem_S hu)
          (e1 r1) (e2 r2) (by omega)
      rcases Nat.lt_or_eq_of_le d1 with l1 | q1
      · rcases Nat.lt_or_eq_of_le d2 with l2 | q2
        · exact no3AP_mod8' p _ _ _ (Fin.lt_def.2 l1) (Fin.lt_def.2 l2) hmod
        · have m2 := res_eq _ _ q2
          exact all_eq ⟨by omega, m2⟩
      · have m1 := res_eq _ _ q1
        exact all_eq ⟨m1, by omega⟩

end Adenwalla


namespace Adenwalla

theorem no4AP_cross_mod8' (p : Bool) :
    ∀ x y z w : ZMod 8, rk p x < rk p y → rk (!p) z < rk (!p) w →
      z - y = y - x → w - z = y - x → 2 * (y - x) = 0 := by
  cases p <;> decide

theorem rk_reverse' (p : Bool) :
    ∀ x y : ZMod 8, rk p x < rk p y → rk (!p) y < rk (!p) x := by
  cases p <;> decide

theorem cast8 {a b : ℤ} (h : a % 8 = b % 8) : (a : ZMod 8) = (b : ZMod 8) := by
  rw [ZMod.intCast_eq_intCast_iff']; simpa using h

theorem mod8_of_rk {p : Bool} {a b : ℤ} (h : (rk p (a : ZMod 8)).val = (rk p (b : ZMod 8)).val) :
    a % 8 = b % 8 := by
  have hres : (a : ZMod 8) = (b : ZMod 8) := rk_injective _ (Fin.ext h)
  rw [ZMod.intCast_eq_intCast_iff'] at hres
  simpa using hres

theorem rankAux_succ (n : ℕ) (z : ℤ) :
    rankAux (n+1) z = (rk (n % 2 == 1) (z : ZMod 8)).val * (14 * 8 ^ n) + rankAux n (z / 8) := rfl

theorem par_succ (n : ℕ) : ((n + 1) % 2 == 1) = !(n % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have : (n + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (n + 1) % 2 = 0 := by omega
    simp [h, this]

theorem mem_X1_of_S0 {z : ℤ} (h : z ∈ S 0) : z ∈ X1 := by
  rw [S_zero] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

theorem cross_base : ∀ z ∈ X1, ∀ w ∈ X1, rankAux 0 z < rankAux 0 w →
    ((-64 ≤ 2*w - z ∧ 2*w - z ≤ -9) ∨ (8 ≤ 2*w - z ∧ 2*w - z < 64)) →
    ((-64 ≤ 3*w - 2*z ∧ 3*w - 2*z ≤ -9) ∨ (8 ≤ 3*w - 2*z ∧ 3*w - 2*z < 64)) →
    ¬ rankAux 1 (2*w - z) < rankAux 1 (3*w - 2*z) := by
  decide

set_option maxRecDepth 20000 in
/-- L5: no 4-AP with first two terms (in order) in block X_{n+1} and last two in X_{n+2}. -/
theorem cross_no4AP : ∀ (n : ℕ) (z w x y : ℤ), z ∈ S n → w ∈ S n → x ∈ S (n+1) → y ∈ S (n+1) →
    rankAux n z < rankAux n w → rankAux (n+1) x < rankAux (n+1) y →
    x - w = w - z → y - x = w - z → False
  | 0, z, w, x, y, hz, hw, hx, hy, h1, h2, e1, e2 => by
      have hx' : x = 2*w - z := by omega
      have hy' : y = 3*w - 2*z := by omega
      subst hx' hy'
      rw [mem_S] at hx hy
      norm_num at hx hy
      exact cross_base z (mem_X1_of_S0 hz) w (mem_X1_of_S0 hw) h1 (by omega) (by omega) h2
  | n + 1, z, w, x, y, hz, hw, hx, hy, h1, h2, e1, e2 => by
      have bw := rankAux_lt n (w / 8) (div8_mem_S hw)
      have by' := rankAux_lt (n+1) (y / 8) (div8_mem_S hy)
      rw [rankAux_succ n z, rankAux_succ n w] at h1
      rw [rankAux_succ (n+1) x, rankAux_succ (n+1) y] at h2
      rw [par_succ] at h2
      set p := (n % 2 == 1)
      obtain ⟨d1, f1⟩ := digit_le bw h1
      obtain ⟨d2, f2⟩ := digit_le by' h2
      -- all residues equal: descend
      have descend : z % 8 = w % 8 → False := by
        intro q
        have qx : x % 8 = w % 8 := by omega
        have qy : y % 8 = x % 8 := by omega
        have r1 : (rk p (z : ZMod 8)).val = (rk p (w : ZMod 8)).val := by rw [cast8 q]
        have r2 : (rk (!p) (x : ZMod 8)).val = (rk (!p) (y : ZMod 8)).val := by rw [cast8 qy]
        exact cross_no4AP n (z / 8) (w / 8) (x / 8) (y / 8) (div8_mem_S hz) (div8_mem_S hw)
          (div8_mem_S hx) (div8_mem_S hy) (f1 r1) (f2 r2) (by omega) (by omega)
      rcases Nat.lt_or_eq_of_le d1 with l1 | q1
      · rcases Nat.lt_or_eq_of_le d2 with l2 | q2
        · have hm := no4AP_cross_mod8' p (z : ZMod 8) (w : ZMod 8) (x : ZMod 8) (y : ZMod 8)
            (Fin.lt_def.2 l1) (Fin.lt_def.2 l2)
            (by have := congrArg (fun t : ℤ => (t : ZMod 8)) e1; push_cast at this; exact this)
            (by have := congrArg (fun t : ℤ => (t : ZMod 8)) e2; push_cast at this; exact this)
          have hd : (8:ℤ) ∣ 2 * (w - z) := by
            have := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * (w - z)) 8).1 (by push_cast; exact hm)
            exact_mod_cast this
          by_cases h8 : z % 8 = w % 8
          · exact descend h8
          · -- d ≡ 4 mod 8: x ≡ z, y ≡ w, order reversed
            have qx : x % 8 = z % 8 := by omega
            have qy : y % 8 = w % 8 := by omega
            have rv := rk_reverse' p (z : ZMod 8) (w : ZMod 8) (Fin.lt_def.2 l1)
            rw [← cast8 qx, ← cast8 qy] at rv
            exact absurd (Fin.lt_def.1 rv) (by omega)
        · have := mod8_of_rk q2
          exact descend (by omega)
      · exact descend (mod8_of_rk q1)

end Adenwalla


namespace Adenwalla

theorem pos_lt_iff_rank {M : ℕ} {z w : ℤ} (hz : z ∈ S M) (hw : w ∈ S M) :
    pos z < pos w ↔ rankAux M z < rankAux M w := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · rw [pos_of_mem_S0 hz, pos_of_mem_S0 hw]; omega
  · rw [pos_of_mem_S (by omega) hz, pos_of_mem_S (by omega) hw]; omega

theorem blk {M : ℕ} {z w u : ℤ} (hz : z ∈ S M) (hw : w ∈ S M) (hu : u ∈ S M)
    (h1 : pos z < pos w) (h2 : pos w < pos u) (e : z + u = 2 * w) : False :=
  block_no3AP M z w u hz hw hu ((pos_lt_iff_rank hz hw).1 h1) ((pos_lt_iff_rank hw hu).1 h2) e

theorem crs {M : ℕ} {z w x y : ℤ} (hz : z ∈ S M) (hw : w ∈ S M) (hx : x ∈ S (M+1))
    (hy : y ∈ S (M+1)) (h1 : pos z < pos w) (h2 : pos x < pos y)
    (e1 : x - w = w - z) (e2 : y - x = w - z) : False :=
  cross_no4AP M z w x y hz hw hx hy ((pos_lt_iff_rank hz hw).1 h1) ((pos_lt_iff_rank hx hy).1 h2) e1 e2

theorem memS_K {M : ℕ} {K : ℤ} (hK : (8:ℤ)^M = K) {z : ℤ}
    (h : (-(8*K) ≤ z ∧ z ≤ -K - 1) ∨ (K ≤ z ∧ z < 8*K)) : z ∈ S M := by
  rw [mem_S, pow_succ, hK]; rcases h with h | h
  · left; constructor <;> linarith [h.1, h.2]
  · right; constructor <;> linarith [h.1, h.2]

theorem S_K {M : ℕ} {K : ℤ} (hK : (8:ℤ)^M = K) {z : ℤ} (h : z ∈ S M) :
    (-(8*K) ≤ z ∧ z ≤ -K - 1) ∨ (K ≤ z ∧ z < 8*K) := by
  rw [mem_S, pow_succ, hK] at h; rcases h with h | h
  · left; constructor <;> linarith [h.1, h.2]
  · right; constructor <;> linarith [h.1, h.2]

/-- P1: the first `2·8^m` positions (m ≥ 1) hold exactly `[-8^m, 8^m - 1]`. -/
theorem pos_lt_iff {m : ℕ} (hm : m ≠ 0) {z : ℤ} :
    pos z < 2 * 8 ^ m ↔ (-(8:ℤ)^m ≤ z ∧ z ≤ (8:ℤ)^m - 1) := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 8 ^ m = K := ⟨_, rfl⟩
  have hKi : (8:ℤ)^m = K := by exact_mod_cast hK
  have h8 : 8 ≤ K := by
    rw [← hK]; calc 8 = 8^1 := rfl
      _ ≤ 8^m := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hK, hKi]
  rcases (pos_range (z := z)) with ⟨hz, pz⟩|⟨hz, pz⟩|⟨hz, pz1, pz2⟩|⟨n, hn, hz, pz1, pz2⟩
  · subst hz; rw [pz]; omega
  · subst hz; rw [pz]; omega
  · have := S_K (M := 0) (K := 1) (by simp) hz
    omega
  · obtain ⟨L, hL⟩ : ∃ L : ℕ, 8 ^ n = L := ⟨_, rfl⟩
    have hLi : (8:ℤ)^n = L := by exact_mod_cast hL
    have hz' := S_K hLi hz
    rw [hL] at pz1 pz2
    rcases Nat.lt_or_ge n m with hnm | hnm
    · have : 8 ^ (n+1) ≤ 8 ^ m := Nat.pow_le_pow_right (by norm_num) hnm
      rw [pow_succ, hL, hK] at this
      omega
    · have : 8 ^ m ≤ 8 ^ n := Nat.pow_le_pow_right (by norm_num) hnm
      rw [hL, hK] at this
      omega

def L16 : List ℤ := 0 :: X1 ++ [-1]

theorem pos_small {z : ℤ} (h1 : -8 ≤ z) (h2 : z ≤ 7) : pos z = L16.idxOf z := by
  have hS : z ≠ 0 → z ≠ -1 → z ∈ S 0 := by
    intro a b; rw [S_zero]; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  by_cases a : z = 0
  · subst a; simp [pos]; decide
  by_cases b : z = -1
  · subst b; simp [pos]; decide
  rw [pos_of_mem_S0 (hS a b)]
  interval_cases z <;> first | (exfalso; omega) | decide

/-- finite check: positions < 16, five terms. -/
theorem F5 : ∀ x ∈ Finset.Icc (-8:ℤ) 7, ∀ d ∈ Finset.Icc (-3:ℤ) 3,
    -8 ≤ x + d → x + d ≤ 7 → -8 ≤ x + 2*d → x + 2*d ≤ 7 → -8 ≤ x + 3*d → x + 3*d ≤ 7 →
    -8 ≤ x + 4*d → x + 4*d ≤ 7 →
    L16.idxOf x < L16.idxOf (x+d) → L16.idxOf (x+d) < L16.idxOf (x+2*d) →
    L16.idxOf (x+2*d) < L16.idxOf (x+3*d) → L16.idxOf (x+3*d) < L16.idxOf (x+4*d) → False := by
  decide

/-- finite check: four terms in the first 16 positions, fifth in X2. -/
theorem F4 : ∀ x ∈ Finset.Icc (-8:ℤ) 7, ∀ d ∈ Finset.Icc (-5:ℤ) 5,
    -8 ≤ x + d → x + d ≤ 7 → -8 ≤ x + 2*d → x + 2*d ≤ 7 → -8 ≤ x + 3*d → x + 3*d ≤ 7 →
    L16.idxOf x < L16.idxOf (x+d) → L16.idxOf (x+d) < L16.idxOf (x+2*d) →
    L16.idxOf (x+2*d) < L16.idxOf (x+3*d) →
    ¬ ((-64 ≤ x + 4*d ∧ x + 4*d ≤ -9) ∨ (8 ≤ x + 4*d ∧ x + 4*d < 64)) := by
  decide

/-- finite check: three terms in the first 16 positions, last two in X2. -/
theorem F3 : ∀ x ∈ Finset.Icc (-8:ℤ) 7, ∀ d ∈ Finset.Icc (-7:ℤ) 7,
    -8 ≤ x + d → x + d ≤ 7 → -8 ≤ x + 2*d → x + 2*d ≤ 7 →
    L16.idxOf x < L16.idxOf (x+d) → L16.idxOf (x+d) < L16.idxOf (x+2*d) →
    ((-64 ≤ x + 3*d ∧ x + 3*d ≤ -9) ∨ (8 ≤ x + 3*d ∧ x + 3*d < 64)) →
    ((-64 ≤ x + 4*d ∧ x + 4*d ≤ -9) ∨ (8 ≤ x + 4*d ∧ x + 4*d < 64)) →
    ¬ rankAux 1 (x + 3*d) < rankAux 1 (x + 4*d) := by
  decide

end Adenwalla

namespace Adenwalla

/-- five terms all in the first 16 positions -/
theorem core_small (x d : ℤ) (h4 : pos (x + 4*d) < 16)
    (h01 : pos x < pos (x+d)) (h12 : pos (x+d) < pos (x+2*d))
    (h23 : pos (x+2*d) < pos (x+3*d)) (h34 : pos (x+3*d) < pos (x+4*d)) : False := by
  have P : ∀ z, pos z < 16 ↔ (-8 ≤ z ∧ z ≤ 7) := fun z => by
    have := pos_lt_iff (m := 1) (by norm_num) (z := z); norm_num at this; exact this
  have q0 := (P x).1 (by omega)
  have q1 := (P (x+d)).1 (by omega)
  have q2 := (P (x+2*d)).1 (by omega)
  have q3 := (P (x+3*d)).1 (by omega)
  have q4 := (P (x+4*d)).1 (by omega)
  rw [pos_small q0.1 q0.2, pos_small q1.1 q1.2, pos_small q2.1 q2.2, pos_small q3.1 q3.2,
    pos_small q4.1 q4.2] at *
  exact F5 x (by simp; omega) d (by simp; omega) q1.1 q1.2 q2.1 q2.2 q3.1 q3.2 q4.1 q4.2
    h01 h12 h23 h34

/-- last term in X2 (block S 1) -/
theorem core_one (x d : ℤ) (h4 : x + 4*d ∈ S 1)
    (h01 : pos x < pos (x+d)) (h12 : pos (x+d) < pos (x+2*d))
    (h23 : pos (x+2*d) < pos (x+3*d)) (h34 : pos (x+3*d) < pos (x+4*d)) : False := by
  have P : ∀ z, pos z < 16 ↔ (-8 ≤ z ∧ z ≤ 7) := fun z => by
    have := pos_lt_iff (m := 1) (by norm_num) (z := z); norm_num at this; exact this
  have P2 : ∀ z, pos z < 128 ↔ (-64 ≤ z ∧ z ≤ 63) := fun z => by
    have := pos_lt_iff (m := 2) (by norm_num) (z := z); norm_num at this; exact this
  have e8 : (8:ℤ)^1 = 8 := by norm_num
  have s4 := S_K e8 h4
  have p4 := pos_of_mem_S (n := 1) (by norm_num) h4
  have r4 := rankAux_lt 1 _ h4
  norm_num at p4 r4
  have hp4 : pos (x + 4*d) < 128 := by omega
  by_cases c2 : pos (x+2*d) < 16
  · have q0 := (P x).1 (by omega)
    have q1 := (P (x+d)).1 (by omega)
    have q2 := (P (x+2*d)).1 c2
    by_cases c3 : pos (x+3*d) < 16
    · have q3 := (P (x+3*d)).1 c3
      rw [pos_small q0.1 q0.2, pos_small q1.1 q1.2] at h01
      rw [pos_small q1.1 q1.2, pos_small q2.1 q2.2] at h12
      rw [pos_small q2.1 q2.2, pos_small q3.1 q3.2] at h23
      exact F4 x (by simp; omega) d (by simp; omega) q1.1 q1.2 q2.1 q2.2 q3.1 q3.2
        h01 h12 h23 (by omega)
    · have q3 := (P (x+3*d)).not.1 c3
      have q3' := (P2 (x+3*d)).1 (by omega)
      have h3 : x + 3*d ∈ S 1 := memS_K e8 (by omega)
      have hr := (pos_lt_iff_rank h3 h4).1 h34
      rw [pos_small q0.1 q0.2, pos_small q1.1 q1.2] at h01
      rw [pos_small q1.1 q1.2, pos_small q2.1 q2.2] at h12
      exact F3 x (by simp; omega) d (by simp; omega) q1.1 q1.2 q2.1 q2.2 h01 h12
        (by omega) (by omega) hr
  · have q2 := (P (x+2*d)).not.1 c2
    have q2' := (P2 (x+2*d)).1 (by omega)
    have q3 := (P (x+3*d)).not.1 (by omega)
    have q3' := (P2 (x+3*d)).1 (by omega)
    exact blk (memS_K e8 (by omega)) (memS_K e8 (by omega)) h4 h23 h34 (by ring)

/-- last term in block S (m+1), m ≥ 1 -/
theorem core_big {m : ℕ} (hm : m ≠ 0) (x d : ℤ) (h4 : x + 4*d ∈ S (m+1))
    (h01 : pos x < pos (x+d)) (h12 : pos (x+d) < pos (x+2*d))
    (h23 : pos (x+2*d) < pos (x+3*d)) (h34 : pos (x+3*d) < pos (x+4*d)) : False := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 8 ^ m = K := ⟨_, rfl⟩
  have hKi : (8:ℤ)^m = K := by exact_mod_cast hK
  have hK1 : 8 ^ (m+1) = 8 * K := by rw [pow_succ, hK]; ring
  have hK2 : 8 ^ (m+2) = 64 * K := by rw [pow_add, hK]; ring
  have hK1i : (8:ℤ)^(m+1) = 8 * K := by rw [pow_succ, hKi]; ring
  have hK2i : (8:ℤ)^(m+2) = 64 * K := by rw [pow_add, hKi]; ring
  have P : ∀ z, pos z < 2 * K ↔ (-(K:ℤ) ≤ z ∧ z ≤ K - 1) := fun z => by
    have := pos_lt_iff hm (z := z); rw [hK, hKi] at this; exact this
  have P8 : ∀ z, pos z < 16 * K ↔ (-(8*K:ℤ) ≤ z ∧ z ≤ 8*K - 1) := fun z => by
    have := pos_lt_iff (m := m+1) (by omega) (z := z); rw [hK1, hK1i] at this
    rw [show 16 * K = 2 * (8 * K) by ring]; exact this
  have P64 : ∀ z, pos z < 128 * K ↔ (-(64*K:ℤ) ≤ z ∧ z ≤ 64*K - 1) := fun z => by
    have := pos_lt_iff (m := m+2) (by omega) (z := z); rw [hK2, hK2i] at this
    rw [show 128 * K = 2 * (64 * K) by ring]; exact this
  have s4 := S_K hK1i h4
  have p4 := pos_of_mem_S (n := m+1) (by omega) h4
  have r4 := rankAux_lt (m+1) _ h4
  rw [hK1] at p4 r4
  have hKpos : 8 ≤ K := by
    rw [← hK]; calc 8 = 8^1 := rfl
      _ ≤ 8^m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have a0 := P x; have a1 := P (x+d); have a2 := P (x+2*d); have a3 := P (x+3*d)
  have a4 := P (x+4*d)
  have b0 := P8 x; have b1 := P8 (x+d); have b2 := P8 (x+2*d); have b3 := P8 (x+3*d)
  have b4 := P8 (x+4*d)
  have c2 := P64 (x+2*d); have c3 := P64 (x+3*d)
  by_cases k2 : pos (x+2*d) < 16 * K
  · by_cases k3 : pos (x+3*d) < 16 * K
    · by_cases l2 : pos (x+2*d) < 2 * K
      · omega
      · by_cases l1 : pos (x+d) < 2 * K
        · omega
        · exact blk (memS_K hKi (by omega)) (memS_K hKi (by omega)) (memS_K hKi (by omega))
            h12 h23 (by ring)
    · by_cases l2 : pos (x+2*d) < 2 * K
      · omega
      · by_cases l1 : pos (x+d) < 2 * K
        · omega
        · exact crs (memS_K hKi (by omega)) (memS_K hKi (by omega))
            (memS_K hK1i (by omega)) h4 h12 h34 (by ring) (by ring)
  · exact blk (memS_K hK1i (by omega)) (memS_K hK1i (by omega)) h4 h23 h34 (by ring)

theorem core (x d : ℤ)
    (h01 : pos x < pos (x+d)) (h12 : pos (x+d) < pos (x+2*d))
    (h23 : pos (x+2*d) < pos (x+3*d)) (h34 : pos (x+3*d) < pos (x+4*d)) : False := by
  rcases (pos_range (z := x + 4*d)) with ⟨_, pz⟩|⟨_, pz⟩|⟨_, pz1, pz2⟩|⟨n, hn, hz, _, _⟩
  · exact core_small x d (by omega) h01 h12 h23 h34
  · exact core_small x d (by omega) h01 h12 h23 h34
  · exact core_small x d (by omega) h01 h12 h23 h34
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact core_one x d hz h01 h12 h23 h34
    · exact core_big (by omega) x d hz h01 h12 h23 h34

end Adenwalla

namespace Erdos195

/-- Adenwalla (2024), Theorem 1: a permutation of ℤ with no monotone 5-term AP. -/
theorem adenwalla_fiveAP_free : ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAP f 5 := by
  refine ⟨Adenwalla.aden, ?_⟩
  rintro ⟨l, ⟨a, d, hap⟩, hl⟩
  have hlen : l.length = 5 := by
    rcases hap with h | h <;> simpa using congrArg List.length h
  match l, hlen with
  | [i, j, k, m, n], _ =>
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at hl
    obtain ⟨⟨hij, hik, him, hin⟩, ⟨hjk, hjm, hjn⟩, ⟨hkm, hkn⟩, hmn⟩ := hl
    have P : ∀ t z, Adenwalla.aden t = z → Adenwalla.pos z = t := fun t z h => by
      rw [← h]; exact Adenwalla.pos_aden t
    rcases hap with h | h
    · simp [List.range_succ] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      apply Adenwalla.core a d
      · rw [P _ _ h1, P _ _ (by rw [h2]; try ring)]; exact hij
      · rw [P _ _ (by rw [h2]; try ring), P _ _ (by rw [h3]; try ring)]; exact hjk
      · rw [P _ _ (by rw [h3]; try ring), P _ _ (by rw [h4]; try ring)]; exact hkm
      · rw [P _ _ (by rw [h4]; try ring), P _ _ (by rw [h5]; try ring)]; exact hmn.1
    · simp [List.range_succ] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      apply Adenwalla.core (a + 4*d) (-d)
      · rw [P _ _ (by rw [h1]; try ring), P _ _ (by rw [h2]; try ring)]; exact hij
      · rw [P _ _ (by rw [h2]; try ring), P _ _ (by rw [h3]; try ring)]; exact hjk
      · rw [P _ _ (by rw [h3]; try ring), P _ _ (by rw [h4]; try ring)]; exact hkm
      · rw [P _ _ (by rw [h4]; try ring), P _ _ (by rw [h5]; try ring)]; exact hmn.1

end Erdos195


namespace Erdos195

/-- Erdős #195 for permutations of ℤ: the answer is 3 iff some permutation avoids monotone 4-APs. -/
theorem answer_eq_three_iff :
    sSup {k : ℕ | ∀ f : ℕ ≃ ℤ, HasMonotoneAP f k} = 3 ↔ ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAP f 4 :=
  answer_eq_three_iff_of_fiveAP_free adenwalla_fiveAP_free

end Erdos195



open Erdos195 in
theorem solution : ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAP f 5 :=
  Erdos195.adenwalla_fiveAP_free
