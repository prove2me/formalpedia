-- Prove2me | solution 1 for FanInSemigroup.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T12:36:26.258126+00:00
-- url     : https://prove2.me/submissions/75d71f1a-0cf3-4c3c-a751-40a95e761bc2

import Definitions.Def_FanInSemigroup_wordLanguage
import Definitions.Def_FanInSemigroup_IsGroupfree
import Definitions.Def_FanInSemigroup_IsNoncounting

set_option autoImplicit false

open FanInSemigroup

/-- `fisPw b k = b ^ (k + 1)` in a semigroup. -/
def fisPw {S : Type*} [Semigroup S] (b : S) : ℕ → S
  | 0 => b
  | k + 1 => fisPw b k * b

theorem fisPw_add {S : Type*} [Semigroup S] (b : S) (i j : ℕ) :
    fisPw b (i + j + 1) = fisPw b i * fisPw b j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show fisPw b (i + j + 1) * b = fisPw b i * (fisPw b j * b)
    rw [ih, mul_assoc]

/-- In a finite groupfree semigroup every element is aperiodic: `b ^ (m + 2) = b ^ (m + 1)`. -/
theorem fisPw_aperiodic {S : Type*} [Semigroup S] [Finite S] (hS : IsGroupfree S) (b : S) :
    ∃ m, fisPw b (m + 1) = fisPw b m := by
  obtain ⟨x, y, hxy, hfxy⟩ := Finite.exists_ne_map_eq_of_infinite (fisPw b)
  obtain ⟨i, j, hij, hfij⟩ : ∃ i j, i < j ∧ fisPw b i = fisPw b j := by
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨x, y, h, hfxy⟩
    · exact ⟨y, x, h, hfxy.symm⟩
  obtain ⟨q, rfl⟩ : ∃ q, j = i + q := ⟨j - i, by omega⟩
  have hq1 : 1 ≤ q := by omega
  have hshift : ∀ r, fisPw b (i + q + r) = fisPw b (i + r) := by
    intro r
    induction r with
    | zero => exact hfij.symm
    | succ r ih =>
      show fisPw b (i + q + r) * b = fisPw b (i + r) * b
      rw [ih]
  have hq : ∀ t, i ≤ t → fisPw b (t + q) = fisPw b t := by
    intro t ht
    obtain ⟨r, rfl⟩ : ∃ r, t = i + r := ⟨t - i, by omega⟩
    rw [show i + r + q = i + q + r by omega]
    exact hshift r
  have hper : ∀ c s, i ≤ s → fisPw b (s + c * q) = fisPw b s := by
    intro c
    induction c with
    | zero => intro s _; simp
    | succ c ih =>
      intro s hs
      rw [show s + (c + 1) * q = (s + c * q) + q by ring,
        hq _ (le_trans hs (Nat.le_add_right _ _)), ih s hs]
  obtain ⟨a, ha, hia⟩ : ∃ a, a + 1 = (i + 1) * q ∧ i ≤ a := by
    have h := Nat.mul_le_mul_left (i + 1) hq1
    rw [mul_one] at h
    generalize (i + 1) * q = Q at h ⊢
    exact ⟨Q - 1, by omega, by omega⟩
  have hE : ∀ s, i ≤ s → fisPw b (s + (a + 1)) = fisPw b s := fun s hs => by
    rw [ha]; exact hper (i + 1) s hs
  have hE' : ∀ c s, i ≤ s → fisPw b (s + c * (a + 1)) = fisPw b s := by
    intro c
    induction c with
    | zero => intro s _; simp
    | succ c ih =>
      intro s hs
      rw [show s + (c + 1) * (a + 1) = (s + c * (a + 1)) + (a + 1) by ring,
        hE _ (le_trans hs (Nat.le_add_right _ _)), ih s hs]
  by_contra hne
  push Not at hne
  apply hS
  refine ⟨{x | ∃ r, x = fisPw b (a + r)}, fisPw b a, ?_⟩
  unfold IsNontrivialGroupIn
  refine ⟨⟨0, rfl⟩, ?_, ?_, ?_, ⟨fisPw b (a + 1), ⟨1, rfl⟩, hne a⟩⟩
  · rintro _ ⟨r, rfl⟩ _ ⟨r', rfl⟩
    refine ⟨a + r + r' + 1, ?_⟩
    rw [← fisPw_add]
    congr 1 <;> omega
  · rintro _ ⟨r, rfl⟩
    constructor
    · rw [← fisPw_add, ← hE (a + r) (by omega)]
      congr 1 <;> omega
    · rw [← fisPw_add, ← hE (a + r) (by omega)]
      congr 1 <;> omega
  · rintro _ ⟨r, rfl⟩
    refine ⟨fisPw b (a + r * a), ⟨r * a, rfl⟩, ?_, ?_⟩
    · rw [← fisPw_add, ← hE' (r + 1) a hia]
      congr 1 <;> ring
    · rw [← fisPw_add, ← hE' (r + 1) a hia]
      congr 1 <;> ring

theorem solution {S : Type*} [Semigroup S] [Finite S] (hS : IsGroupfree S) (a : S) :
    IsNoncounting (wordLanguage a) := by
  classical
  have := Fintype.ofFinite S
  choose mb hmb using fisPw_aperiodic hS
  have hstab : ∀ b k, mb b ≤ k → fisPw b k = fisPw b (mb b) := by
    intro b k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      show fisPw b k * b = _
      rw [ih]
      exact hmb b
  have hcoe : ∀ (l : List S) (a₀ : S), ((l.foldl (· * ·) a₀ : S) : WithOne S) =
      (a₀ : WithOne S) * (l.map (fun s : S => (s : WithOne S))).prod := by
    intro l
    induction l with
    | nil => intro a₀; simp
    | cons x l ih =>
      intro a₀
      rw [List.foldl_cons, ih, WithOne.coe_mul]
      simp [mul_assoc]
  have memL : ∀ w : List S, w ∈ wordLanguage a ↔
      w ≠ [] ∧ (w.map (fun s : S => (s : WithOne S))).prod = (a : WithOne S) := by
    intro w
    constructor
    · rintro ⟨a₀, l, rfl, h⟩
      refine ⟨List.cons_ne_nil _ _, ?_⟩
      rw [← h, wordProd, hcoe]
      simp
    · rintro ⟨hne, h⟩
      obtain ⟨a₀, l, rfl⟩ := List.exists_cons_of_ne_nil hne
      refine ⟨a₀, l, rfl, ?_⟩
      apply WithOne.coe_injective
      rw [wordProd, hcoe]
      simpa using h
  have hrep : ∀ (y : List S) (k : ℕ),
      (((List.replicate k y).flatten).map (fun s : S => (s : WithOne S))).prod =
        ((y.map (fun s : S => (s : WithOne S))).prod) ^ k := by
    intro y k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.replicate_succ, List.flatten_cons, List.map_append, List.prod_append, ih,
        pow_succ']
  refine ⟨Finset.univ.sup mb + 1, ?_⟩
  intro x y z m hm
  rcases eq_or_ne y [] with rfl | hy
  · simp
  obtain ⟨c₀, l, rfl⟩ := List.exists_cons_of_ne_nil hy
  have hyc : ((c₀ :: l).map (fun s : S => (s : WithOne S))).prod =
      ((wordProd c₀ l : S) : WithOne S) := by
    rw [wordProd, hcoe]
    simp
  have hpow : ∀ k, ((wordProd c₀ l : S) : WithOne S) ^ (k + 1) =
      ((fisPw (wordProd c₀ l) k : S) : WithOne S) := by
    intro k
    induction k with
    | zero => simp [fisPw]
    | succ k ih =>
      rw [pow_succ, ih, ← WithOne.coe_mul]
      rfl
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hle : mb (wordProd c₀ l) ≤ m' := by
    have := Finset.le_sup (f := mb) (Finset.mem_univ (wordProd c₀ l))
    omega
  have heq : fisPw (wordProd c₀ l) (m' + 1) = fisPw (wordProd c₀ l) m' := by
    rw [hstab _ _ hle, hstab _ _ (by omega)]
  rw [memL, memL]
  simp only [List.map_append, List.prod_append]
  rw [hrep, hrep, hyc, hpow, hpow, heq]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨by simp [List.replicate_succ], h⟩
  · rintro ⟨_, h⟩
    exact ⟨by simp [List.replicate_succ], h⟩
