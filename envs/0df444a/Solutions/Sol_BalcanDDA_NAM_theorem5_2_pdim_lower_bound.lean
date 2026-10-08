-- Prove2me | solution 1 for BalcanDDA.NAM.theorem5_2_pdim_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T15:03:17.666589+00:00
-- url     : https://prove2.me/submissions/e8a66903-ae0a-4a01-b8f7-3eecbe05096c

/-
Theorem 5.2 of Balcan et al. (data-driven algorithm design, neutral affine maximizers): the
pseudo-dimension of the class of NAM welfare functions is at least `⌊n/2⌋`.

Pair up the agents `(2l, 2l+1)`, for `l < ⌊n/2⌋`. In profile `l`, agent `2l` values alternative 0 at
2 and alternative 1 at 0, agent `2l+1` values them at 0 and 1, every other alternative is worth `-1`
to both, and all other agents value everything at 0. For a bit pattern `b`, give the pair `l`
weights `(1, 0)` if `b l` and `(0, 1)` otherwise (so every weight vector has a zero entry). Then
alternative 0 (resp. 1) is the unique weighted maximizer in profile `l`, whatever the other
pairs' weights are, so any argmax rule outputs it; the welfare is 2 (resp. 1). The threshold `3/2`
separates the patterns.
-/
import Mathlib
import Definitions.Def_FoundationsML_Regression_Shatters
import Definitions.Def_BalcanDDA_NAM_Model

set_option autoImplicit false

namespace NamLib
open BalcanDDA.NAM

/-- Valuations of the pair of agents `2l, 2l+1`: agent `2l` likes alternative 0 (value 2), agent
`2l+1` likes alternative 1 (value 1), every other alternative is worth `-1` to both. -/
def pairVal (l i j : ℕ) : ℝ :=
  if i = 2 * l then (if j = 0 then 2 else if j = 1 then 0 else -1)
  else if i = 2 * l + 1 then (if j = 0 then 0 else if j = 1 then 1 else -1) else 0

/-- Weights: in pair `l` give weight `(1, 0)` if the bit is set and `(0, 1)` otherwise. -/
noncomputable def rho (n : ℕ) (b : Fin (n / 2) → Bool) : Fin n → ℝ := fun i =>
  if h : i.val / 2 < n / 2 then
    (if i.val % 2 = 0 then (if b ⟨i.val / 2, h⟩ then 1 else 0) else (if b ⟨i.val / 2, h⟩ then 0 else 1))
  else 0

theorem sum_pair (n l : ℕ) (hl : 2 * l + 1 < n) (g : ℕ → ℝ)
    (hg : ∀ i, i ≠ 2 * l → i ≠ 2 * l + 1 → g i = 0) :
    ∑ i : Fin n, g i.val = g (2 * l) + g (2 * l + 1) := by
  rw [Finset.sum_eq_add (⟨2 * l, by omega⟩ : Fin n) ⟨2 * l + 1, hl⟩ (by simp [Fin.ext_iff])]
  · intro c _ hc
    exact hg c.val (fun h => hc.1 (Fin.ext h)) (fun h => hc.2 (Fin.ext h))
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rho_even (n : ℕ) (b : Fin (n / 2) → Bool) (l : Fin (n / 2)) (h : 2 * l.val < n) :
    rho n b ⟨2 * l.val, h⟩ = if b l then 1 else 0 := by
  unfold rho
  have h1 : (2 * l.val) / 2 = l.val := by omega
  simp [h1, l.2]

theorem rho_odd (n : ℕ) (b : Fin (n / 2) → Bool) (l : Fin (n / 2)) (h : 2 * l.val + 1 < n) :
    rho n b ⟨2 * l.val + 1, h⟩ = if b l then 0 else 1 := by
  unfold rho
  have h1 : (2 * l.val + 1) / 2 = l.val := by omega
  have h2 : (2 * l.val + 1) % 2 = 1 := by omega
  simp [h1, h2, l.2]

theorem rho_nonneg (n : ℕ) (b : Fin (n / 2) → Bool) (i : Fin n) : 0 ≤ rho n b i := by
  unfold rho
  split_ifs <;> norm_num

theorem rho_zero (n : ℕ) (hn : 1 ≤ n) (b : Fin (n / 2) → Bool) : ∃ i, rho n b i = 0 := by
  by_cases h : n / 2 = 0
  · refine ⟨⟨0, hn⟩, ?_⟩
    unfold rho
    simp [h]
  · have h0 : 0 < n / 2 := Nat.pos_of_ne_zero h
    have h2 : 2 ≤ n := by omega
    by_cases hb : b ⟨0, h0⟩ = true
    · refine ⟨⟨2 * 0 + 1, by omega⟩, ?_⟩
      have := rho_odd n b ⟨0, h0⟩ (by simpa using (by omega : 1 < n))
      simpa [hb] using this
    · refine ⟨⟨2 * 0, by omega⟩, ?_⟩
      have := rho_even n b ⟨0, h0⟩ (by simpa using (by omega : 0 < n))
      simpa [hb] using this

/-- The weighted value of alternative `j` in profile `l` under the weights `rho n b`. -/
theorem weighted (n m : ℕ) (b : Fin (n / 2) → Bool) (l : Fin (n / 2)) (j : Fin m) :
    ∑ i : Fin n, rho n b i * pairVal l.val i.val j.val =
      (if b l then (1 : ℝ) else 0) * pairVal l.val (2 * l.val) j.val +
        (if b l then (0 : ℝ) else 1) * pairVal l.val (2 * l.val + 1) j.val := by
  have hl : 2 * l.val + 1 < n := by have := l.2; omega
  have hl0 : 2 * l.val < n := by omega
  have := sum_pair n l.val hl (fun i => if h : i < n then rho n b ⟨i, h⟩ * pairVal l.val i j.val else 0)
    (fun i hi1 hi2 => by
      by_cases h : i < n
      · simp only [h, dif_pos]
        have : pairVal l.val i j.val = 0 := by simp [pairVal, hi1, hi2]
        rw [this, mul_zero]
      · simp [h])
  have e : ∀ i : Fin n, (if h : i.val < n then rho n b ⟨i.val, h⟩ * pairVal l.val i.val j.val else 0) =
      rho n b i * pairVal l.val i.val j.val := fun i => by simp
  simp only [e] at this
  rw [this]
  simp only [hl, hl0, dif_pos]
  rw [rho_even n b l hl0, rho_odd n b l hl]

theorem welfare_value (n m : ℕ) (l : Fin (n / 2)) (o : Fin m) :
    ∑ i : Fin n, pairVal l.val i.val o.val =
      pairVal l.val (2 * l.val) o.val + pairVal l.val (2 * l.val + 1) o.val := by
  have hl : 2 * l.val + 1 < n := by have := l.2; omega
  exact sum_pair n l.val hl (fun i => pairVal l.val i o.val)
    (fun i hi1 hi2 => by simp [pairVal, hi1, hi2])

theorem nam_main (n m : ℕ) (hn : 1 ≤ n) (hm : 2 ≤ m)
    (ψ : (Fin n → ℝ) → (Fin n → Fin m → ℝ) → Fin m) (hψ : IsArgmaxSelector ψ) :
    ∃ v : Fin (n / 2) → (Fin n → Fin m → ℝ), FoundationsML.Regression.Shatters (namClass ψ) v := by
  refine ⟨fun l i j => pairVal l.val i.val j.val, fun _ => 3 / 2, fun b => ?_⟩
  refine ⟨welfare ψ (rho n b), ⟨rho n b, ⟨rho_nonneg n b, rho_zero n hn b⟩, rfl⟩, fun l => ?_⟩
  set v : Fin n → Fin m → ℝ := fun i j => pairVal l.val i.val j.val with hv
  set o : Fin m := ψ (rho n b) v with ho
  have hmax : ∀ j : Fin m, ∑ i : Fin n, rho n b i * v i j ≤ ∑ i : Fin n, rho n b i * v i o :=
    hψ (rho n b) v
  have hw : welfare ψ (rho n b) v = ∑ i : Fin n, pairVal l.val i.val o.val := rfl
  rw [hw, welfare_value]
  have hSj : ∀ j : Fin m, ∑ i : Fin n, rho n b i * v i j =
      (if b l then (1 : ℝ) else 0) * pairVal l.val (2 * l.val) j.val +
        (if b l then (0 : ℝ) else 1) * pairVal l.val (2 * l.val + 1) j.val :=
    fun j => weighted n m b l j
  by_cases hb : b l = true
  · have h0 := hmax ⟨0, by omega⟩
    rw [hSj, hSj] at h0
    have ho0 : o.val = 0 := by
      by_contra hne
      simp [hb, pairVal] at h0
      by_cases h1 : o.val = 1
      · simp [h1] at h0; norm_num at h0
      · simp [hne, h1] at h0; norm_num at h0
    simp [pairVal, ho0, hb]
    norm_num
  · have hb' : b l = false := by simpa using hb
    have h1 := hmax ⟨1, by omega⟩
    rw [hSj, hSj] at h1
    have ho1 : o.val = 1 := by
      by_contra hne
      simp [hb', pairVal] at h1
      by_cases h0 : o.val = 0
      · simp [h0] at h1; norm_num at h1
      · simp [hne, h0] at h1; norm_num at h1
    simp [pairVal, ho1, hb']
    norm_num

end NamLib

open BalcanDDA.NAM in
theorem solution (n m : ℕ) (hn : 1 ≤ n) (hm : 2 ≤ m)
    (ψ : (Fin n → ℝ) → (Fin n → Fin m → ℝ) → Fin m) (hψ : IsArgmaxSelector ψ) :
    ∃ v : Fin (n / 2) → (Fin n → Fin m → ℝ),
      FoundationsML.Regression.Shatters (namClass ψ) v :=
  NamLib.nam_main n m hn hm ψ hψ
