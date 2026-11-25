-- Prove2me | solution 1 for Erdos1063.sharp_valuation_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:43:08.695894+00:00
-- url     : https://prove2.me/submissions/ab3dcdce-db88-43aa-a1b8-b1b01ea59fba

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
public import Theorems.Thm_Erdos1063_valuation_bound_aux
public import Theorems.Thm_Erdos1063_padicValNat_prod_range
public import Theorems.Thm_Erdos1063_prod_range_succ_eq_factorial

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {n k p e : ℕ} (hp : p.Prime) (hkn : 2 * k ≤ n) (hpk : p ∣ k)
    (hk : 2 ≤ k) (he : e < k)
    (hgood : ∀ i < k, i ≠ e → (n - i) ∣ n.choose k) :
    padicValNat p k + padicValNat p ((k - 1).choose e) + Nat.log p (max e (k - 1 - e))
      ≤ padicValNat p (n - e) := by
  have := Fact.mk hp
  have hC : n.choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  obtain ⟨hVM, hLM⟩ := valuation_bound_aux hp hkn hpk hk hgood
  set V := padicValNat p (n.choose k) with hV
  set M := padicValNat p (n - e) with hM
  set a := padicValNat p k with ha
  set m := k - 1 - e with hm
  have hle : ∀ i < k, i ≠ e → padicValNat p (n - i) ≤ V := by
    intro i hi hne
    exact (padicValNat_dvd_iff_le hC).mp ((pow_padicValNat_dvd).trans (hgood i hi hne))
  -- each other element has valuation at most that of its distance to e
  have hlow : ∀ i < e, padicValNat p (n - i) ≤ padicValNat p (e - i) := by
    intro i hi
    have hc := hle i (by omega) (by omega)
    have d1 : p ^ padicValNat p (n - i) ∣ n - i := pow_padicValNat_dvd
    have d2 : p ^ padicValNat p (n - i) ∣ n - e :=
      (pow_dvd_pow p (by omega)).trans pow_padicValNat_dvd
    have d3 := Nat.dvd_sub d1 d2
    rw [show n - i - (n - e) = e - i by omega] at d3
    exact (padicValNat_dvd_iff_le (by omega)).mp d3
  have hhigh : ∀ y < m, padicValNat p (n - (e + 1 + y)) ≤ padicValNat p (y + 1) := by
    intro y hy
    have hc := hle (e + 1 + y) (by omega) (by omega)
    have d1 : p ^ padicValNat p (n - (e + 1 + y)) ∣ n - (e + 1 + y) := pow_padicValNat_dvd
    have d2 : p ^ padicValNat p (n - (e + 1 + y)) ∣ n - e :=
      (pow_dvd_pow p (by omega)).trans pow_padicValNat_dvd
    have d3 := Nat.dvd_sub d2 d1
    rw [show n - e - (n - (e + 1 + y)) = y + 1 by omega] at d3
    exact (padicValNat_dvd_iff_le (by omega)).mp d3
  -- the whole block: sum of valuations = v_p(k!) + V
  have hprod := padicValNat_prod_range (p := p) (fun i => n - i) k (fun i hi => by omega)
  rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose,
    padicValNat.mul (Nat.factorial_ne_zero k) hC] at hprod
  have hsplit : ∑ i ∈ Finset.range k, padicValNat p (n - i) =
      ∑ i ∈ Finset.range e, padicValNat p (n - i) + M +
      ∑ y ∈ Finset.range m, padicValNat p (n - (e + 1 + y)) := by
    have hk' : k = (e + 1) + m := by omega
    conv_lhs => rw [hk']
    rw [Finset.sum_range_add, Finset.sum_range_succ]
  have hefac : padicValNat p (e !) = ∑ i ∈ Finset.range e, padicValNat p (e - i) := by
    have h := padicValNat_prod_range (p := p) (fun i => e - i) e (fun i hi => by omega)
    rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self] at h
    exact h
  have hmfac : padicValNat p (m !) = ∑ y ∈ Finset.range m, padicValNat p (y + 1) := by
    have h := padicValNat_prod_range (p := p) (fun y => y + 1) m (fun y hy => by omega)
    rw [prod_range_succ_eq_factorial] at h
    exact h
  have hkfac : padicValNat p (k !) =
      a + padicValNat p ((k - 1).choose e) + padicValNat p (e !) + padicValNat p (m !) := by
    rw [← Nat.mul_factorial_pred (by omega : k ≠ 0),
      ← Nat.choose_mul_factorial_mul_factorial (by omega : e ≤ k - 1),
      padicValNat.mul (by omega) (Nat.mul_ne_zero (Nat.mul_ne_zero
        (Nat.choose_pos (by omega)).ne' (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _)),
      padicValNat.mul (Nat.mul_ne_zero (Nat.choose_pos (by omega)).ne' (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      padicValNat.mul (Nat.choose_pos (by omega)).ne' (Nat.factorial_ne_zero _)]
    ring
  have hsumlow : ∑ i ∈ Finset.range e, padicValNat p (n - i) ≤
      ∑ i ∈ Finset.range e, padicValNat p (e - i) :=
    Finset.sum_le_sum fun i hi => hlow i (by simpa using hi)
  have hsumhigh : ∑ y ∈ Finset.range m, padicValNat p (n - (e + 1 + y)) ≤
      ∑ y ∈ Finset.range m, padicValNat p (y + 1) :=
    Finset.sum_le_sum fun y hy => hhigh y (by simpa using hy)
  have key : V + a + padicValNat p ((k - 1).choose e) ≤ M := by omega
  -- some other element sits at distance p^u from e, so u ≤ V
  have hu : Nat.log p (max e m) ≤ V := by
    set r := max e m with hr
    have h1 := le_max_left e m
    have h2 := le_max_right e m
    have hrk : r ≤ k - 1 := max_le (by omega) (by omega)
    have hr0 : r ≠ 0 := by omega
    set u := Nat.log p r with hu'
    have hpu : p ^ u ≤ r := Nat.pow_log_le_self p hr0
    have hu1 : 1 ≤ p ^ u := Nat.one_le_pow _ _ hp.pos
    have hulog : u ≤ Nat.log p (k - 1) := Nat.log_mono_right hrk
    have hpuM : p ^ u ∣ n - e := (pow_dvd_pow p (by omega)).trans pow_padicValNat_dvd
    rcases le_total m e with h | h
    · have hre : r = e := by rw [hr]; exact max_eq_left h
      have hd : p ^ u ∣ n - (e - p ^ u) := by
        rw [show n - (e - p ^ u) = (n - e) + p ^ u by omega]
        exact Nat.dvd_add hpuM dvd_rfl
      exact ((padicValNat_dvd_iff_le (by omega)).mp hd).trans (hle _ (by omega) (by omega))
    · have hre : r = m := by rw [hr]; exact max_eq_right h
      have hd : p ^ u ∣ n - (e + p ^ u) := by
        rw [show n - (e + p ^ u) = (n - e) - p ^ u by omega]
        exact Nat.dvd_sub hpuM dvd_rfl
      exact ((padicValNat_dvd_iff_le (by omega)).mp hd).trans (hle _ (by omega) (by omega))
  omega
end Erdos1063
