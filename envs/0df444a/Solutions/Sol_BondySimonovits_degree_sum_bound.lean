-- Prove2me | solution 1 for BondySimonovits.degree_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:17:38.667868+00:00
-- url     : https://prove2.me/submissions/51302ca4-d2f1-4900-975a-9f7ef5cbe7df

module
public import Definitions.Def_BondySimonovitsLib_BSGrowth
public import Definitions.Def_BondySimonovitsLib_BSFinal
public import Theorems.Thm_BondySimonovits_restrictGraph_walk_mem
public import Theorems.Thm_BondySimonovits_bfs_bound
public import Theorems.Thm_BondySimonovits_exists_large_cut
public import Theorems.Thm_BondySimonovits_exists_minimal_dense


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*}
namespace BondySimonovits
theorem _root_.solution (k : ℕ) (hk : 2 ≤ k) [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcyc : ∀ (v : V) (p : G.Walk v v), p.IsCycle → p.length ≠ 2 * k) :
    ((∑ v, (univ.filter (G.Adj v)).card : ℕ) : ℝ) ≤
      2 * (16 * k + 4) * (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by
  classical
  by_contra hlt
  push Not at hlt
  set n := Fintype.card V with hn_def
  set S := ∑ v, (univ.filter (G.Adj v)).card with hS
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have : IsEmpty V := Fintype.card_eq_zero_iff.1 h
      have hS0 : S = 0 := by simp [hS]
      rw [hS0, h, Nat.cast_zero, Real.zero_rpow (by positivity)] at hlt
      simp at hlt
    · exact h
  obtain ⟨f, hf⟩ := exists_large_cut G
  set H := cutGraph G f with hH
  set E := ecount H univ univ with hE
  have hSE : S ≤ 2 * E := by
    refine hf.trans (le_of_eq ?_)
    rw [hE]
    unfold ecount
    congr 1
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [hH]
    exact congrArg Finset.card (Finset.filter_congr (fun u _ => Iff.rfl))
  set D := E / (2 * n) with hD
  have hD1 : 2 * n * D ≤ E := Nat.mul_div_le E (2 * n)
  have hD2 : E < 2 * n * (D + 1) := Nat.lt_mul_div_succ E (by omega)
  obtain ⟨Y, -, hYne, hYdeg, -⟩ := exists_minimal_dense H D univ
    (by rw [Finset.card_univ]; nlinarith)
  obtain ⟨x, hx⟩ := hYne
  set K := restrictGraph H (Y : Set V) with hK
  have hKG : K ≤ G := fun u v h => h.1.1
  have hfK : ∀ u v, K.Adj u v → f u ≠ f v := fun u v h => h.1.2
  have hcycK : ∀ (v : V) (p : K.Walk v v), p.IsCycle → p.length ≠ 2 * k := by
    intro v p hp
    have := hcyc v (p.mapLe hKG) (hp.mapLe hKG)
    rwa [Walk.length_mapLe] at this
  have hdeg : ∀ v, K.Reachable x v → D ≤ (univ.filter (K.Adj v)).card := by
    intro v ⟨p⟩
    have hv : v ∈ Y := restrictGraph_walk_mem H (Y : Set V) p hx
    refine (hYdeg v hv).trans (le_of_eq (congrArg Finset.card ?_))
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hK, restrictGraph,
      Finset.mem_coe]
    tauto
  -- arithmetic
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set r := (n : ℝ) ^ (1 / (k : ℝ)) with hr
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hr1 : 1 ≤ r := Real.one_le_rpow (by exact_mod_cast hn) (by positivity)
  have hrk : r ^ k = n := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hnr.le, one_div, inv_mul_cancel₀ hk0,
      Real.rpow_one]
  have hpow : (n : ℝ) ^ (1 + 1 / (k : ℝ)) = n * r := by
    rw [Real.rpow_add hnr, Real.rpow_one]
  rw [hpow] at hlt
  have hSE' : (S : ℝ) ≤ 2 * E := by exact_mod_cast hSE
  have hD2' : (E : ℝ) < 2 * n * (D + 1) := by exact_mod_cast hD2
  have h1 : (16 * k + 4 : ℝ) * r < 2 * (D + 1) := by
    have : (16 * k + 4 : ℝ) * r * n < 2 * (D + 1) * n := by nlinarith
    exact lt_of_mul_lt_mul_right this hnr.le
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hDr : (8 * k + 1 : ℝ) * r < D := by nlinarith
  have hdk : 8 * k ≤ D := by
    have : (8 * k : ℝ) < D := by nlinarith
    exact_mod_cast this.le
  have hbound := bfs_bound K f hfK x k hk hcycK D hdeg hdk
  push_cast at hbound
  have ht : r < (D : ℝ) / (2 * k) - 3 := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]
    nlinarith
  have := pow_lt_pow_left₀ ht (by linarith) (show k ≠ 0 by omega)
  rw [hrk] at this
  linarith
end BondySimonovits
