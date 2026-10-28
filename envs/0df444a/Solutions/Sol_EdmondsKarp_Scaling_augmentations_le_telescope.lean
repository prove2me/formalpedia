-- Prove2me | solution 1 for EdmondsKarp.Scaling.augmentations_le_telescope
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:06:39.575736+00:00
-- url     : https://prove2.me/submissions/b96ac242-9722-4249-bfc8-182662e9b52f

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.MinMax
import Mathlib.Order.Partition.Finpartition
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_EdmondsKarp_Scaling_Transport
import Definitions.Def_EdmondsKarp_Scaling_Augmentation
import Definitions.Def_EdmondsKarp_Scaling_Run
import Theorems.Thm_EdmondsKarp_Scaling_maxFlow_value_problem
import Theorems.Thm_EdmondsKarp_Scaling_isMaxFlow_iff_no_augPath

open EdmondsKarp.Scaling

@[simp] private lemma zero_f0 {m n : ℕ} (i : Fin m) : (0 : Flow m n).f0 i = 0 := rfl
@[simp] private lemma zero_fx {m n : ℕ} (i : Fin m) (j : Fin n) : (0 : Flow m n).fx i j = 0 := rfl
@[simp] private lemma zero_fz {m n : ℕ} (j : Fin n) : (0 : Flow m n).fz j = 0 := rfl
@[simp] private lemma zero_ret {m n : ℕ} : (0 : Flow m n).ret = 0 := rfl

@[simp] private lemma smul_f0 {m n : ℕ} (c : ℝ) (x : Flow m n) (i : Fin m) :
    (c • x).f0 i = c * x.f0 i := rfl
@[simp] private lemma smul_fx {m n : ℕ} (c : ℝ) (x : Flow m n) (i : Fin m) (j : Fin n) :
    (c • x).fx i j = c * x.fx i j := rfl
@[simp] private lemma smul_fz {m n : ℕ} (c : ℝ) (x : Flow m n) (j : Fin n) :
    (c • x).fz j = c * x.fz j := rfl
@[simp] private lemma smul_ret {m n : ℕ} (c : ℝ) (x : Flow m n) :
    (c • x).ret = c * x.ret := rfl

/-- All arc values and the return-arc value of `x` are integers. -/
private def IsIntegralFlow {m n : ℕ} (x : Flow m n) : Prop :=
  (∀ i, ∃ z : ℤ, x.f0 i = z) ∧
  (∀ i j, ∃ z : ℤ, x.fx i j = z) ∧
  (∀ j, ∃ z : ℤ, x.fz j = z) ∧
  (∃ z : ℤ, x.ret = z)

private lemma isIntegralFlow_zero {m n : ℕ} : IsIntegralFlow (0 : Flow m n) := by
  refine ⟨fun _ => ⟨0, ?_⟩, fun _ _ => ⟨0, ?_⟩, fun _ => ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;>
    simp only [zero_f0, zero_fx, zero_fz, zero_ret, Int.cast_zero]

private lemma isIntegralFlow_two_smul {m n : ℕ} {x : Flow m n} (hx : IsIntegralFlow x) :
    IsIntegralFlow ((2 : ℝ) • x) := by
  rcases hx with ⟨hf0, hfx, hfz, zret, hret⟩
  refine ⟨fun i => ?_, fun i j => ?_, fun j => ?_, ⟨2 * zret, ?_⟩⟩
  · rcases hf0 i with ⟨z, hz⟩
    exact ⟨2 * z, by simp only [smul_f0, hz, Int.cast_mul, Int.cast_ofNat]⟩
  · rcases hfx i j with ⟨z, hz⟩
    exact ⟨2 * z, by simp only [smul_fx, hz, Int.cast_mul, Int.cast_ofNat]⟩
  · rcases hfz j with ⟨z, hz⟩
    exact ⟨2 * z, by simp only [smul_fz, hz, Int.cast_mul, Int.cast_ofNat]⟩
  · simp only [smul_ret, hret, Int.cast_mul, Int.cast_ofNat]

private lemma pathDir_integral {m n : ℕ} (L : List (Node m n)) (u v : Node m n) :
    ∃ z : ℤ, pathDir L u v = z := by
  unfold pathDir
  split_ifs <;>
    [exact ⟨0, by norm_num⟩; exact ⟨1, by norm_num⟩;
     exact ⟨-1, by norm_num⟩; exact ⟨0, by norm_num⟩]

private lemma resCap_problem_integral {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ)
    (d : Fin m → Fin n → ℝ) (p : ℕ) {x : Flow m n} (hx : IsIntegralFlow x)
    (u v : Node m n) {ε : ℝ} (hε : resCap (problem a b d p) x u v = (ε : WithTop ℝ)) :
    ∃ z : ℤ, ε = z := by
  rcases hx with ⟨hf0, hfx, hfz, _⟩
  rcases u with _ | _ | i | j <;> rcases v with _ | _ | i' | j'
  · simp only [resCap, WithTop.zero_eq_coe] at hε; exact ⟨0, by rw [hε, Int.cast_zero]⟩
  · simp only [resCap, WithTop.zero_eq_coe] at hε; exact ⟨0, by rw [hε, Int.cast_zero]⟩
  · dsimp [resCap, problem] at hε
    rcases hf0 i' with ⟨z, hz⟩
    have h1 : ((a i' / 2 ^ p : ℕ) : ℝ) - x.f0 i' = ε := WithTop.coe_inj.mp hε
    exact ⟨(a i' / 2 ^ p : ℕ) - z, by rw [Int.cast_sub, Int.cast_natCast, ← h1, hz]⟩
  · simp only [resCap, WithTop.zero_eq_coe] at hε; exact ⟨0, by rw [hε, Int.cast_zero]⟩
  · simp only [resCap, WithTop.zero_eq_coe] at hε; exact ⟨0, by rw [hε, Int.cast_zero]⟩
  · simp only [resCap, WithTop.zero_eq_coe] at hε; exact ⟨0, by rw [hε, Int.cast_zero]⟩
  · simp only [resCap, WithTop.zero_eq_coe] at hε; exact ⟨0, by rw [hε, Int.cast_zero]⟩
  · dsimp [resCap] at hε
    rcases hfz j' with ⟨z, hz⟩
    have h1 : x.fz j' = ε := WithTop.coe_inj.mp hε
    exact ⟨z, by linarith⟩
  · dsimp [resCap] at hε
    rcases hf0 i with ⟨z, hz⟩
    have h1 : x.f0 i = ε := WithTop.coe_inj.mp hε
    exact ⟨z, by linarith⟩
  · simp only [resCap, WithTop.zero_eq_coe] at hε; exact ⟨0, by rw [hε, Int.cast_zero]⟩
  · simp only [resCap, WithTop.zero_eq_coe] at hε; exact ⟨0, by rw [hε, Int.cast_zero]⟩
  · simp only [resCap, WithTop.top_ne_coe] at hε
  · simp only [resCap, WithTop.zero_eq_coe] at hε; exact ⟨0, by rw [hε, Int.cast_zero]⟩
  · dsimp [resCap, problem] at hε
    rcases hfz j with ⟨z, hz⟩
    have h1 : ((b j / 2 ^ p : ℕ) : ℝ) - x.fz j = ε := WithTop.coe_inj.mp hε
    exact ⟨(b j / 2 ^ p : ℕ) - z, by rw [Int.cast_sub, Int.cast_natCast, ← h1, hz]⟩
  · dsimp [resCap] at hε
    rcases hfx i' j with ⟨z, hz⟩
    have h1 : x.fx i' j = ε := WithTop.coe_inj.mp hε
    exact ⟨z, by linarith⟩
  · simp only [resCap, WithTop.zero_eq_coe] at hε; exact ⟨0, by rw [hε, Int.cast_zero]⟩

private lemma augStep_integral_and_ret_add_one {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ)
    (d : Fin m → Fin n → ℝ) (p : ℕ) {x y : Flow m n} (hx : IsIntegralFlow x)
    (hstep : AugStep (problem a b d p) x y) :
    IsIntegralFlow y ∧ x.ret + 1 ≤ y.ret := by
  rcases hstep with ⟨L, ε, hL, hε, rfl⟩
  rcases hε.2 with ⟨e, he, hcap⟩
  have hpos_wt : (0 : WithTop ℝ) < (ε : WithTop ℝ) := hcap ▸ hL.2.2.2 e he
  have hpos : 0 < ε := WithTop.coe_lt_coe.mp hpos_wt
  rcases resCap_problem_integral a b d p hx e.1 e.2 hcap with ⟨zε, hzε⟩
  have hzε_pos : 0 < zε := by
    have : ((0 : ℤ) : ℝ) < (zε : ℝ) := by rw [Int.cast_zero, ← hzε]; exact hpos
    exact Int.cast_lt.mp this
  have hzε_ge : (1 : ℝ) ≤ ε := by
    have h1 : (1 : ℤ) ≤ zε := by omega
    rw [hzε]
    exact_mod_cast h1
  rcases hx with ⟨hf0, hfx, hfz, zret, hret⟩
  refine ⟨⟨fun i => ?_, fun i j => ?_, fun j => ?_, ⟨zret + zε, ?_⟩⟩, ?_⟩
  · rcases hf0 i with ⟨z0, hz0⟩
    rcases pathDir_integral L .s (.src i) with ⟨zd, hzd⟩
    exact ⟨z0 + zε * zd, by simp only [augment, hz0, hzε, hzd, Int.cast_add, Int.cast_mul]⟩
  · rcases hfx i j with ⟨zx, hzx⟩
    rcases pathDir_integral L (.src i) (.dst j) with ⟨zd, hzd⟩
    exact ⟨zx + zε * zd, by simp only [augment, hzx, hzε, hzd, Int.cast_add, Int.cast_mul]⟩
  · rcases hfz j with ⟨zz, hzz⟩
    rcases pathDir_integral L (.dst j) .t with ⟨zd, hzd⟩
    exact ⟨zz + zε * zd, by simp only [augment, hzz, hzε, hzd, Int.cast_add, Int.cast_mul]⟩
  · simp only [augment, hret, hzε, Int.cast_add]
  · simp only [augment]
    linarith

private lemma phase_integral_and_ret {m n : ℕ} {a : Fin m → ℕ} {b : Fin n → ℕ}
    {d : Fin m → Fin n → ℝ} {l : ℕ} {K : ℕ → ℕ} {F : ℕ → ℕ → Flow m n}
    (hR : IsScalingRun a b d l K F) {p : ℕ} (hp : p < l) (h0 : IsIntegralFlow (F p 0)) :
    ∀ k ≤ K p, IsIntegralFlow (F p k) ∧ (F p 0).ret + (k : ℝ) ≤ (F p k).ret := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨h0, by simp only [Nat.cast_zero, add_zero, le_rfl]⟩
  | succ k ih =>
    intro hk
    have hk_lt : k < K p := Nat.lt_of_succ_le hk
    obtain ⟨hint_k, hret_k⟩ := ih (Nat.le_of_lt hk_lt)
    obtain ⟨hint_succ, hret_succ⟩ :=
      augStep_integral_and_ret_add_one a b d p hint_k (hR.step p hp k hk_lt)
    refine ⟨hint_succ, ?_⟩
    rw [Nat.cast_add, Nat.cast_one]
    linarith

private lemma run_integral {m n : ℕ} {a : Fin m → ℕ} {b : Fin n → ℕ}
    {d : Fin m → Fin n → ℝ} {l : ℕ} {K : ℕ → ℕ} {F : ℕ → ℕ → Flow m n}
    (hR : IsScalingRun a b d l K F) :
    ∀ q, ∀ p, p < l → l - 1 - p = q →
      IsIntegralFlow (F p 0) ∧ (F p 0).ret + (K p : ℝ) ≤ (F p (K p)).ret := by
  intro q
  induction q with
  | zero =>
    intro p hp hq
    have hp_eq : p = l - 1 := by omega
    have h0 : IsIntegralFlow (F p 0) := by
      rw [hp_eq, hR.start]
      exact isIntegralFlow_zero
    exact ⟨h0, (phase_integral_and_ret hR hp h0 (K p) le_rfl).2⟩
  | succ q ih =>
    intro p hp hq
    have hp1 : p + 1 < l := by omega
    have h0_prev : IsIntegralFlow (F (p + 1) 0) := (ih (p + 1) hp1 (by omega)).1
    have hK_prev : IsIntegralFlow (F (p + 1) (K (p + 1))) :=
      (phase_integral_and_ret hR hp1 h0_prev (K (p + 1)) le_rfl).1
    have h0 : IsIntegralFlow (F p 0) := by
      have hrest := hR.restart (p + 1) (by omega) hp1
      simp only [Nat.add_sub_cancel] at hrest
      rw [hrest]
      exact isIntegralFlow_two_smul hK_prev
    exact ⟨h0, (phase_integral_and_ret hR hp h0 (K p) le_rfl).2⟩

private lemma sum_range_le_telescope_aux (K : ℕ → ℕ) (g : ℕ → ℤ) {l : ℕ}
    (hstep : ∀ p, p + 1 < l → (K p : ℤ) ≤ g p - 2 * g (p + 1)) :
    ∀ k, k < l →
      ((∑ p ∈ Finset.range k, K p : ℕ) : ℤ) ≤ g 0 - g k - ∑ p ∈ Finset.Ico 1 (k + 1), g p := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, sub_self, Finset.Ico_self, le_rfl]
  | succ k ih =>
    intro hk
    have hk_lt : k < l := Nat.lt_of_succ_lt hk
    have h1 := ih hk_lt
    have h2 := hstep k hk
    rw [Finset.sum_range_succ, Nat.cast_add, Finset.sum_Ico_succ_top (by omega : 1 ≤ k + 1)]
    linarith

/-- Proof of Theorem 9, eq. (6) (p. 260): writing `f_p^* = min(∑_i [a_i/2^p], ∑_j [b_j/2^p])` for the
maximum-flow value of Problem `p`, the total number of augmentations of a run of the scaling method
is at most `f_{l-1}^* + ∑_{p=1}^{l-1} (f_{p-1}^* - 2 f_p^*) = f_0^* - ∑_{p=1}^{l-1} f_p^*`. -/
theorem solution {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (a : Fin m → ℕ)
    (b : Fin n → ℕ) (d : Fin m → Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hsum : ∑ i, a i = ∑ j, b j) (hd : ∀ i j, 0 ≤ d i j) (l : ℕ)
    (hla : ∀ i, a i < 2 ^ l) (hlb : ∀ j, b j < 2 ^ l) (K : ℕ → ℕ) (F : ℕ → ℕ → Flow m n)
    (hR : IsScalingRun a b d l K F) :
    ((∑ p ∈ Finset.range l, K p : ℕ) : ℤ) ≤
      ((min (∑ i, a i) (∑ j, b j) : ℕ) : ℤ) -
        ∑ p ∈ Finset.Ico 1 l, ((min (∑ i, a i / 2 ^ p) (∑ j, b j / 2 ^ p) : ℕ) : ℤ) := by
  have _ := hlb
  have hl_pos : 1 ≤ l := by
    by_contra h
    have hl0 : l = 0 := by omega
    have h1 := ha ⟨0, hm⟩
    have h2 := hla ⟨0, hm⟩
    rw [hl0, pow_zero] at h2
    omega
  let g : ℕ → ℤ := fun p => ((min (∑ i, a i / 2 ^ p) (∑ j, b j / 2 ^ p) : ℕ) : ℤ)
  have hret_end : ∀ p < l, (F p (K p)).ret = (g p : ℝ) := by
    intro p hp
    have hflow : IsFlow (problem a b d p) (F p (K p)) := (hR.pseudo p hp (K p) le_rfl).1
    have hmax : IsMaxFlow (problem a b d p) (F p (K p)) :=
      (isMaxFlow_iff_no_augPath (problem a b d p) (F p (K p)) hflow).mpr (hR.stop p hp)
    have hval := (maxFlow_value_problem hm hn a b d ha hb hsum hd p).2 (F p (K p)) hmax
    rw [hval]
    dsimp only [g]
    exact (Int.cast_natCast _).symm
  have hK_le : ∀ p < l, (F p 0).ret + (K p : ℝ) ≤ (g p : ℝ) := by
    intro p hp
    rw [← hret_end p hp]
    exact (run_integral hR (l - 1 - p) p hp rfl).2
  have hstep_g : ∀ p, p + 1 < l → (K p : ℤ) ≤ g p - 2 * g (p + 1) := by
    intro p hp1
    have hp : p < l := Nat.lt_of_succ_lt hp1
    have hrest := hR.restart (p + 1) (by omega) hp1
    simp only [Nat.add_sub_cancel] at hrest
    have h0_ret : (F p 0).ret = 2 * (g (p + 1) : ℝ) := by
      rw [hrest, smul_ret, hret_end (p + 1) hp1]
    have h_real : (K p : ℝ) ≤ (g p : ℝ) - 2 * (g (p + 1) : ℝ) := by
      linarith [hK_le p hp, h0_ret]
    have h_cast : (((K p : ℤ) : ℝ)) ≤ (((g p - 2 * g (p + 1) : ℤ) : ℝ)) := by
      rw [Int.cast_natCast, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
      exact h_real
    exact Int.cast_le.mp h_cast
  have hlast_g : (K (l - 1) : ℤ) ≤ g (l - 1) := by
    have h0_ret : (F (l - 1) 0).ret = 0 := by
      rw [hR.start, zero_ret]
    have h_real : (K (l - 1) : ℝ) ≤ (g (l - 1) : ℝ) := by
      linarith [hK_le (l - 1) (by omega), h0_ret]
    have h_cast : (((K (l - 1) : ℤ) : ℝ)) ≤ (g (l - 1) : ℝ) := by
      rw [Int.cast_natCast]
      exact h_real
    exact Int.cast_le.mp h_cast
  have htele := sum_range_le_telescope_aux K g hstep_g (l - 1) (by omega)
  have hl_eq : l - 1 + 1 = l := by omega
  rw [hl_eq] at htele
  have hsum_K :
      ((∑ p ∈ Finset.range l, K p : ℕ) : ℤ) =
        ((∑ p ∈ Finset.range (l - 1), K p : ℕ) : ℤ) + (K (l - 1) : ℤ) := by
    conv_lhs => rw [← hl_eq]
    rw [Finset.sum_range_succ, Nat.cast_add]
  have hg0 : g 0 = ((min (∑ i, a i) (∑ j, b j) : ℕ) : ℤ) := by
    dsimp only [g]
    simp only [pow_zero, Nat.div_one]
  have hsum_g :
      (∑ p ∈ Finset.Ico 1 l, ((min (∑ i, a i / 2 ^ p) (∑ j, b j / 2 ^ p) : ℕ) : ℤ)) =
        ∑ p ∈ Finset.Ico 1 l, g p := rfl
  linarith
