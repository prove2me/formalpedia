-- Prove2me | solution 1 for DermanSeqDecisions.LinProg.total_cost_eq_cycle
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T23:12:49.58299+00:00
-- url     : https://prove2.me/submissions/03b4feab-278e-4d65-9193-342bd298361f

import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model
import Definitions.Def_DermanSeqDecisions_LinProg_Model

open Matrix

open scoped ENNReal


namespace DermanSeqDecisions.LinProg

theorem dm_vecMul_pow {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℝ) (w : I → ℝ)
    (hw : w ᵥ* P = w) (k : ℕ) : w ᵥ* (P ^ k) = w := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hw]

theorem dm_inv_zero {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℝ)
    (hP : P.IsIrreducible) (w : I → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : w ᵥ* P = w) (j : I)
    (hj : w j = 0) : ∀ i, w i = 0 := by
  intro i
  obtain ⟨k, -, hk⟩ := (Matrix.isIrreducible_iff_exists_pow_pos hP.nonneg).1 hP i j
  have hPk : ∀ a b, 0 ≤ (P ^ k) a b := fun a b => Matrix.pow_apply_nonneg hP.nonneg k a b
  have h1 := congrFun (dm_vecMul_pow P w hw k) j
  rw [Matrix.vecMul, dotProduct, hj] at h1
  have h2 : w i * (P ^ k) i j ≤ ∑ l, w l * (P ^ k) l j :=
    Finset.single_le_sum (f := fun l => w l * (P ^ k) l j)
      (fun l _ => mul_nonneg (hw0 l) (hPk l j)) (Finset.mem_univ i)
  have : w i * (P ^ k) i j = 0 := le_antisymm (by linarith) (mul_nonneg (hw0 i) (hPk i j))
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · linarith

theorem dm_stat_pos {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℝ)
    (hP : P.IsIrreducible) (π : I → ℝ) (hπ : JewellMRP.InfiniteStep.IsStationary P π) :
    ∀ j, 0 < π j := by
  intro j
  rcases (hπ.1 j).lt_or_eq with h | h
  · exact h
  · have := dm_inv_zero P hP π hπ.1 hπ.2.2 j h.symm
    have h2 := hπ.2.1
    simp [this] at h2

theorem fsc_core {I Act : Type*} [Fintype I] [DecidableEq I] [Fintype Act]
    (q : I → Act → I → ℝ) (hq : IsTransitionLaw q)
    (hA : ∀ D : I → Act → ℝ, IsStationaryRandomized D → (chainMatrix q D).IsIrreducible) :
    (∀ D : I → Act → ℝ, IsStationaryRandomized D → ∀ π : I → ℝ,
      JewellMRP.InfiniteStep.IsStationary (chainMatrix q D) π →
      IsFreqSolution q (fun j k => π j * D j k) ∧ ∀ j, 0 < ∑ k, π j * D j k) ∧
    ∀ x : I → Act → ℝ, IsFreqSolution q x →
      (∀ j, 0 < ∑ k, x j k) ∧ IsStationaryRandomized (decode x) ∧
      JewellMRP.InfiniteStep.IsStationary (chainMatrix q (decode x)) (fun j => ∑ k, x j k) ∧
      ∀ j k, x j k = (∑ k', x j k') * decode x j k := by
  constructor
  · intro D hD π hπ
    have hpos := dm_stat_pos _ (hA D hD) π hπ
    have hrow : ∀ j, ∑ k, π j * D j k = π j := by
      intro j; rw [← Finset.mul_sum, hD.2 j, mul_one]
    refine ⟨⟨fun j k => mul_nonneg (hπ.1 j) (hD.1 j k), ?_, ?_⟩, ?_⟩
    · intro j
      have h := congrFun hπ.2.2 j
      simp only [Matrix.vecMul, dotProduct, chainMatrix, Matrix.of_apply] at h
      rw [hrow j]
      have : ∑ i, ∑ k, π i * D i k * q i k j = ∑ i, π i * ∑ a, q i a j * D i a := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => by ring
      rw [this, h]; ring
    · simp_rw [hrow]; exact hπ.2.1
    · intro j; rw [hrow]; exact hpos j
  · intro x hx
    obtain ⟨hx0, hbal, hsum⟩ := hx
    set s : I → ℝ := fun j => ∑ k, x j k with hs
    have hs0 : ∀ j, 0 ≤ s j := fun j => Finset.sum_nonneg fun k _ => hx0 j k
    have hAct : Nonempty Act := by
      by_contra h
      rw [not_nonempty_iff] at h
      have h0 : ∀ j, s j = 0 := fun j => by simp [hs]
      simp [h0] at hsum
    let D' : I → Act → ℝ := fun j k => if s j = 0 then (Fintype.card Act : ℝ)⁻¹ else x j k / s j
    have hcard : (0 : ℝ) < Fintype.card Act := by exact_mod_cast Fintype.card_pos
    have hD' : IsStationaryRandomized D' := by
      refine ⟨fun j k => ?_, fun j => ?_⟩
      · simp only [D']; split_ifs
        · positivity
        · exact div_nonneg (hx0 j k) (hs0 j)
      · simp only [D']; split_ifs with h
        · simp [Finset.card_univ]
        · rw [← Finset.sum_div]; exact div_self h
    have hmul : ∀ i k, s i * D' i k = x i k := by
      intro i k
      simp only [D']; split_ifs with h
      · have : x i k = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hx0 i k)).1 h k
          (Finset.mem_univ k)
        rw [h, this, zero_mul]
      · field_simp
    have hstat : JewellMRP.InfiniteStep.IsStationary (chainMatrix q D') s := by
      refine ⟨hs0, hsum, ?_⟩
      funext j
      simp only [Matrix.vecMul, dotProduct, chainMatrix, Matrix.of_apply]
      have : ∑ i, s i * ∑ a, q i a j * D' i a = ∑ i, ∑ k, x i k * q i k j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_
        rw [← hmul i a]; ring
      rw [this]; linarith [hbal j]
    have hpos := dm_stat_pos _ (hA D' hD') s hstat
    have hdec : decode x = D' := by
      funext j k
      simp only [decode, D']
      rw [if_neg (hpos j).ne']
    refine ⟨hpos, hdec ▸ hD', hdec ▸ hstat, ?_⟩
    intro j k
    rw [hdec]; exact (hmul j k).symm


theorem dm_unique {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℝ)
    (hP : P.IsIrreducible) (π : I → ℝ) (hπ : JewellMRP.InfiniteStep.IsStationary P π)
    (u : I → ℝ) (hu : u ᵥ* P = u) : ∃ c : ℝ, u = c • π := by
  have hpos := dm_stat_pos P hP π hπ
  have hne : (Finset.univ : Finset I).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := hπ.2.1; rw [h] at this; simp at this
  obtain ⟨j0, -, hj0⟩ := Finset.exists_min_image Finset.univ (fun j => u j / π j) hne
  set c := u j0 / π j0
  refine ⟨c, ?_⟩
  set w := u - c • π with hw
  have hw0 : ∀ i, 0 ≤ w i := by
    intro i
    have := hj0 i (Finset.mem_univ i)
    simp only [hw, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have := (le_div_iff₀ (hpos i)).1 this
    linarith
  have hwP : w ᵥ* P = w := by
    rw [hw, Matrix.sub_vecMul, Matrix.smul_vecMul, hu, hπ.2.2]
  have hwj : w j0 = 0 := by
    simp only [hw, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, c]
    field_simp [(hpos j0).ne']; ring
  have := dm_inv_zero P hP w hw0 hwP j0 hwj
  funext i
  have := this i
  simp only [hw, Pi.sub_apply] at this
  linarith

theorem dm_range {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℝ)
    (hP : P.IsIrreducible) (π : I → ℝ) (hπ : JewellMRP.InfiniteStep.IsStationary P π)
    (h : I → ℝ) (hh : π ⬝ᵥ h = 0) : ∃ y : I → ℝ, y - P *ᵥ y = h := by
  have hpos := dm_stat_pos P hP π hπ
  set A : Matrix I I ℝ := 1 - P
  let W : Submodule ℝ (I → ℝ) :=
    { carrier := {v | π ⬝ᵥ v = 0}
      add_mem' := by intro a b ha hb; simp_all [dotProduct_add]
      zero_mem' := by simp
      smul_mem' := by intro c v hv; simp_all [dotProduct_smul] }
  have hrangeW : LinearMap.range A.mulVecLin ≤ W := by
    rintro v ⟨y, rfl⟩
    show π ⬝ᵥ (A *ᵥ y) = 0
    rw [Matrix.dotProduct_mulVec]
    have : π ᵥ* A = 0 := by
      simp only [A, Matrix.vecMul_sub, Matrix.vecMul_one, hπ.2.2, sub_self]
    rw [this, zero_dotProduct]
  have hWtop : W ≠ ⊤ := by
    intro htop
    have : π ∈ W := htop ▸ Submodule.mem_top
    have h2 : π ⬝ᵥ π = 0 := this
    have h3 : 0 < π ⬝ᵥ π := by
      have hne : (Finset.univ : Finset I).Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        have := hπ.2.1; rw [h] at this; simp at this
      obtain ⟨j, -⟩ := hne
      exact Finset.sum_pos' (fun i _ => mul_self_nonneg _) ⟨j, Finset.mem_univ _,
        mul_pos (hpos j) (hpos j)⟩
    linarith
  have hWlt := Submodule.finrank_lt hWtop
  have hker : LinearMap.ker Aᵀ.mulVecLin ≤ Submodule.span ℝ {π} := by
    intro u hu
    have hu' : Aᵀ *ᵥ u = 0 := hu
    rw [Matrix.mulVec_transpose] at hu'
    have : u ᵥ* P = u := by
      simp only [A, Matrix.vecMul_sub, Matrix.vecMul_one] at hu'
      exact (sub_eq_zero.1 hu').symm
    obtain ⟨c, hc⟩ := dm_unique P hP π hπ u this
    rw [Submodule.mem_span_singleton]; exact ⟨c, hc.symm⟩
  have hk1 : Module.finrank ℝ (LinearMap.ker Aᵀ.mulVecLin) ≤ 1 := by
    refine (Submodule.finrank_mono hker).trans ?_
    refine (finrank_span_le_card ({π} : Set (I → ℝ))).trans ?_
    simp
  have hrn := LinearMap.finrank_range_add_finrank_ker Aᵀ.mulVecLin
  have hrk : A.rank = Aᵀ.rank := (Matrix.rank_transpose A).symm
  simp only [Matrix.rank] at hrk
  simp only [Module.finrank_fintype_fun_eq_card] at hrn hWlt
  have hEq : LinearMap.range A.mulVecLin = W := by
    refine Submodule.eq_of_le_of_finrank_le hrangeW ?_
    omega
  have : h ∈ LinearMap.range A.mulVecLin := hEq ▸ (show π ⬝ᵥ h = 0 from hh)
  obtain ⟨y, hy⟩ := this
  refine ⟨y, ?_⟩
  have hy' : A *ᵥ y = h := hy
  simpa [A, Matrix.sub_mulVec] using hy'

theorem dm_chain_nonneg {I Act : Type*} [Fintype I] [Fintype Act] (q : I → Act → I → ℝ)
    (hq : IsTransitionLaw q) (D : I → Act → ℝ) (hD : IsStationaryRandomized D) :
    ∀ i j, 0 ≤ chainMatrix q D i j := fun i j =>
  Finset.sum_nonneg fun a _ => mul_nonneg (hq.1 i a j) (hD.1 i a)

theorem dm_chain_row {I Act : Type*} [Fintype I] [Fintype Act] (q : I → Act → I → ℝ)
    (hq : IsTransitionLaw q) (D : I → Act → ℝ) (hD : IsStationaryRandomized D) :
    ∀ i, ∑ j, chainMatrix q D i j = 1 := by
  intro i
  simp only [chainMatrix, Matrix.of_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hq.2 i, one_mul]
  exact hD.2 i

theorem dm_pow_row {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1) : ∀ t i, ∑ j, (P ^ t) i j = 1 := by
  intro t
  induction t with
  | zero => intro i; simp [Matrix.one_apply]
  | succ t ih =>
    intro i
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hrow, mul_one]
    exact ih i

theorem dm_pow_le_one {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℝ)
    (h0 : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1) (t : ℕ) (i j : I) :
    (P ^ t) i j ≤ 1 := by
  rw [← dm_pow_row P hrow t i]
  exact Finset.single_le_sum (f := fun j => (P ^ t) i j)
    (fun l _ => Matrix.pow_apply_nonneg h0 t i l) (Finset.mem_univ j)

theorem acs_core {S Act : Type*} [Fintype S] [DecidableEq S] [Fintype Act]
    (q : S → Act → S → ℝ) (w : S → Act → ℝ) (hq : IsTransitionLaw q)
    (hA : ∀ D : S → Act → ℝ, IsStationaryRandomized D → (chainMatrix q D).IsIrreducible)
    (D : S → Act → ℝ) (hD : IsStationaryRandomized D)
    (π : S → ℝ) (hπ : JewellMRP.InfiniteStep.IsStationary (chainMatrix q D) π) :
    ∀ i, avgCost q w D i = ∑ j, π j * ∑ a, D j a * w j a := by
  intro i
  set P := chainMatrix q D with hPdef
  have hP := hA D hD
  have h0 := dm_chain_nonneg q hq D hD
  have hrow := dm_chain_row q hq D hD
  set g : S → ℝ := fun j => ∑ a, D j a * w j a with hg
  set c := ∑ j, π j * g j with hc
  set h : S → ℝ := fun j => g j - c with hh
  have hπh : π ⬝ᵥ h = 0 := by
    simp only [dotProduct, hh, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ.2.1]
    simp [hc, g]
  obtain ⟨y, hy⟩ := dm_range P hP π hπ h hπh
  have hexp : ∀ t, expCost q w D i t = c + ((P ^ t) *ᵥ y) i - ((P ^ (t+1)) *ᵥ y) i := by
    intro t
    simp only [expCost]
    rw [← hPdef]
    have e1 : ∑ j, (P ^ t) i j * ∑ a, D j a * w j a = ∑ j, (P ^ t) i j * (h j + c) := by
      refine Finset.sum_congr rfl fun j _ => ?_; simp [hh, g]
    rw [e1]
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, dm_pow_row P hrow t i, one_mul]
    have : h = y - P *ᵥ y := hy.symm
    rw [this]
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    have e2 : ∑ x, (P ^ t) i x * ∑ x_1, P x x_1 * y x_1 = ∑ x, (P ^ (t+1)) i x * y x := by
      simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e2]; ring
  have hsum : ∀ T, ∑ t ∈ Finset.range (T + 1), expCost q w D i t
      = (T + 1) * c + y i - ((P ^ (T+1)) *ᵥ y) i := by
    intro T
    induction T with
    | zero => simp [hexp]
    | succ T ih =>
      rw [Finset.sum_range_succ, ih, hexp]; push_cast; ring
  set B := ∑ j, |y j|
  have hbd : ∀ t, |((P ^ t) *ᵥ y) i| ≤ B := by
    intro t
    simp only [Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_of_nonneg (Matrix.pow_apply_nonneg h0 t i j)]
    have := dm_pow_le_one P h0 hrow t i j
    nlinarith [abs_nonneg (y j)]
  have htend : Filter.Tendsto
      (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range (T + 1), expCost q w D i t)
      Filter.atTop (nhds c) := by
    have hrem : Filter.Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * (c + y i - ((P ^ (T+1)) *ᵥ y) i))
        Filter.atTop (nhds 0) := by
      have hb : ∀ T : ℕ, |c + y i - ((P ^ (T+1)) *ᵥ y) i| ≤ |c| + |y i| + B := by
        intro T
        have := hbd (T+1)
        calc |c + y i - ((P ^ (T+1)) *ᵥ y) i| ≤ |c + y i| + |((P ^ (T+1)) *ᵥ y) i| :=
              abs_sub _ _
          _ ≤ |c| + |y i| + B := by linarith [abs_add_le c (y i)]
      have ht := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const
        (|c| + |y i| + B)
      rw [zero_mul] at ht
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun T => norm_nonneg _) (fun T => ?_) ht
      simp only [Function.comp, Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (hb T) (by positivity)
    · have hev : ∀ᶠ T : ℕ in Filter.atTop,
          c + (T : ℝ)⁻¹ * (c + y i - ((P ^ (T+1)) *ᵥ y) i) =
          (T : ℝ)⁻¹ * ∑ t ∈ Finset.range (T + 1), expCost q w D i t := by
        filter_upwards [Filter.eventually_ge_atTop 1] with T hT
        rw [hsum]
        have : (T : ℝ) ≠ 0 := by positivity
        field_simp; ring
      have := (tendsto_const_nhds (x := c)).add hrem
      simp only [add_zero] at this
      exact this.congr' hev
  exact htend.limsup_eq


section Taboo
variable {I : Type*} [Fintype I] [DecidableEq I]

def tabQ (P : Matrix I I ℝ) (i : I) : Matrix I I ℝ := Matrix.of fun l j => if l = i then 0 else P l j

theorem dm_maxp (P : Matrix I I ℝ) (h0 : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1)
    (hirr : P.IsIrreducible) (i : I) (u : I → ℝ) (hu : ∀ l, l ≠ i → u l = ∑ j, P l j * u j)
    (hi : u i = 0) : ∀ l, u l ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨l1, hl1⟩ := hcon
  obtain ⟨l0, -, hl0⟩ := Finset.exists_max_image Finset.univ u ⟨l1, Finset.mem_univ _⟩
  set M := u l0
  have hM : 0 < M := lt_of_lt_of_le hl1 (hl0 l1 (Finset.mem_univ _))
  have hZ : ∀ m, u m = M → ∀ j, 0 < P m j → u j = M := by
    intro m hm j hj
    have hmi : m ≠ i := by intro h; rw [h, hi] at hm; linarith
    have hs : ∑ k, P m k * (M - u k) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hrow m, one_mul]
      rw [← hu m hmi, hm, sub_self]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (h0 m k)
      (sub_nonneg.2 (hl0 k (Finset.mem_univ _))))).1 hs j (Finset.mem_univ _)
    rcases mul_eq_zero.1 hz with h | h
    · linarith
    · linarith
  have hk : ∀ k j, 0 < (P ^ k) l0 j → u j = M := by
    intro k
    induction k with
    | zero =>
      intro j hj
      rw [pow_zero, Matrix.one_apply] at hj
      split_ifs at hj with h
      · rw [← h]
      · linarith
    | succ k ih =>
      intro j hj
      rw [pow_succ, Matrix.mul_apply] at hj
      obtain ⟨m, -, hm⟩ := (Finset.sum_pos_iff_of_nonneg (fun m _ => mul_nonneg
        (Matrix.pow_apply_nonneg h0 k l0 m) (h0 m j))).1 hj
      have h1 : 0 < (P ^ k) l0 m := by
        rcases (Matrix.pow_apply_nonneg h0 k l0 m).lt_or_eq with h | h
        · exact h
        · rw [← h, zero_mul] at hm; exact absurd hm (lt_irrefl 0)
      have h2 : 0 < P m j := by
        rcases (h0 m j).lt_or_eq with h | h
        · exact h
        · rw [← h, mul_zero] at hm; exact absurd hm (lt_irrefl 0)
      exact hZ m (ih m h1) j h2
  obtain ⟨k, -, hk'⟩ := (Matrix.isIrreducible_iff_exists_pow_pos hirr.nonneg).1 hirr l0 i
  have := hk k i hk'
  linarith

theorem dm_Q_unit (P : Matrix I I ℝ) (h0 : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1)
    (hirr : P.IsIrreducible) (i : I) : IsUnit (1 - tabQ P i) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ u : I → ℝ, (1 - tabQ P i) *ᵥ u = 0 → u = 0 := by
    intro u hu
    have hu' : ∀ l, u l = (tabQ P i *ᵥ u) l := by
      intro l
      have := congrFun hu l
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.zero_apply] at this
      linarith
    have hi : u i = 0 := by
      rw [hu' i]; simp [Matrix.mulVec, dotProduct, tabQ]
    have harm : ∀ l, l ≠ i → u l = ∑ j, P l j * u j := by
      intro l hl
      rw [hu' l]; simp [Matrix.mulVec, dotProduct, tabQ, hl]
    have h1 := dm_maxp P h0 hrow hirr i u harm hi
    have h2 := dm_maxp P h0 hrow hirr i (-u) (by
      intro l hl; simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, harm l hl])
      (by simp [hi])
    funext l
    have := h2 l
    simp only [Pi.neg_apply] at this
    simp only [Pi.zero_apply]; linarith [h1 l]
  intro a b hab
  have := key (a - b) (by rw [Matrix.mulVec_sub, hab, sub_self])
  exact sub_eq_zero.1 this

theorem dm_taboo_eq (P : Matrix I I ℝ) (i : I) (t : ℕ) :
    tabooProb P i (t + 1) = (fun j => P i j) ᵥ* (tabQ P i) ^ t := by
  induction t with
  | zero => funext j; simp [tabooProb]
  | succ t ih =>
    rw [pow_succ, ← Matrix.vecMul_vecMul, ← ih]
    funext j
    show ∑ l, (if l = i then 0 else tabooProb P i (t + 1) l) * P l j = _
    simp only [Matrix.vecMul, dotProduct, tabQ, Matrix.of_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp

theorem dm_Q_nonneg (P : Matrix I I ℝ) (h0 : ∀ a b, 0 ≤ P a b) (i : I) :
    ∀ a b, 0 ≤ tabQ P i a b := by
  intro a b; simp only [tabQ, Matrix.of_apply]; split_ifs
  · exact le_rfl
  · exact h0 a b

theorem dm_Q_pow_row (P : Matrix I I ℝ) (h0 : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1)
    (i : I) : ∀ n a, ∑ b, (tabQ P i ^ n) a b ≤ 1 := by
  intro n
  induction n with
  | zero => intro a; simp [Matrix.one_apply]
  | succ n ih =>
    intro a
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    calc ∑ y, ∑ x, (tabQ P i ^ n) a y * tabQ P i y x
        = ∑ y, (tabQ P i ^ n) a y * ∑ x, tabQ P i y x := by simp_rw [Finset.mul_sum]
      _ ≤ ∑ y, (tabQ P i ^ n) a y * 1 := by
          refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_
            (Matrix.pow_apply_nonneg (dm_Q_nonneg P h0 i) n a y)
          simp only [tabQ, Matrix.of_apply]; split_ifs
          · simp
          · rw [hrow y]
      _ ≤ 1 := by simp only [mul_one]; exact ih a

theorem dm_taboo_nonneg (P : Matrix I I ℝ) (h0 : ∀ a b, 0 ≤ P a b) (i : I) :
    ∀ t j, 0 ≤ tabooProb P i t j := by
  intro t j
  cases t with
  | zero => simp [tabooProb]
  | succ t =>
    rw [dm_taboo_eq]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (h0 i l)
      (Matrix.pow_apply_nonneg (dm_Q_nonneg P h0 i) t l j)

theorem dm_taboo_summable (P : Matrix I I ℝ) (h0 : ∀ a b, 0 ≤ P a b)
    (hrow : ∀ a, ∑ b, P a b = 1) (hirr : P.IsIrreducible) (i : I) :
    ∀ j, Summable (fun t : ℕ => tabooProb P i t j) := by
  intro j
  set Q := tabQ P i
  have hU := dm_Q_unit P h0 hrow hirr i
  have hdet : IsUnit (1 - Q).det := (Matrix.isUnit_iff_isUnit_det _).1 hU
  set R := (1 - Q)⁻¹
  have hR : (1 - Q) * R = 1 := Matrix.mul_nonsing_inv _ hdet
  have hgeom : ∀ n, ∑ t ∈ Finset.range n, Q ^ t = (1 - Q ^ n) * R := by
    intro n
    have h1 : (∑ t ∈ Finset.range n, Q ^ t) * (1 - Q) = 1 - Q ^ n := by
      have := geom_sum_mul Q n
      rw [← neg_sub Q 1, mul_neg, this, neg_sub]
    calc ∑ t ∈ Finset.range n, Q ^ t = (∑ t ∈ Finset.range n, Q ^ t) * ((1 - Q) * R) := by
          rw [hR, mul_one]
      _ = (1 - Q ^ n) * R := by rw [← mul_assoc, h1]
  set B := ∑ k, |R k j|
  have hQn : ∀ n a b, 0 ≤ (Q ^ n) a b ∧ (Q ^ n) a b ≤ 1 := by
    intro n a b
    refine ⟨Matrix.pow_apply_nonneg (dm_Q_nonneg P h0 i) n a b, ?_⟩
    refine le_trans ?_ (dm_Q_pow_row P h0 hrow i n a)
    exact Finset.single_le_sum (f := fun b => (Q ^ n) a b)
      (fun b _ => Matrix.pow_apply_nonneg (dm_Q_nonneg P h0 i) n a b) (Finset.mem_univ b)
  have hbd : ∀ n l, ((1 - Q ^ n) * R : Matrix I I ℝ) l j ≤ B := by
    intro n l
    rw [Matrix.mul_apply]
    refine le_trans (Finset.sum_le_sum fun k _ => le_abs_self _) (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    have : |(1 - Q ^ n) l k| ≤ 1 := by
      obtain ⟨a1, a2⟩ := hQn n l k
      rw [Matrix.sub_apply, Matrix.one_apply, abs_le]
      split_ifs <;> constructor <;> linarith
    nlinarith [abs_nonneg (R k j)]
  have hps : ∀ n, ∑ t ∈ Finset.range n, tabooProb P i (t + 1) j
      = ((fun j => P i j) ᵥ* ∑ t ∈ Finset.range n, Q ^ t) j := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Matrix.vecMul_add, Pi.add_apply,
        dm_taboo_eq]
  have hs1 : Summable (fun t : ℕ => tabooProb P i (t + 1) j) := by
    refine summable_of_sum_range_le (c := B) (fun t => dm_taboo_nonneg P h0 i _ j) (fun n => ?_)
    rw [hps, hgeom]
    simp only [Matrix.vecMul, dotProduct]
    calc ∑ x, P i x * ((1 - Q ^ n) * R) x j ≤ ∑ x, P i x * B :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hbd n x) (h0 i x)
      _ = B := by rw [← Finset.sum_mul, hrow i, one_mul]
  exact (summable_nat_add_iff 1).1 hs1

theorem tab_core (P : Matrix I I ℝ) (hP : JewellMRP.InfiniteStep.IsErgodic P)
    (π : I → ℝ) (hπ : JewellMRP.InfiniteStep.IsStationary P π) (f : I → ℝ) (i : I) :
    (∀ j, Summable (fun t : ℕ => tabooProb P i t j)) ∧
    HasSum (fun t : ℕ => ∑ j, tabooProb P i t j * f j) (∑ j, ∑' t : ℕ, tabooProb P i t j * f j) ∧
    ∑ j, ∑' t : ℕ, tabooProb P i t j * f j = (1 / π i) * ∑ j, π j * f j := by
  obtain ⟨h0, hrow⟩ := Matrix.mem_rowStochastic_iff_sum.1 hP.1
  have hirr := hP.2
  have hsum := dm_taboo_summable P h0 hrow hirr i
  refine ⟨hsum, ?_, ?_⟩
  · have := hasSum_sum (s := Finset.univ) fun j _ => (hsum j).hasSum.mul_right (f j)
    simpa [tsum_mul_right] using this
  · set T := tabooProb P i
    set v : I → ℝ := fun j => ∑' t, T t j with hv
    have hT0 : ∀ j, T 0 j = 0 := fun j => rfl
    have hv1 : ∀ j, v j = ∑' t, T (t + 1) j := by
      intro j; simp only [hv]; rw [(hsum j).tsum_eq_zero_add, hT0, zero_add]
    have hs1 : ∀ j, Summable (fun t => T (t + 1) j) := fun j => (summable_nat_add_iff 1).2 (hsum j)
    have hrec : ∀ t j, T (t + 2) j = ∑ l, (if l = i then 0 else T (t + 1) l) * P l j :=
      fun t j => rfl
    -- v = P i + (zeroed v) P
    have hvrec : ∀ j, v j = P i j + ∑ l, (if l = i then 0 else v l) * P l j := by
      intro j
      rw [hv1 j, (hs1 j).tsum_eq_zero_add]
      congr 1
      simp_rw [show ∀ t, T (t + 1 + 1) j = T (t + 2) j from fun t => rfl, hrec]
      rw [Summable.tsum_finsetSum]
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [tsum_mul_right]
        split_ifs
        · simp
        · rw [hv1 l]
      · intro l _
        refine Summable.mul_right _ ?_
        split_ifs
        · exact summable_zero
        · exact hs1 l
    -- v i = 1
    set s : ℕ → ℝ := fun t => ∑ j, T t j
    have hss : Summable s := summable_sum fun j _ => hsum j
    have hsrec : ∀ t, s (t + 2) = s (t + 1) - T (t + 1) i := by
      intro t
      simp only [s]
      simp_rw [hrec]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hrow, mul_one]
      have : ∀ l, (if l = i then (0:ℝ) else T (t + 1) l) = T (t+1) l - if l = i then T (t+1) l else 0 := by
        intro l; split_ifs <;> simp
      simp_rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hs1v : s 1 = 1 := by simp only [s]; exact hrow i
    have hpart : ∀ n, ∑ t ∈ Finset.range n, T (t + 1) i = 1 - s (n + 1) := by
      intro n
      induction n with
      | zero => simp [hs1v]
      | succ n ih => rw [Finset.sum_range_succ, ih, hsrec]; ring
    have hlim : Filter.Tendsto (fun n => ∑ t ∈ Finset.range n, T (t + 1) i) Filter.atTop
        (nhds 1) := by
      simp_rw [hpart]
      have := ((summable_nat_add_iff 1).2 hss).tendsto_atTop_zero
      simpa using (tendsto_const_nhds (x := (1:ℝ))).sub this
    have hvi : v i = 1 := by
      rw [hv1 i]
      exact tendsto_nhds_unique (hs1 i).hasSum.tendsto_sum_nat hlim
    have hvP : v ᵥ* P = v := by
      funext j
      rw [hvrec j]
      simp only [Matrix.vecMul, dotProduct]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      simp only [if_true, zero_mul, zero_add, hvi, one_mul]
      congr 1
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [if_neg (Finset.ne_of_mem_erase hl)]
    obtain ⟨c, hc⟩ := dm_unique P hirr π hπ v hvP
    have hpos := dm_stat_pos P hirr π hπ
    have hci : c = 1 / π i := by
      have := congrFun hc i
      rw [hvi] at this
      simp only [Pi.smul_apply, smul_eq_mul] at this
      field_simp [(hpos i).ne']; linarith
    simp_rw [tsum_mul_right]
    show ∑ j, v j * f j = _
    rw [hc, hci, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]; ring

end Taboo


section Transient
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem dm_maxp' (P : Matrix I I ℝ) (h0 : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1)
    (i : I) (hreach : ∀ l, ∃ k, 0 < (P ^ k) l i)
    (u : I → ℝ) (hu : ∀ l, l ≠ i → u l = ∑ j, P l j * u j)
    (hi : u i = 0) : ∀ l, u l ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨l1, hl1⟩ := hcon
  obtain ⟨l0, -, hl0⟩ := Finset.exists_max_image Finset.univ u ⟨l1, Finset.mem_univ _⟩
  set M := u l0
  have hM : 0 < M := lt_of_lt_of_le hl1 (hl0 l1 (Finset.mem_univ _))
  have hZ : ∀ m, u m = M → ∀ j, 0 < P m j → u j = M := by
    intro m hm j hj
    have hmi : m ≠ i := by intro h; rw [h, hi] at hm; linarith
    have hs : ∑ k, P m k * (M - u k) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hrow m, one_mul]
      rw [← hu m hmi, hm, sub_self]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (h0 m k)
      (sub_nonneg.2 (hl0 k (Finset.mem_univ _))))).1 hs j (Finset.mem_univ _)
    rcases mul_eq_zero.1 hz with h | h
    · linarith
    · linarith
  have hk : ∀ k j, 0 < (P ^ k) l0 j → u j = M := by
    intro k
    induction k with
    | zero =>
      intro j hj
      rw [pow_zero, Matrix.one_apply] at hj
      split_ifs at hj with h
      · rw [← h]
      · linarith
    | succ k ih =>
      intro j hj
      rw [pow_succ, Matrix.mul_apply] at hj
      obtain ⟨m, -, hm⟩ := (Finset.sum_pos_iff_of_nonneg (fun m _ => mul_nonneg
        (Matrix.pow_apply_nonneg h0 k l0 m) (h0 m j))).1 hj
      have h1 : 0 < (P ^ k) l0 m := by
        rcases (Matrix.pow_apply_nonneg h0 k l0 m).lt_or_eq with h | h
        · exact h
        · rw [← h, zero_mul] at hm; exact absurd hm (lt_irrefl 0)
      have h2 : 0 < P m j := by
        rcases (h0 m j).lt_or_eq with h | h
        · exact h
        · rw [← h, mul_zero] at hm; exact absurd hm (lt_irrefl 0)
      exact hZ m (ih m h1) j h2
  obtain ⟨k, hk'⟩ := hreach l0
  have := hk k i hk'
  linarith

theorem dm_Q_unit' (P : Matrix I I ℝ) (h0 : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1)
    (i : I) (hreach : ∀ l, ∃ k, 0 < (P ^ k) l i) : IsUnit (1 - tabQ P i) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ u : I → ℝ, (1 - tabQ P i) *ᵥ u = 0 → u = 0 := by
    intro u hu
    have hu' : ∀ l, u l = (tabQ P i *ᵥ u) l := by
      intro l
      have := congrFun hu l
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.zero_apply] at this
      linarith
    have hi : u i = 0 := by
      rw [hu' i]; simp [Matrix.mulVec, dotProduct, tabQ]
    have harm : ∀ l, l ≠ i → u l = ∑ j, P l j * u j := by
      intro l hl
      rw [hu' l]; simp [Matrix.mulVec, dotProduct, tabQ, hl]
    have h1 := dm_maxp' P h0 hrow i hreach u harm hi
    have h2 := dm_maxp' P h0 hrow i hreach (-u) (by
      intro l hl; simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, harm l hl])
      (by simp [hi])
    funext l
    have := h2 l
    simp only [Pi.neg_apply] at this
    simp only [Pi.zero_apply]; linarith [h1 l]
  intro a b hab
  have := key (a - b) (by rw [Matrix.mulVec_sub, hab, sub_self])
  exact sub_eq_zero.1 this

theorem dm_Q_hasSum (P : Matrix I I ℝ) (h0 : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1)
    (i : I) (hU : IsUnit (1 - tabQ P i)) :
    ∀ l j, HasSum (fun t => (tabQ P i ^ t) l j) ((1 - tabQ P i)⁻¹ l j) := by
  set Q := tabQ P i
  have hdet : IsUnit (1 - Q).det := (Matrix.isUnit_iff_isUnit_det _).1 hU
  set R := (1 - Q)⁻¹
  have hR : (1 - Q) * R = 1 := Matrix.mul_nonsing_inv _ hdet
  have hR' : R * (1 - Q) = 1 := Matrix.nonsing_inv_mul _ hdet
  have hgeom : ∀ n, ∑ t ∈ Finset.range n, Q ^ t = (1 - Q ^ n) * R := by
    intro n
    have h1 : (∑ t ∈ Finset.range n, Q ^ t) * (1 - Q) = 1 - Q ^ n := by
      have := geom_sum_mul Q n
      rw [← neg_sub Q 1, mul_neg, this, neg_sub]
    calc ∑ t ∈ Finset.range n, Q ^ t = (∑ t ∈ Finset.range n, Q ^ t) * ((1 - Q) * R) := by
          rw [hR, mul_one]
      _ = (1 - Q ^ n) * R := by rw [← mul_assoc, h1]
  have hQn : ∀ n a b, 0 ≤ (Q ^ n) a b ∧ (Q ^ n) a b ≤ 1 := by
    intro n a b
    refine ⟨Matrix.pow_apply_nonneg (dm_Q_nonneg P h0 i) n a b, ?_⟩
    refine le_trans ?_ (dm_Q_pow_row P h0 hrow i n a)
    exact Finset.single_le_sum (f := fun b => (Q ^ n) a b)
      (fun b _ => Matrix.pow_apply_nonneg (dm_Q_nonneg P h0 i) n a b) (Finset.mem_univ b)
  have hsumm : ∀ l j, Summable (fun t => (Q ^ t) l j) := by
    intro l j
    refine summable_of_sum_range_le (c := ∑ k, |R k j|) (fun t => (hQn t l j).1) (fun n => ?_)
    have : ∑ t ∈ Finset.range n, (Q ^ t) l j = (∑ t ∈ Finset.range n, Q ^ t) l j := by
      rw [Matrix.sum_apply]
    rw [this, hgeom, Matrix.mul_apply]
    refine le_trans (Finset.sum_le_sum fun k _ => le_abs_self _) (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    have : |(1 - Q ^ n) l k| ≤ 1 := by
      obtain ⟨a1, a2⟩ := hQn n l k
      rw [Matrix.sub_apply, Matrix.one_apply, abs_le]
      split_ifs <;> constructor <;> linarith
    nlinarith [abs_nonneg (R k j)]
  set M : Matrix I I ℝ := Matrix.of fun l j => ∑' t, (Q ^ t) l j
  have hM : (1 - Q) * M = 1 := by
    have hfix : M = 1 + Q * M := by
      ext l j
      simp only [M, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
      rw [(hsumm l j).tsum_eq_zero_add, pow_zero]
      congr 1
      simp_rw [pow_succ', Matrix.mul_apply]
      rw [Summable.tsum_finsetSum (fun k _ => (hsumm k j).mul_left _)]
      simp_rw [tsum_mul_left]
    calc (1 - Q) * M = M - Q * M := by rw [sub_mul, one_mul]
      _ = 1 := sub_eq_iff_eq_add.2 hfix
  have hMR : M = R := by
    calc M = R * ((1 - Q) * M) := by rw [← mul_assoc, hR', one_mul]
      _ = R := by rw [hM, mul_one]
  intro l j
  have := (hsumm l j).hasSum
  rw [← hMR]; exact this

end Transient

section AMM

variable {S Act : Type*} [Fintype S] [DecidableEq S] [Fintype Act]

def gD (w : S → Act → ℝ) (D : S → Act → ℝ) : S → ℝ := fun j => ∑ a, D j a * w j a

noncomputable def VD (q : S → Act → S → ℝ) (w : S → Act → ℝ) (L : S) (D : S → Act → ℝ) : S → ℝ :=
  (1 - tabQ (chainMatrix q D) L)⁻¹ *ᵥ gD w D

theorem dm_absorb (q : S → Act → S → ℝ) (L : S) (hq : IsTransitionLaw q)
    (hL : ∀ a, q L a L = 1) (D : S → Act → ℝ) (hD : IsStationaryRandomized D) :
    ∀ j, chainMatrix q D L j = if j = L then 1 else 0 := by
  have hz : ∀ a j, j ≠ L → q L a j = 0 := by
    intro a j hj
    have h1 := hq.2 L a
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ L), hL a] at h1
    have h2 : ∑ x ∈ Finset.univ.erase L, q L a x = 0 := by linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hq.1 L a x)).1 h2 j
      (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩)
  intro j
  simp only [chainMatrix, Matrix.of_apply]
  split_ifs with h
  · subst h; simp only [hL, one_mul]; exact hD.2 _
  · simp [hz _ j h]

theorem dm_PQ (q : S → Act → S → ℝ) (L : S) (hq : IsTransitionLaw q)
    (hL : ∀ a, q L a L = 1) (D : S → Act → ℝ) (hD : IsStationaryRandomized D)
    (h : S → ℝ) (hh : h L = 0) :
    chainMatrix q D *ᵥ h = tabQ (chainMatrix q D) L *ᵥ h := by
  funext l
  by_cases hl : l = L
  · subst hl
    simp only [Matrix.mulVec, dotProduct, dm_absorb q l hq hL D hD, tabQ, Matrix.of_apply]
    simp [hh]
  · simp [Matrix.mulVec, dotProduct, tabQ, hl]

theorem dm_reach (q : S → Act → S → ℝ) (L : S)
    (hB : ∀ D : S → Act → ℝ, IsStationaryRandomized D → ∀ i, ∃ t : ℕ, 0 < (chainMatrix q D ^ t) i L)
    (D : S → Act → ℝ) (hD : IsStationaryRandomized D) :
    ∀ l, ∃ k, 0 < (chainMatrix q D ^ k) l L := hB D hD

theorem dm_total (q : S → Act → S → ℝ) (w : S → Act → ℝ) (L : S) (hq : IsTransitionLaw q)
    (hL : ∀ a, q L a L = 1) (hwL : ∀ a, w L a = 0) (hw : ∀ i a, i ≠ L → 0 < w i a)
    (hB : ∀ D : S → Act → ℝ, IsStationaryRandomized D → ∀ i, ∃ t : ℕ, 0 < (chainMatrix q D ^ t) i L)
    (D : S → Act → ℝ) (hD : IsStationaryRandomized D) :
    (∀ i, HasSum (fun t => expCost q w D i t) (VD q w L D i)) ∧ (∀ i, 0 ≤ VD q w L D i) ∧
    (∀ i t, 0 ≤ expCost q w D i t) ∧
    (∀ l j, 0 ≤ (1 - tabQ (chainMatrix q D) L)⁻¹ l j) ∧
    (∀ l, 1 ≤ (1 - tabQ (chainMatrix q D) L)⁻¹ l l) := by
  set P := chainMatrix q D
  have h0 := dm_chain_nonneg q hq D hD
  have hrow := dm_chain_row q hq D hD
  have hU := dm_Q_unit' P h0 hrow L (hB D hD)
  have hS := dm_Q_hasSum P h0 hrow L hU
  set Q := tabQ P L
  set R := (1 - Q)⁻¹
  have hg0 : ∀ j, 0 ≤ gD w D j := by
    intro j
    refine Finset.sum_nonneg fun a _ => mul_nonneg (hD.1 j a) ?_
    by_cases h : j = L
    · rw [h, hwL]
    · exact (hw j a h).le
  have hgL : gD w D L = 0 := by simp [gD, hwL]
  have hpow : ∀ t (h : S → ℝ), h L = 0 → P ^ t *ᵥ h = Q ^ t *ᵥ h := by
    intro t
    induction t with
    | zero => intro h _; simp
    | succ t ih =>
      intro h hh
      have hPh : (P *ᵥ h) L = 0 := by
        simp [Matrix.mulVec, dotProduct, P, dm_absorb q L hq hL D hD, hh]
      rw [pow_succ, ← Matrix.mulVec_mulVec, ih _ hPh, dm_PQ q L hq hL D hD h hh, pow_succ,
        ← Matrix.mulVec_mulVec]
  have hexp : ∀ i t, expCost q w D i t = (Q ^ t *ᵥ gD w D) i := by
    intro i t
    rw [← hpow t _ hgL]; rfl
  have hRnn : ∀ l j, 0 ≤ R l j := fun l j =>
    (hS l j).nonneg fun t => Matrix.pow_apply_nonneg (dm_Q_nonneg P h0 L) t l j
  have hQnn : ∀ t a b, 0 ≤ (Q ^ t) a b := fun t a b =>
    Matrix.pow_apply_nonneg (dm_Q_nonneg P h0 L) t a b
  refine ⟨fun i => ?_, fun i => ?_, fun i t => ?_, hRnn, fun l => ?_⟩
  · simp_rw [hexp]
    have := hasSum_sum (s := Finset.univ) fun j _ => (hS i j).mul_right (gD w D j)
    simpa [Matrix.mulVec, dotProduct, VD] using this
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (hRnn i j) (hg0 j)
  · rw [hexp]; exact Finset.sum_nonneg fun j _ => mul_nonneg (hQnn t i j) (hg0 j)
  · have := (hS l l).nonneg
    have h1 : ∑ t ∈ Finset.range 1, (Q ^ t) l l ≤ R l l :=
      sum_le_hasSum (Finset.range 1) (fun t _ => hQnn t l l) (hS l l)
    simpa using h1

theorem dm_identity (q : S → Act → S → ℝ) (w : S → Act → ℝ) (L : S) (hq : IsTransitionLaw q)
    (hL : ∀ a, q L a L = 1)
    (hB : ∀ D : S → Act → ℝ, IsStationaryRandomized D → ∀ i, ∃ t : ℕ, 0 < (chainMatrix q D ^ t) i L)
    (D : S → Act → ℝ) (hD : IsStationaryRandomized D) (V : S → ℝ) (hV : V L = 0) :
    V = VD q w L D + (1 - tabQ (chainMatrix q D) L)⁻¹ *ᵥ (V - gD w D - chainMatrix q D *ᵥ V) := by
  set P := chainMatrix q D
  have h0 := dm_chain_nonneg q hq D hD
  have hrow := dm_chain_row q hq D hD
  have hU := dm_Q_unit' P h0 hrow L (hB D hD)
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hU
  rw [dm_PQ q L hq hL D hD V hV]
  set Q := tabQ P L
  have : V - gD w D - Q *ᵥ V = (1 - Q) *ᵥ V - gD w D := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  rw [this, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
    Matrix.one_mulVec, VD]
  abel

theorem dm_VD_fix (q : S → Act → S → ℝ) (w : S → Act → ℝ) (L : S) (hq : IsTransitionLaw q)
    (hL : ∀ a, q L a L = 1) (hwL : ∀ a, w L a = 0)
    (hB : ∀ D : S → Act → ℝ, IsStationaryRandomized D → ∀ i, ∃ t : ℕ, 0 < (chainMatrix q D ^ t) i L)
    (D : S → Act → ℝ) (hD : IsStationaryRandomized D) :
    VD q w L D L = 0 ∧ VD q w L D = gD w D + chainMatrix q D *ᵥ VD q w L D := by
  set P := chainMatrix q D
  have h0 := dm_chain_nonneg q hq D hD
  have hrow := dm_chain_row q hq D hD
  have hU := dm_Q_unit' P h0 hrow L (hB D hD)
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have h1 : (1 - tabQ P L) *ᵥ VD q w L D = gD w D := by
    rw [VD, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hLz : VD q w L D L = 0 := by
    have := congrFun h1 L
    simp [Matrix.mulVec, dotProduct, tabQ, gD, hwL, Matrix.one_apply] at this
    exact this
  refine ⟨hLz, ?_⟩
  rw [dm_PQ q L hq hL D hD _ hLz, ← h1, Matrix.sub_mulVec, Matrix.one_mulVec]; abel

theorem dm_r_formula (q : S → Act → S → ℝ) (w : S → Act → ℝ) (D : S → Act → ℝ)
    (hD1 : ∀ l, ∑ a, D l a = 1) (V : S → ℝ) (l : S) :
    (V - gD w D - chainMatrix q D *ᵥ V) l = ∑ a, D l a * (V l - w l a - ∑ j, q l a j * V j) := by
  simp only [Pi.sub_apply, gD, Matrix.mulVec, dotProduct, chainMatrix, Matrix.of_apply,
    mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hD1 l, one_mul]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring

theorem dm_totalCost_eq (q : S → Act → S → ℝ) (w : S → Act → ℝ) (L : S) (hq : IsTransitionLaw q)
    (hL : ∀ a, q L a L = 1) (hwL : ∀ a, w L a = 0) (hw : ∀ i a, i ≠ L → 0 < w i a)
    (hB : ∀ D : S → Act → ℝ, IsStationaryRandomized D → ∀ i, ∃ t : ℕ, 0 < (chainMatrix q D ^ t) i L)
    (D : S → Act → ℝ) (hD : IsStationaryRandomized D) (i : S) :
    totalCost q w D i = ENNReal.ofReal (VD q w L D i) := by
  obtain ⟨hs, -, hnn, -⟩ := dm_total q w L hq hL hwL hw hB D hD
  rw [totalCost, ← (hs i).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (hnn i) (hs i).summable]

theorem amm_core (q : S → Act → S → ℝ) (w : S → Act → ℝ) (L : S) (hq : IsTransitionLaw q)
    (hL : ∀ a, q L a L = 1) (hwL : ∀ a, w L a = 0) (hw : ∀ i a, i ≠ L → 0 < w i a)
    (hB : ∀ D : S → Act → ℝ, IsStationaryRandomized D → ∀ i, ∃ t : ℕ, 0 < (chainMatrix q D ^ t) i L) :
    (∀ D : S → Act → ℝ, IsStationaryRandomized D → ∀ i, totalCost q w D i < ⊤) ∧
    ∀ Dstar : S → Act → ℝ, IsStationaryRandomized Dstar →
      (∀ D : S → Act → ℝ, IsStationaryRandomized D →
        ∑ i, totalCost q w Dstar i ≤ ∑ i, totalCost q w D i) →
      ∀ D : S → Act → ℝ, IsStationaryRandomized D → ∀ i, totalCost q w Dstar i ≤ totalCost q w D i := by
  have hTC := dm_totalCost_eq q w L hq hL hwL hw hB
  refine ⟨fun D hD i => by rw [hTC D hD i]; exact ENNReal.ofReal_lt_top, ?_⟩
  intro Ds hDs hmin
  set V := VD q w L Ds
  obtain ⟨hVL, hVfix⟩ := dm_VD_fix q w L hq hL hwL hB Ds hDs
  have hsumle : ∀ D, IsStationaryRandomized D → ∑ i, V i ≤ ∑ i, VD q w L D i := by
    intro D hD
    have := hmin D hD
    simp only [hTC Ds hDs, hTC D hD] at this
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (dm_total q w L hq hL hwL hw hB Ds hDs).2.1 i),
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => (dm_total q w L hq hL hwL hw hB D hD).2.1 i)] at this
    exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun i _ =>
      (dm_total q w L hq hL hwL hw hB D hD).2.1 i)).1 this
  -- Bellman inequality
  have hbell : ∀ i0 a0, V i0 ≤ w i0 a0 + ∑ j, q i0 a0 j * V j := by
    classical
    intro i0 a0
    by_contra hcon
    push_neg at hcon
    set D' : S → Act → ℝ := fun i a => if i = i0 then (if a = a0 then 1 else 0) else Ds i a
    have hD' : IsStationaryRandomized D' := by
      refine ⟨fun i a => ?_, fun i => ?_⟩
      · simp only [D']; split_ifs
        · norm_num
        · norm_num
        · exact hDs.1 i a
      · simp only [D']; split_ifs
        · simp
        · exact hDs.2 i
    have hid := dm_identity q w L hq hL hB D' hD' V hVL
    set R := (1 - tabQ (chainMatrix q D') L)⁻¹
    obtain ⟨-, -, -, hRnn, hRdiag⟩ := dm_total q w L hq hL hwL hw hB D' hD'
    obtain ⟨r, hrdef⟩ : ∃ r, r = V - gD w D' - chainMatrix q D' *ᵥ V := ⟨_, rfl⟩
    rw [← hrdef] at hid
    have hr : ∀ l, l ≠ i0 → r l = 0 := by
      intro l hl
      have := dm_r_formula q w D' hD'.2 V l
      rw [hrdef, this]
      have h2 := dm_r_formula q w Ds hDs.2 V l
      have h3 : (V - gD w Ds - chainMatrix q Ds *ᵥ V) l = 0 := by
        have := congrFun hVfix l
        simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
        linarith
      rw [h3] at h2
      simp only [D', if_neg hl]
      exact h2.symm
    have hr0 : 0 < r i0 := by
      rw [hrdef, dm_r_formula q w D' hD'.2 V i0]
      simp only [D', if_true, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ]
      linarith
    have hrnn : ∀ l, 0 ≤ r l := by
      intro l; by_cases h : l = i0
      · rw [h]; exact hr0.le
      · rw [hr l h]
    have hRr : ∀ l, 0 ≤ (R *ᵥ r) l := fun l =>
      Finset.sum_nonneg fun k _ => mul_nonneg (hRnn l k) (hrnn k)
    have hRr0 : 0 < (R *ᵥ r) i0 := by
      have : R i0 i0 * r i0 ≤ (R *ᵥ r) i0 :=
        Finset.single_le_sum (f := fun k => R i0 k * r k)
          (fun k _ => mul_nonneg (hRnn i0 k) (hrnn k)) (Finset.mem_univ i0)
      nlinarith [hRdiag i0]
    have hlt : ∑ i, VD q w L D' i < ∑ i, V i := by
      have : ∀ i, V i = VD q w L D' i + (R *ᵥ r) i := fun i => by
        have := congrFun hid i; simpa using this
      simp_rw [this, Finset.sum_add_distrib]
      have : 0 < ∑ i, (R *ᵥ r) i :=
        Finset.sum_pos' (fun i _ => hRr i) ⟨i0, Finset.mem_univ _, hRr0⟩
      linarith
    have := hsumle D' hD'
    linarith
  intro D hD i
  rw [hTC Ds hDs, hTC D hD]
  apply ENNReal.ofReal_le_ofReal
  have hid := dm_identity q w L hq hL hB D hD V hVL
  obtain ⟨-, -, -, hRnn, -⟩ := dm_total q w L hq hL hwL hw hB D hD
  have hrn : ∀ l, (V - gD w D - chainMatrix q D *ᵥ V) l ≤ 0 := by
    intro l
    rw [dm_r_formula q w D hD.2 V l]
    exact Finset.sum_nonpos fun a _ => mul_nonpos_of_nonneg_of_nonpos (hD.1 l a)
      (by linarith [hbell l a])
  have := congrFun hid i
  simp only [Pi.add_apply] at this
  have h2 : ((1 - tabQ (chainMatrix q D) L)⁻¹ *ᵥ (V - gD w D - chainMatrix q D *ᵥ V)) i ≤ 0 :=
    Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (hRnn i k) (hrn k)
  linarith

end AMM


section TCC
variable {S Act : Type*} [Fintype S] [DecidableEq S] [Fintype Act]

theorem dm_exp_eq (q : S → Act → S → ℝ) (w : S → Act → ℝ) (L : S) (hq : IsTransitionLaw q)
    (hL : ∀ a, q L a L = 1) (hwL : ∀ a, w L a = 0)
    (D : S → Act → ℝ) (hD : IsStationaryRandomized D) (i : S) (t : ℕ) :
    expCost q w D i t = (tabQ (chainMatrix q D) L ^ t *ᵥ gD w D) i := by
  set P := chainMatrix q D
  have hgL : gD w D L = 0 := by simp [gD, hwL]
  have hpow : ∀ t (h : S → ℝ), h L = 0 → P ^ t *ᵥ h = tabQ P L ^ t *ᵥ h := by
    intro t
    induction t with
    | zero => intro h _; simp
    | succ t ih =>
      intro h hh
      have hPh : (P *ᵥ h) L = 0 := by
        simp [Matrix.mulVec, dotProduct, P, dm_absorb q L hq hL D hD, hh]
      rw [pow_succ, ← Matrix.mulVec_mulVec, ih _ hPh, dm_PQ q L hq hL D hD h hh, pow_succ,
        ← Matrix.mulVec_mulVec]
  rw [← hpow t _ hgL]; rfl

theorem dm_aug_law (q : S → Act → S → ℝ) (L : S) (hq : IsTransitionLaw q) :
    IsTransitionLaw (augLaw q L) := by
  have hn : (0 : ℝ) < Fintype.card S := by
    have : Nonempty S := ⟨L⟩
    exact_mod_cast Fintype.card_pos
  refine ⟨fun i a j => ?_, fun i a => ?_⟩
  · rcases i with _ | i <;> rcases j with _ | j <;> simp only [augLaw]
    · exact le_rfl
    · positivity
    · split_ifs <;> norm_num
    · split_ifs
      · exact le_rfl
      · exact hq.1 i a j
  · rcases i with _ | i
    · simp only [Fintype.sum_option, augLaw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp; simp
    · simp only [Fintype.sum_option, augLaw]
      split_ifs
      · simp
      · simp [hq.2 i a]

theorem dm_aug_proc (D : S → Act → ℝ) (hD : IsStationaryRandomized D) (D₀ : Act → ℝ)
    (hD₀ : (∀ a, 0 ≤ D₀ a) ∧ ∑ a, D₀ a = 1) : IsStationaryRandomized (augProc D D₀) := by
  refine ⟨fun i a => ?_, fun i => ?_⟩
  · rcases i with _ | i
    · exact hD₀.1 a
    · exact hD.1 i a
  · rcases i with _ | i
    · exact hD₀.2
    · exact hD.2 i

theorem dm_aug_entries (q : S → Act → S → ℝ) (L : S) (D : S → Act → ℝ)
    (hD : IsStationaryRandomized D) (D₀ : Act → ℝ) (hD₀ : (∀ a, 0 ≤ D₀ a) ∧ ∑ a, D₀ a = 1) :
    chainMatrix (augLaw q L) (augProc D D₀) none none = 0 ∧
    (∀ j, chainMatrix (augLaw q L) (augProc D D₀) none (some j) = 1 / (Fintype.card S : ℝ)) ∧
    (∀ i, chainMatrix (augLaw q L) (augProc D D₀) (some i) none = if i = L then 1 else 0) ∧
    (∀ i j, chainMatrix (augLaw q L) (augProc D D₀) (some i) (some j) =
      tabQ (chainMatrix q D) L i j) := by
  refine ⟨?_, fun j => ?_, fun i => ?_, fun i j => ?_⟩
  · simp [chainMatrix, augLaw]
  · simp only [chainMatrix, augLaw, augProc, Matrix.of_apply, ← Finset.mul_sum, hD₀.2, mul_one]
  · simp only [chainMatrix, augLaw, augProc, Matrix.of_apply]
    split_ifs
    · simp [hD.2 i]
    · simp
  · simp only [chainMatrix, augLaw, augProc, Matrix.of_apply, tabQ]
    split_ifs
    · simp
    · rfl

theorem dm_pow_ge {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℝ)
    (h0 : ∀ a b, 0 ≤ P a b) (a b : ℕ) (x m y : I) :
    (P ^ a) x m * (P ^ b) m y ≤ (P ^ (a + b)) x y := by
  rw [pow_add, Matrix.mul_apply]
  exact Finset.single_le_sum (f := fun k => (P ^ a) x k * (P ^ b) k y)
    (fun k _ => mul_nonneg (Matrix.pow_apply_nonneg h0 a x k) (Matrix.pow_apply_nonneg h0 b k y))
    (Finset.mem_univ m)

theorem dm_aug_irred (q : S → Act → S → ℝ) (L : S) (hq : IsTransitionLaw q)
    (hL : ∀ a, q L a L = 1)
    (D : S → Act → ℝ) (hD : IsStationaryRandomized D) (hreach : ∀ i, ∃ t : ℕ, 0 < (chainMatrix q D ^ t) i L)
    (D₀ : Act → ℝ) (hD₀ : (∀ a, 0 ≤ D₀ a) ∧ ∑ a, D₀ a = 1) :
    (chainMatrix (augLaw q L) (augProc D D₀)).IsIrreducible := by
  have hA0 := dm_chain_nonneg (augLaw q L) (dm_aug_law q L hq) _ (dm_aug_proc D hD D₀ hD₀)
  have h0 := dm_chain_nonneg q hq D hD
  obtain ⟨e1, e2, e3, e4⟩ := dm_aug_entries q L D hD D₀ hD₀
  set PA := chainMatrix (augLaw q L) (augProc D D₀)
  set P := chainMatrix q D
  have hn : (0 : ℝ) < Fintype.card S := by
    have : Nonempty S := ⟨L⟩
    exact_mod_cast Fintype.card_pos
  have hLn : 0 < (PA ^ 1) (some L) none := by rw [pow_one, e3]; simp
  have hnj : ∀ j, 0 < (PA ^ 1) none (some j) := by intro j; rw [pow_one, e2]; positivity
  have hsome : ∀ t i, 0 < (P ^ t) i L → ∃ s, 0 < (PA ^ s) (some i) none := by
    intro t
    induction t with
    | zero =>
      intro i hi
      rw [pow_zero, Matrix.one_apply] at hi
      split_ifs at hi with h
      · subst h; exact ⟨1, hLn⟩
      · exact absurd hi (lt_irrefl 0)
    | succ t ih =>
      intro i hi
      by_cases hiL : i = L
      · subst hiL; exact ⟨1, hLn⟩
      rw [pow_succ', Matrix.mul_apply] at hi
      obtain ⟨m, -, hm⟩ := (Finset.sum_pos_iff_of_nonneg (fun m _ => mul_nonneg
        (h0 i m) (Matrix.pow_apply_nonneg h0 t m L))).1 hi
      have h1 : 0 < P i m := by
        rcases (h0 i m).lt_or_eq with h | h
        · exact h
        · rw [← h, zero_mul] at hm; exact absurd hm (lt_irrefl 0)
      have h2 : 0 < (P ^ t) m L := by
        rcases (Matrix.pow_apply_nonneg h0 t m L).lt_or_eq with h | h
        · exact h
        · rw [← h, mul_zero] at hm; exact absurd hm (lt_irrefl 0)
      obtain ⟨s, hs⟩ := ih m h2
      refine ⟨1 + s, lt_of_lt_of_le ?_ (dm_pow_ge PA hA0 1 s (some i) (some m) none)⟩
      refine mul_pos ?_ hs
      rw [pow_one, e4]; simp [tabQ, hiL, h1]
  have hnone : ∀ x, ∃ s, 0 < (PA ^ s) x none := by
    intro x
    rcases x with _ | i
    · exact ⟨1 + 1, lt_of_lt_of_le (mul_pos (hnj L) hLn) (dm_pow_ge PA hA0 1 1 none (some L) none)⟩
    · obtain ⟨t, ht⟩ := hreach i
      exact hsome t i ht
  rw [Matrix.isIrreducible_iff_exists_pow_pos hA0]
  intro x y
  obtain ⟨s, hs⟩ := hnone x
  rcases y with _ | j
  · refine ⟨s + (1 + 1), by omega, lt_of_lt_of_le (mul_pos hs ?_) (dm_pow_ge PA hA0 s 2 x none none)⟩
    exact lt_of_lt_of_le (mul_pos (hnj L) hLn) (dm_pow_ge PA hA0 1 1 none (some L) none)
  · exact ⟨s + 1, by omega, lt_of_lt_of_le (mul_pos hs (hnj j)) (dm_pow_ge PA hA0 s 1 x none (some j))⟩

theorem dm_aug_taboo (q : S → Act → S → ℝ) (L : S) (D : S → Act → ℝ)
    (hD : IsStationaryRandomized D) (D₀ : Act → ℝ) (hD₀ : (∀ a, 0 ≤ D₀ a) ∧ ∑ a, D₀ a = 1) :
    ∀ t j, tabooProb (chainMatrix (augLaw q L) (augProc D D₀)) none (t + 1) (some j) =
      1 / (Fintype.card S : ℝ) * ∑ i, (tabQ (chainMatrix q D) L ^ t) i j := by
  obtain ⟨e1, e2, e3, e4⟩ := dm_aug_entries q L D hD D₀ hD₀
  intro t
  induction t with
  | zero => intro j; simp [tabooProb, e2, Matrix.one_apply]
  | succ t ih =>
    intro j
    show ∑ l, (if l = none then 0 else tabooProb _ none (t + 1) l) * _ = _
    rw [Fintype.sum_option]
    simp only [if_true, zero_mul, zero_add, reduceCtorEq, if_false, ih, e4]
    rw [pow_succ]
    simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem tcc_core (q : S → Act → S → ℝ) (w : S → Act → ℝ) (L : S) (hq : IsTransitionLaw q)
    (hL : ∀ a, q L a L = 1) (hwL : ∀ a, w L a = 0) (hw : ∀ i a, i ≠ L → 0 < w i a)
    (hB : ∀ D : S → Act → ℝ, IsStationaryRandomized D → ∀ i, ∃ t : ℕ, 0 < (chainMatrix q D ^ t) i L)
    (D : S → Act → ℝ) (hD : IsStationaryRandomized D)
    (D₀ : Act → ℝ) (hD₀ : (∀ a, 0 ≤ D₀ a) ∧ ∑ a, D₀ a = 1)
    (π : Option S → ℝ)
    (hπ : JewellMRP.InfiniteStep.IsStationary (chainMatrix (augLaw q L) (augProc D D₀)) π) :
    0 < π none ∧
    (∀ j, Summable (fun t : ℕ => tabooProb (chainMatrix (augLaw q L) (augProc D D₀)) none t j)) ∧
    (1 / (Fintype.card S : ℝ≥0∞)) * ∑ i, totalCost q w D i =
      ENNReal.ofReal (∑' t : ℕ, ∑ j, tabooProb (chainMatrix (augLaw q L) (augProc D D₀)) none t j *
        ∑ a, augProc D D₀ j a * augCost w j a) ∧
    ∑' t : ℕ, ∑ j, tabooProb (chainMatrix (augLaw q L) (augProc D D₀)) none t j *
        ∑ a, augProc D D₀ j a * augCost w j a =
      (1 / π none) * ∑ j, π j * ∑ a, augProc D D₀ j a * augCost w j a := by
  have htab := dm_aug_taboo q L D hD D₀ hD₀
  set PA := chainMatrix (augLaw q L) (augProc D D₀)
  have hirr := dm_aug_irred q L hq hL D hD (hB D hD) D₀ hD₀
  have hlaw := dm_aug_law q L hq
  have hproc := dm_aug_proc D hD D₀ hD₀
  have hA0 := dm_chain_nonneg (augLaw q L) hlaw _ hproc
  have hArow := dm_chain_row (augLaw q L) hlaw _ hproc
  have herg : JewellMRP.InfiniteStep.IsErgodic PA :=
    ⟨Matrix.mem_rowStochastic_iff_sum.2 ⟨hA0, hArow⟩, hirr⟩
  obtain ⟨hsum, hhas, heq⟩ := tab_core PA herg π hπ
    (fun j => ∑ a, augProc D D₀ j a * augCost w j a) none
  refine ⟨dm_stat_pos PA hirr π hπ none, hsum, ?_, ?_⟩
  · set n : ℝ := (Fintype.card S : ℝ)
    have hn : (0 : ℝ) < n := by
      have : Nonempty S := ⟨L⟩
      simp only [n]; exact_mod_cast Fintype.card_pos
    obtain ⟨hs, hVnn⟩ : (∀ i, HasSum (fun t => expCost q w D i t) (VD q w L D i)) ∧
        (∀ i, 0 ≤ VD q w L D i) := by
      obtain ⟨a, b, -⟩ := dm_total q w L hq hL hwL hw hB D hD; exact ⟨a, b⟩
    have hterm : ∀ t, ∑ j, tabooProb PA none (t + 1) j * ∑ a, augProc D D₀ j a * augCost w j a
        = 1 / n * ∑ i, expCost q w D i t := by
      intro t
      rw [Fintype.sum_option]
      have hg : ∀ x, ∑ a, augProc D D₀ (some x) a * augCost w (some x) a = gD w D x :=
        fun x => rfl
      have hz : ∑ a, augProc D D₀ none a * augCost w none a = 0 := by simp [augCost]
      rw [hz, mul_zero, zero_add]
      simp only [hg, htab, dm_exp_eq q w L hq hL hwL D hD]
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have hH : HasSum (fun t => ∑ j, tabooProb PA none t j * ∑ a, augProc D D₀ j a * augCost w j a)
        (1 / n * ∑ i, VD q w L D i) := by
      rw [← hasSum_nat_add_iff' 1]
      simp only [Finset.range_one, Finset.sum_singleton]
      have h0' : ∑ j, tabooProb PA none 0 j * ∑ a, augProc D D₀ j a * augCost w j a = 0 := by
        simp [tabooProb]
      rw [h0', sub_zero]
      simp_rw [hterm]
      exact (hasSum_sum fun i _ => hs i).mul_left _
    rw [hH.tsum_eq, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => hVnn i)]
    congr 1
    · rw [one_div, one_div, ENNReal.ofReal_inv_of_pos hn]
      simp [n]
    · refine Finset.sum_congr rfl fun i _ => ?_
      exact dm_totalCost_eq q w L hq hL hwL hw hB D hD i
  · rw [← heq]
    exact hhas.tsum_eq

end TCC

end DermanSeqDecisions.LinProg

open DermanSeqDecisions.LinProg


theorem solution {S Act : Type*} [Fintype S] [DecidableEq S] [Fintype Act]
    (q : S → Act → S → ℝ) (w : S → Act → ℝ) (L : S) (hq : IsTransitionLaw q)
    (hL : ∀ a, q L a L = 1) (hwL : ∀ a, w L a = 0) (hw : ∀ i a, i ≠ L → 0 < w i a)
    (hB : ∀ D : S → Act → ℝ, IsStationaryRandomized D → ∀ i, ∃ t : ℕ, 0 < (chainMatrix q D ^ t) i L)
    (D : S → Act → ℝ) (hD : IsStationaryRandomized D)
    (D₀ : Act → ℝ) (hD₀ : (∀ a, 0 ≤ D₀ a) ∧ ∑ a, D₀ a = 1)
    (π : Option S → ℝ)
    (hπ : JewellMRP.InfiniteStep.IsStationary (chainMatrix (augLaw q L) (augProc D D₀)) π) :
    0 < π none ∧
    (∀ j, Summable (fun t : ℕ => tabooProb (chainMatrix (augLaw q L) (augProc D D₀)) none t j)) ∧
    (1 / (Fintype.card S : ℝ≥0∞)) * ∑ i, totalCost q w D i =
      ENNReal.ofReal (∑' t : ℕ, ∑ j, tabooProb (chainMatrix (augLaw q L) (augProc D D₀)) none t j *
        ∑ a, augProc D D₀ j a * augCost w j a) ∧
    ∑' t : ℕ, ∑ j, tabooProb (chainMatrix (augLaw q L) (augProc D D₀)) none t j *
        ∑ a, augProc D D₀ j a * augCost w j a =
      (1 / π none) * ∑ j, π j * ∑ a, augProc D D₀ j a * augCost w j a := by
  exact tcc_core q w L hq hL hwL hw hB D hD D₀ hD₀ π hπ
