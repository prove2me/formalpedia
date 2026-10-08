-- Prove2me | solution 1 for DermanSeqDecisions.LinProg.avg_cost_eq_stationary
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T23:00:47.072587+00:00
-- url     : https://prove2.me/submissions/0f7296e6-d234-43bf-b98c-30ca6495d526

import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model
import Definitions.Def_DermanSeqDecisions_LinProg_Model

open Matrix


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

end DermanSeqDecisions.LinProg

open DermanSeqDecisions.LinProg


theorem solution {S Act : Type*} [Fintype S] [DecidableEq S] [Fintype Act]
    (q : S → Act → S → ℝ) (w : S → Act → ℝ) (hq : IsTransitionLaw q)
    (hw : ∀ i a, 0 < w i a)
    (hA : ∀ D : S → Act → ℝ, IsStationaryRandomized D → (chainMatrix q D).IsIrreducible)
    (D : S → Act → ℝ) (hD : IsStationaryRandomized D)
    (π : S → ℝ) (hπ : JewellMRP.InfiniteStep.IsStationary (chainMatrix q D) π) :
    ∀ i, avgCost q w D i = ∑ j, π j * ∑ a, D j a * w j a := by
  exact acs_core q w hq hA D hD π hπ
