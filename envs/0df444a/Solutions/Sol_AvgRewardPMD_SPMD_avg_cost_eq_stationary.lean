-- Prove2me | solution 1 for AvgRewardPMD.SPMD.avg_cost_eq_stationary
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T11:46:07.017593+00:00
-- url     : https://prove2.me/submissions/d8e6b81b-9f79-4e11-86f8-eaf9018f34ad

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting

open FoundationsML.ReinforcementLearning AvgRewardPMD.SPMD Filter Topology

set_option linter.unusedSectionVars false

namespace MixAux
open Finset

variable {S : Type*} [Fintype S] [DecidableEq S]

def IsStoch (M : Matrix S S ℝ) : Prop := (∀ s s', 0 ≤ M s s') ∧ ∀ s, ∑ s', M s s' = 1

lemma IsStoch.mul' {M N : Matrix S S ℝ} (hM : IsStoch M) (hN : IsStoch N) : IsStoch (M * N) := by
  refine ⟨fun s s' => ?_, fun s => ?_⟩
  · simp only [Matrix.mul_apply]; exact sum_nonneg fun x _ => mul_nonneg (hM.1 _ _) (hN.1 _ _)
  · simp only [Matrix.mul_apply]; rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum, hN.2, mul_one]
    exact hM.2 s

lemma IsStoch.one' : IsStoch (1 : Matrix S S ℝ) :=
  ⟨fun s s' => by rw [Matrix.one_apply]; split_ifs <;> norm_num, fun s => by simp [Matrix.one_apply]⟩

lemma IsStoch.pow' {M : Matrix S S ℝ} (hM : IsStoch M) : ∀ n, IsStoch (M ^ n)
  | 0 => by rw [pow_zero]; exact IsStoch.one'
  | n+1 => by rw [pow_succ]; exact (hM.pow' n).mul' hM

lemma vecMul_mem {M : Matrix S S ℝ} (hM : IsStoch M) {q : S → ℝ} (hq : q ∈ stdSimplex ℝ S) :
    Matrix.vecMul q M ∈ stdSimplex ℝ S := by
  refine ⟨fun s' => ?_, ?_⟩
  · simp only [Matrix.vecMul, dotProduct]
    exact sum_nonneg fun s _ => mul_nonneg (hq.1 s) (hM.1 s s')
  · simp only [Matrix.vecMul, dotProduct]; rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hM.2, mul_one]; exact hq.2

lemma half_contract {N : Matrix S S ℝ} (ν0 : S → ℝ)
    (hmix : ∀ q ∈ stdSimplex ℝ S, ∑ s', |∑ s, q s * N s s' - ν0 s'| ≤ 1/2)
    (d : S → ℝ) (hd : ∑ s, d s = 0) :
    ∑ s', |Matrix.vecMul d N s'| ≤ (∑ s, |d s|) / 2 := by
  set dp : S → ℝ := fun s => max (d s) 0 with hdp
  set dm : S → ℝ := fun s => max (-d s) 0 with hdm
  have e1 : ∀ s, dp s - dm s = d s ∧ dp s + dm s = |d s| := by
    intro s
    rcases le_total 0 (d s) with h | h
    · have h' : -d s ≤ 0 := by linarith
      simp only [dp, dm, max_eq_left h, max_eq_right h', abs_of_nonneg h]
      constructor <;> ring
    · have h' : 0 ≤ -d s := by linarith
      simp only [dp, dm, max_eq_right h, max_eq_left h', abs_of_nonpos h]
      constructor <;> ring
  have hdp0 : ∀ s, 0 ≤ dp s := fun s => le_max_right _ _
  have hdm0 : ∀ s, 0 ≤ dm s := fun s => le_max_right _ _
  set a := ∑ s, dp s with ha
  have hsm : ∑ s, dm s = a := by
    have : ∑ s, (dp s - dm s) = 0 := by simp_rw [fun s => (e1 s).1]; exact hd
    rw [sum_sub_distrib] at this; linarith
  have hl1 : ∑ s, |d s| = 2 * a := by
    simp_rw [← fun s => (e1 s).2]; rw [sum_add_distrib, hsm]; ring
  rcases (sum_nonneg fun s (_ : s ∈ univ) => hdp0 s).eq_or_lt with h0 | hpos
  · -- a = 0, so d = 0
    have hdp_z : ∀ s, dp s = 0 := fun s =>
      (sum_eq_zero_iff_of_nonneg fun s _ => hdp0 s).1 h0.symm s (mem_univ s)
    have hdm_z : ∀ s, dm s = 0 := fun s =>
      (sum_eq_zero_iff_of_nonneg fun s _ => hdm0 s).1 (by rw [hsm]; exact h0.symm) s (mem_univ s)
    have hdz : ∀ s, d s = 0 := fun s => by rw [← (e1 s).1, hdp_z, hdm_z, sub_zero]
    have : ∀ s', Matrix.vecMul d N s' = 0 := fun s' => by
      simp [Matrix.vecMul, dotProduct, hdz]
    simp [this, hdz]
  · have hq1 : (fun s => dp s / a) ∈ stdSimplex ℝ S :=
      ⟨fun s => div_nonneg (hdp0 s) hpos.le, by rw [← sum_div]; exact div_self hpos.ne'⟩
    have hq2 : (fun s => dm s / a) ∈ stdSimplex ℝ S :=
      ⟨fun s => div_nonneg (hdm0 s) hpos.le, by rw [← sum_div, hsm]; exact div_self hpos.ne'⟩
    have m1 := hmix _ hq1
    have m2 := hmix _ hq2
    have key : ∀ s', Matrix.vecMul d N s'
        = a * ((∑ s, dp s / a * N s s' - ν0 s') - (∑ s, dm s / a * N s s' - ν0 s')) := by
      intro s'
      have : ∑ s, dp s / a * N s s' - ∑ s, dm s / a * N s s'
          = (∑ s, d s * N s s') / a := by
        rw [← sum_sub_distrib, sum_div]
        refine sum_congr rfl fun s _ => ?_
        rw [← (e1 s).1]; field_simp
      have e2 : Matrix.vecMul d N s' = ∑ s, d s * N s s' := rfl
      rw [e2]
      have : (∑ s, dp s / a * N s s' - ν0 s') - (∑ s, dm s / a * N s s' - ν0 s')
          = (∑ s, d s * N s s') / a := by linarith
      rw [this, mul_div_cancel₀ _ (show a ≠ 0 from hpos.ne')]
    calc ∑ s', |Matrix.vecMul d N s'|
        ≤ ∑ s', a * (|∑ s, dp s / a * N s s' - ν0 s'| + |∑ s, dm s / a * N s s' - ν0 s'|) := by
          refine sum_le_sum fun s' _ => ?_
          rw [key s', abs_mul, abs_of_pos hpos]
          exact mul_le_mul_of_nonneg_left (abs_sub _ _) hpos.le
      _ = a * (∑ s', |∑ s, dp s / a * N s s' - ν0 s'| + ∑ s', |∑ s, dm s / a * N s s' - ν0 s'|) := by
          rw [← sum_add_distrib, mul_sum]
      _ ≤ a * (1/2 + 1/2) := mul_le_mul_of_nonneg_left (add_le_add m1 m2) hpos.le
      _ = (∑ s, |d s|) / 2 := by rw [hl1]; ring

lemma geom {M : Matrix S S ℝ} (hM : IsStoch M) (ν0 : S → ℝ) (hν0 : ν0 ∈ stdSimplex ℝ S)
    (hstat : Matrix.vecMul ν0 M = ν0) (t : ℕ) (ht : 1 ≤ t)
    (hmix : ∀ q ∈ stdSimplex ℝ S, ∑ s', |∑ s, q s * (M ^ t) s s' - ν0 s'| ≤ 1/2) :
    ∀ q ∈ stdSimplex ℝ S, ∀ n, ∑ s', |Matrix.vecMul q (M ^ n) s' - ν0 s'|
      ≤ 4 * ((1/2:ℝ) ^ ((t:ℝ)⁻¹)) ^ n := by
  set r := (1/2:ℝ) ^ ((t:ℝ)⁻¹) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) (by positivity)
  have hrt : r ^ t = 1/2 := Real.rpow_inv_natCast_pow (by norm_num) (by omega)
  have hstatn : ∀ n, Matrix.vecMul ν0 (M ^ n) = ν0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hstat]
  intro q hq n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < t
    · have hqn := vecMul_mem (hM.pow' n) hq
      have h2 : ∑ s', |Matrix.vecMul q (M ^ n) s' - ν0 s'| ≤ 2 := by
        calc ∑ s', |Matrix.vecMul q (M ^ n) s' - ν0 s'|
            ≤ ∑ s', (Matrix.vecMul q (M ^ n) s' + ν0 s') := sum_le_sum fun s' _ => by
              rw [abs_le]; constructor <;> linarith [hqn.1 s', hν0.1 s']
          _ = 2 := by rw [sum_add_distrib, hqn.2, hν0.2]; norm_num
      have : (1/2:ℝ) ≤ r ^ n := by rw [← hrt]; exact pow_le_pow_of_le_one hr0.le hr1 hn.le
      linarith
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + t := ⟨n - t, by omega⟩
      have hm := ih m (by omega)
      have he : ∀ s', Matrix.vecMul q (M ^ (m + t)) s' - ν0 s'
          = Matrix.vecMul (fun s => Matrix.vecMul q (M ^ m) s - ν0 s) (M ^ t) s' := by
        intro s'
        rw [pow_add, ← Matrix.vecMul_vecMul]
        conv_lhs => rw [show ν0 s' = Matrix.vecMul ν0 (M ^ t) s' by rw [hstatn]]
        simp only [Matrix.vecMul, dotProduct, sub_mul, sum_sub_distrib]
      simp_rw [he]
      have hsum0 : ∑ s, (Matrix.vecMul q (M ^ m) s - ν0 s) = 0 := by
        rw [sum_sub_distrib, (vecMul_mem (hM.pow' m) hq).2, hν0.2, sub_self]
      have := half_contract (N := M ^ t) ν0 hmix _ hsum0
      calc _ ≤ _ := this
        _ ≤ 4 * r ^ m / 2 := by linarith
        _ = 4 * r ^ (m + t) := by rw [pow_add, hrt]; ring

lemma row_bound {M : Matrix S S ℝ} (hM : IsStoch M) (ν0 : S → ℝ) (hν0 : ν0 ∈ stdSimplex ℝ S)
    (hstat : Matrix.vecMul ν0 M = ν0) (t : ℕ) (ht : 1 ≤ t)
    (hmix : ∀ q ∈ stdSimplex ℝ S, ∑ s', |∑ s, q s * (M ^ t) s s' - ν0 s'| ≤ 1/2)
    (v : S → ℝ) (s : S) (n : ℕ) :
    |(M ^ n).mulVec v s - ∑ s', ν0 s' * v s'|
      ≤ 4 * ((1/2:ℝ) ^ ((t:ℝ)⁻¹)) ^ n * ∑ s', |v s'| := by
  set r := (1/2:ℝ) ^ ((t:ℝ)⁻¹) with hr
  have hq : (Pi.single s 1 : S → ℝ) ∈ stdSimplex ℝ S := by
    refine ⟨fun x => ?_, ?_⟩
    · by_cases hx : x = s
      · subst hx; simp
      · simp [Pi.single_apply, hx]
    · simp
  have hg := geom hM ν0 hν0 hstat t ht hmix _ hq n
  have hrow : ∀ s', Matrix.vecMul (Pi.single s 1) (M ^ n) s' = (M ^ n) s s' := by
    intro s'; rw [Matrix.single_vecMul]; simp
  simp_rw [hrow] at hg
  set V := ∑ s', |v s'| with hV
  have hvV : ∀ s', |v s'| ≤ V := fun s' =>
    single_le_sum (f := fun x => |v x|) (fun x _ => abs_nonneg _) (mem_univ s')
  have e : (M ^ n).mulVec v s - ∑ s', ν0 s' * v s' = ∑ s', ((M ^ n) s s' - ν0 s') * v s' := by
    simp only [Matrix.mulVec, dotProduct, sub_mul, sum_sub_distrib]
  rw [e]
  calc |∑ s', ((M ^ n) s s' - ν0 s') * v s'|
      ≤ ∑ s', |((M ^ n) s s' - ν0 s') * v s'| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', |(M ^ n) s s' - ν0 s'| * V := sum_le_sum fun s' _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hvV s') (abs_nonneg _)
    _ = (∑ s', |(M ^ n) s s' - ν0 s'|) * V := by rw [sum_mul]
    _ ≤ 4 * r ^ n * V := mul_le_mul_of_nonneg_right hg
        (sum_nonneg fun x _ => abs_nonneg _)

lemma r_lt_one (t : ℕ) (ht : 1 ≤ t) : (1/2:ℝ) ^ ((t:ℝ)⁻¹) < 1 :=
  Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)

lemma r_pos (t : ℕ) : 0 < (1/2:ℝ) ^ ((t:ℝ)⁻¹) := Real.rpow_pos_of_pos (by norm_num) _

end MixAux

namespace MixAux

lemma stateMatrix_stoch {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (π : S → A → ℝ) (hπ : IsPolicy π) :
    IsStoch (stateMatrix P π) := by
  refine ⟨fun s s' => ?_, fun s => ?_⟩
  · simp only [stateMatrix, Matrix.of_apply, InducedTransition]
    exact Finset.sum_nonneg fun a _ => mul_nonneg ((hπ s).1 a) ((hP s a).1 s')
  · simp only [stateMatrix, Matrix.of_apply, InducedTransition]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (hP s _).2, mul_one]
    exact (hπ s).2

/-- Under the mixing assumption, `P_π^n v → ⟨ν, v⟩` geometrically for every stationary `ν`. -/
lemma mixing_conv {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (hmix : IsMixing P)
    (π : S → A → ℝ) (hπ : IsPolicy π) (ν : S → ℝ)
    (hν : MarkovMixing.IsStationary (stateMatrix P π) ν) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ (v : S → ℝ) (s : S) (n : ℕ),
      |((stateMatrix P π) ^ n).mulVec v s - ∑ s', ν s' * v s'| ≤ 4 * r ^ n * ∑ s', |v s'| := by
  obtain ⟨ν0, hν0, t, ht1, -, hmt⟩ := (Classical.choose_spec hmix) π hπ
  set M := stateMatrix P π with hMdef
  have hM : IsStoch M := stateMatrix_stoch P hP π hπ
  have hν0S : ν0 ∈ stdSimplex ℝ S := ⟨hν0.1.1, hν0.1.2⟩
  have hνS : ν ∈ stdSimplex ℝ S := ⟨hν.1.1, hν.1.2⟩
  have hr1 := r_lt_one t ht1
  have hr0 := r_pos t
  set r := (1/2:ℝ) ^ ((t:ℝ)⁻¹) with hr
  have hνeq : ν = ν0 := by
    have hstatn : ∀ n, Matrix.vecMul ν (M ^ n) = ν := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hν.2]
    have hg := geom hM ν0 hν0S hν0.2 t ht1 hmt ν hνS
    funext s
    have hlim : Tendsto (fun n : ℕ => 4 * r ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul 4
    have hle : ∀ n : ℕ, |ν s - ν0 s| ≤ 4 * r ^ n := fun n => by
      have := hg n
      rw [hstatn n] at this
      exact (Finset.single_le_sum (f := fun x => |ν x - ν0 x|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ s)).trans this
    have h0 : |ν s - ν0 s| ≤ 0 := ge_of_tendsto' hlim hle
    have := abs_nonpos_iff.1 h0
    linarith
  rw [hνeq]
  exact ⟨r, hr0, hr1, fun v s n => row_bound hM ν0 hν0S hν0.2 t ht1 hmt v s n⟩

end MixAux

open MixAux in
theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (hmix : IsMixing P)
    (π : S → A → ℝ) (hπ : IsPolicy π) (ν : S → ℝ)
    (hν : MarkovMixing.IsStationary (stateMatrix P π) ν) (c : S → A → ℝ) :
    ∀ s, Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
          ∑ t ∈ Finset.range T, (((stateMatrix P π) ^ t).mulVec (InducedReward π c)) s)
        atTop (𝓝 (∑ s', ν s' * InducedReward π c s')) ∧
      avgCost P π c s = ∑ s', ν s' * InducedReward π c s' := by
  obtain ⟨r, hr0, hr1, hb⟩ := mixing_conv P hP hmix π hπ ν hν
  intro s
  have hlim : Tendsto (fun n : ℕ => 4 * r ^ n * ∑ s', |InducedReward π c s'|) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul 4).mul_const
      (∑ s', |InducedReward π c s'|)
  have hconv : Tendsto (fun n : ℕ => ((stateMatrix P π) ^ n).mulVec (InducedReward π c) s)
      atTop (𝓝 (∑ s', ν s' * InducedReward π c s')) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    rw [Real.norm_eq_abs]
    exact hb _ s n
  have hT := hconv.cesaro
  exact ⟨hT, hT.limUnder_eq⟩
