-- Prove2me | solution 1 for AvgRewardPMD.SPMD.bellman_solution_sets
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T11:49:41.420233+00:00
-- url     : https://prove2.me/submissions/370100ea-0c1d-49ed-9902-e3fbf875aaf5

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting
import Theorems.Thm_AvgRewardPMD_SPMD_avg_cost_eq_stationary

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


namespace MixAux

/-- geometric decay of the centred iterates, uniformly in the start state -/
lemma summable_of_geom (r B : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 4 * r ^ n * B) : Summable f := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0.le hr1).mul_left (4 * B))
    (fun n => ?_)
  rw [Real.norm_eq_abs]
  calc |f n| ≤ 4 * r ^ n * B := hf n
    _ = 4 * B * r ^ n := by ring

end MixAux

open MixAux in
theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (hmix : IsMixing P)
    (π : S → A → ℝ) (hπ : IsPolicy π) (c : S → A → ℝ) :
    {V : S → ℝ | ∀ s, V s = InducedReward π c s - avgCost P π c s
        + ∑ s', InducedTransition π P s s' * V s'}
      = {V : S → ℝ | ∃ b : ℝ, V = fun s => diffV P π c s + b} ∧
    {Q : S × A → ℝ | ∀ x, Q x = c x.1 x.2 - avgCost P π c x.1
        + ∑ y, saTransition P π x y * Q y}
      = {Q : S × A → ℝ | ∃ b : ℝ, Q = fun x => diffQ P π c x + b} := by
  classical
  obtain ⟨ν0, hν0, -⟩ := (Classical.choose_spec hmix) π hπ
  obtain ⟨r, hr0, hr1, hb⟩ := mixing_conv P hP hmix π hπ ν0 hν0
  set M := stateMatrix P π with hMdef
  have hMst : IsStoch M := stateMatrix_stoch P hP π hπ
  set rw' : S → ℝ := InducedReward π c with hrw
  set ρ := ∑ s', ν0 s' * rw' s' with hρdef
  have hρ : ∀ s, avgCost P π c s = ρ := fun s =>
    (avg_cost_eq_stationary P hP hmix π hπ ν0 hν0 c s).2
  have hIT : ∀ s s', InducedTransition π P s s' = M s s' := fun s s' => rfl
  have hlim0 : ∀ B : ℝ, Tendsto (fun n : ℕ => 4 * r ^ n * B) atTop (𝓝 0) := fun B => by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul 4).mul_const B
  -- harmonic functions are constant
  have harm : ∀ W : S → ℝ, (∀ s, W s = ∑ s', M s s' * W s') → ∀ s, W s = ∑ s', ν0 s' * W s' := by
    intro W hW s
    have hWn : ∀ n, (M ^ n).mulVec W = W := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
        funext s; exact (hW s).symm
    have hle : ∀ n : ℕ, |W s - ∑ s', ν0 s' * W s'| ≤ 4 * r ^ n * ∑ s', |W s'| := fun n => by
      have := hb W s n
      rw [hWn n] at this
      exact this
    have h0 := ge_of_tendsto' (hlim0 _) hle
    have := abs_nonpos_iff.1 h0
    linarith
  -- V part
  set f : S → ℕ → ℝ := fun s n => (M ^ n).mulVec rw' s - ρ with hf
  have hfb : ∀ s n, |f s n| ≤ 4 * r ^ n * ∑ s', |rw' s'| := fun s n => hb rw' s n
  have hfs : ∀ s, Summable (f s) := fun s => summable_of_geom r _ hr0 hr1 _ (hfb s)
  have hdiffV : ∀ s, diffV P π c s = ∑' n, f s n := by
    intro s; simp only [diffV, hρ, f]; rfl
  have hrow : ∀ s, ∑ s', M s s' = 1 := hMst.2
  have hfstep : ∀ s n, f s (n + 1) = ∑ s', M s s' * f s' n := by
    intro s n
    simp only [f]
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hrow,
      one_mul]
  have hVb : ∀ s, diffV P π c s = rw' s - ρ + ∑ s', M s s' * diffV P π c s' := by
    intro s
    rw [hdiffV, (hfs s).tsum_eq_zero_add]
    have h0 : f s 0 = rw' s - ρ := by simp [f]
    rw [h0]
    simp_rw [hfstep, hdiffV]
    rw [Summable.tsum_finsetSum (fun s' _ => (hfs s').mul_left (M s s'))]
    simp_rw [tsum_mul_left]
  -- Q part
  set PQ := saTransition P π with hPQ
  set c' : S × A → ℝ := fun y => c y.1 y.2 with hc'
  have hPQrow : ∀ x, ∑ y, PQ x y = 1 := by
    intro x
    simp only [PQ, saTransition, Matrix.of_apply]
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (hπ _).2, mul_one]
    exact (hP x.1 x.2).2
  have hPQpow : ∀ n x, ((PQ ^ (n + 1)).mulVec c') x = ∑ s', P x.1 x.2 s' * (M ^ n).mulVec rw' s' := by
    intro n
    induction n with
    | zero =>
      intro x
      simp only [zero_add, pow_one, pow_zero, Matrix.one_mulVec]
      simp only [Matrix.mulVec, dotProduct, PQ, saTransition, Matrix.of_apply, c', rw',
        InducedReward]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun s' _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    | succ n ih =>
      intro x
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      have e1 : (PQ.mulVec ((PQ ^ (n + 1)).mulVec c')) x
          = ∑ y, PQ x y * ∑ s', P y.1 y.2 s' * (M ^ n).mulVec rw' s' := by
        simp only [Matrix.mulVec, dotProduct] at ih ⊢
        exact Finset.sum_congr rfl fun y _ => by rw [ih y]
      rw [e1, pow_succ', ← Matrix.mulVec_mulVec]
      set v := (M ^ n).mulVec rw' with hv
      simp only [PQ, saTransition, Matrix.of_apply]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun s'' _ => ?_
      calc ∑ a, P x.1 x.2 s'' * π s'' a * ∑ s', P s'' a s' * v s'
          = P x.1 x.2 s'' * ∑ a, ∑ s', π s'' a * (P s'' a s' * v s') := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun s' _ => by ring
        _ = P x.1 x.2 s'' * ∑ s', ∑ a, π s'' a * (P s'' a s' * v s') := by rw [Finset.sum_comm]
        _ = P x.1 x.2 s'' * (M.mulVec v) s'' := by
            congr 1
            simp only [Matrix.mulVec, dotProduct, M, stateMatrix, Matrix.of_apply,
              InducedTransition, Finset.sum_mul]
            exact Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun a _ => by ring
  set g : S × A → ℕ → ℝ := fun x n => (PQ ^ n).mulVec c' x - ρ with hg
  have hProw : ∀ x : S × A, ∑ s', P x.1 x.2 s' = 1 := fun x => (hP x.1 x.2).2
  have hgsucc : ∀ x n, g x (n + 1) = ∑ s', P x.1 x.2 s' * f s' n := by
    intro x n
    simp only [g, f, hPQpow]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hProw, one_mul]
  have hgs : ∀ x, Summable (g x) := by
    intro x
    refine (summable_nat_add_iff 1).1 ?_
    refine summable_of_geom r (∑ s', |rw' s'|) hr0 hr1 _ (fun n => ?_)
    rw [hgsucc]
    calc |∑ s', P x.1 x.2 s' * f s' n| ≤ ∑ s', |P x.1 x.2 s' * f s' n| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s', P x.1 x.2 s' * (4 * r ^ n * ∑ s', |rw' s'|) := Finset.sum_le_sum fun s' _ => by
          rw [abs_mul, abs_of_nonneg ((hP x.1 x.2).1 s')]
          exact mul_le_mul_of_nonneg_left (hfb s' n) ((hP x.1 x.2).1 s')
      _ = 4 * r ^ n * ∑ s', |rw' s'| := by rw [← Finset.sum_mul, hProw, one_mul]
  have hdiffQ : ∀ x, diffQ P π c x = ∑' n, g x n := by
    intro x; simp only [diffQ, hρ, g]; rfl
  have hgstep : ∀ x n, g x (n + 1) = ∑ y, PQ x y * g y n := by
    intro x n
    simp only [g]
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hPQrow, one_mul]
  have hQb : ∀ x, diffQ P π c x = c' x - ρ + ∑ y, PQ x y * diffQ P π c y := by
    intro x
    rw [hdiffQ, (hgs x).tsum_eq_zero_add]
    have h0 : g x 0 = c' x - ρ := by simp [g]
    rw [h0]
    simp_rw [hgstep, hdiffQ]
    rw [Summable.tsum_finsetSum (fun y _ => (hgs y).mul_left (PQ x y))]
    simp_rw [tsum_mul_left]
  refine ⟨?_, ?_⟩
  · ext V
    simp only [Set.mem_ofPred_eq, hρ, hIT]
    constructor
    · intro hV
      set W : S → ℝ := fun s => V s - diffV P π c s with hW
      have hWh : ∀ s, W s = ∑ s', M s s' * W s' := by
        intro s
        simp only [W]
        rw [hV s, hVb s]
        simp only [mul_sub, Finset.sum_sub_distrib]
        ring
      refine ⟨∑ s', ν0 s' * W s', ?_⟩
      funext s
      have := harm W hWh s
      simp only [W] at this
      linarith
    · rintro ⟨b, rfl⟩ s
      show diffV P π c s + b = rw' s - ρ + ∑ s', M s s' * (diffV P π c s' + b)
      rw [hVb s]
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hrow, one_mul]
      ring
  · ext Q
    simp only [Set.mem_ofPred_eq, hρ]
    constructor
    · intro hQ
      set W : S × A → ℝ := fun x => Q x - diffQ P π c x with hW
      have hWh : ∀ x, W x = ∑ y, PQ x y * W y := by
        intro x
        simp only [W]
        rw [hQ x, hQb x]
        simp only [mul_sub, Finset.sum_sub_distrib, c']
        ring
      set w : S → ℝ := fun s => ∑ a, π s a * W (s, a) with hw
      have hWw : ∀ x : S × A, W x = ∑ s', P x.1 x.2 s' * w s' := by
        intro x
        rw [hWh x]
        simp only [PQ, saTransition, Matrix.of_apply, w]
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun s' _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
      have hwh : ∀ s, w s = ∑ s', M s s' * w s' := by
        intro s
        calc w s = ∑ a, π s a * ∑ s', P s a s' * w s' :=
              Finset.sum_congr rfl fun a _ => congrArg _ (hWw (s, a))
          _ = ∑ a, ∑ s', π s a * (P s a s' * w s') := by simp_rw [Finset.mul_sum]
          _ = ∑ s', ∑ a, π s a * (P s a s' * w s') := Finset.sum_comm
          _ = ∑ s', M s s' * w s' := by
              refine Finset.sum_congr rfl fun s' _ => ?_
              simp only [M, stateMatrix, Matrix.of_apply, InducedTransition, Finset.sum_mul]
              exact Finset.sum_congr rfl fun a _ => by ring
      refine ⟨∑ s', ν0 s' * w s', ?_⟩
      funext x
      set bb := ∑ s', ν0 s' * w s' with hbb
      have hc : ∀ s, w s = bb := harm w hwh
      have : W x = bb := by
        rw [hWw x]
        simp_rw [hc]
        rw [← Finset.sum_mul, hProw, one_mul]
      simp only [W] at this
      linarith
    · rintro ⟨b, rfl⟩ x
      show diffQ P π c x + b = c x.1 x.2 - ρ + ∑ y, PQ x y * (diffQ P π c y + b)
      rw [hQb x]
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hPQrow, one_mul, c']
      ring
