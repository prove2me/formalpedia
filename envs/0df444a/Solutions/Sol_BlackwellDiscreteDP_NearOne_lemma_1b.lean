-- Prove2me | solution 1 for BlackwellDiscreteDP.NearOne.lemma_1b
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T21:47:52.058356+00:00
-- url     : https://prove2.me/submissions/bfdb62b5-b02a-4f32-b4eb-1a63653d5a15

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
open Filter Topology Matrix


namespace BlackwellDiscreteDP.NearOne

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section MarkovTheory
variable {n : Type*} [Fintype n] [DecidableEq n]

instance bmk_fc : FirstCountableTopology (Matrix n n ℝ) :=
  inferInstanceAs (FirstCountableTopology (n → n → ℝ))

lemma bmk_mul {A B : Matrix n n ℝ} (hA : IsMarkovMatrix A) (hB : IsMarkovMatrix B) :
    IsMarkovMatrix (A * B) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hA.1 i k) (hB.1 k j)
  · simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hB.2, mul_one]
    exact hA.2 i

lemma bmk_one : IsMarkovMatrix (1 : Matrix n n ℝ) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · rw [Matrix.one_apply]; split_ifs <;> norm_num
  · simp [Matrix.one_apply]

lemma bmk_pow {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (k : ℕ) : IsMarkovMatrix (P ^ k) := by
  induction k with
  | zero => simpa using (bmk_one (n := n))
  | succ k ih => rw [pow_succ]; exact bmk_mul ih hP

lemma bmk_le_one {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (i j : n) : P i j ≤ 1 := by
  rw [← hP.2 i]
  exact Finset.single_le_sum (f := fun j => P i j) (fun j _ => hP.1 i j) (Finset.mem_univ j)

lemma bmk_cesaro {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (N : ℕ) :
    IsMarkovMatrix (cesaroMean P N) := by
  unfold cesaroMean
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => (bmk_pow hP k).1 i j)
  · simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [(bmk_pow hP _).2 i]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    field_simp

lemma bmk_P_mul_sum (P : Matrix n n ℝ) (N : ℕ) :
    P * ∑ k ∈ Finset.range (N + 1), P ^ k = ∑ k ∈ Finset.range (N + 1), P ^ k + (P ^ (N + 1) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, ← pow_succ']
    abel

lemma bmk_sum_mul_P (P : Matrix n n ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), P ^ k) * P = ∑ k ∈ Finset.range (N + 1), P ^ k + (P ^ (N + 1) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, add_mul, ih, ← pow_succ]
    abel

lemma bmk_P_cesaro (P : Matrix n n ℝ) (N : ℕ) :
    P * cesaroMean P N - cesaroMean P N = ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1) := by
  unfold cesaroMean
  rw [Matrix.mul_smul, bmk_P_mul_sum, smul_add]
  abel

lemma bmk_cesaro_P (P : Matrix n n ℝ) (N : ℕ) :
    cesaroMean P N * P - cesaroMean P N = ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1) := by
  unfold cesaroMean
  rw [Matrix.smul_mul, bmk_sum_mul_P, smul_add]
  abel

lemma bmk_D_tendsto {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hb : ∀ N : ℕ, ‖(((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) i j‖ ≤ 1 / ((N : ℝ) + 1) := by
    intro N
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Real.norm_eq_abs]
    have h1 := (bmk_pow hP (N + 1)).1 i j
    have h2 := bmk_le_one (bmk_pow hP (N + 1)) i j
    have h3 : (0 : ℝ) ≤ (1 : Matrix n n ℝ) i j := bmk_one.1 i j
    have h4 : (1 : Matrix n n ℝ) i j ≤ 1 := bmk_le_one bmk_one i j
    rw [abs_mul, abs_of_pos (by positivity), one_div]
    have : |(P ^ (N + 1)) i j - (1 : Matrix n n ℝ) i j| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    calc ((N : ℝ) + 1)⁻¹ * |(P ^ (N + 1)) i j - (1 : Matrix n n ℝ) i j| ≤ ((N : ℝ) + 1)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_one _
  exact squeeze_zero_norm hb tendsto_one_div_add_atTop_nhds_zero_nat

lemma bmk_clus {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {L : Matrix n n ℝ}
    (hL : Tendsto (fun j => cesaroMean P (ns j)) atTop (𝓝 L)) : P * L = L ∧ L * P = L := by
  have hD := (bmk_D_tendsto hP).comp hns
  constructor
  · have h1 : Tendsto (fun j => P * cesaroMean P (ns j) - cesaroMean P (ns j)) atTop
        (𝓝 (P * L - L)) := (hL.const_mul P).sub hL
    have h2 : (fun j => P * cesaroMean P (ns j) - cesaroMean P (ns j)) =
        (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) ∘ ns := by
      funext j; exact bmk_P_cesaro P (ns j)
    rw [h2] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 hD)
  · have h1 : Tendsto (fun j => cesaroMean P (ns j) * P - cesaroMean P (ns j)) atTop
        (𝓝 (L * P - L)) := (hL.mul_const P).sub hL
    have h2 : (fun j => cesaroMean P (ns j) * P - cesaroMean P (ns j)) =
        (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) ∘ ns := by
      funext j; exact bmk_cesaro_P P (ns j)
    rw [h2] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 hD)

lemma bmk_avg_const (L : Matrix n n ℝ) (N : ℕ) :
    ((N : ℝ) + 1)⁻¹ • ∑ k ∈ Finset.range (N + 1), L = L := by
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (by positivity), one_smul]

lemma bmk_cesaro_mul_fix {P L : Matrix n n ℝ} (h : P * L = L) (N : ℕ) :
    cesaroMean P N * L = L := by
  have hk : ∀ k : ℕ, P ^ k * L = L := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Matrix.mul_assoc, ih, h]
  unfold cesaroMean
  rw [Matrix.smul_mul, Finset.sum_mul]
  simp_rw [hk]
  exact bmk_avg_const L N

lemma bmk_fix_mul_cesaro {P L : Matrix n n ℝ} (h : L * P = L) (N : ℕ) :
    L * cesaroMean P N = L := by
  have hk : ∀ k : ℕ, L * P ^ k = L := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mul_assoc, ih, h]
  unfold cesaroMean
  rw [Matrix.mul_smul, Finset.mul_sum]
  simp_rw [hk]
  exact bmk_avg_const L N

lemma bmk_compact : IsCompact {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} := by
  have e : {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} =
      Set.pi Set.univ (fun (_ : n) => Set.pi Set.univ (fun (_ : n) => Set.Icc (0 : ℝ) 1)) := by
    ext M; exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [e]
  exact isCompact_univ_pi (fun (_ : n) => isCompact_univ_pi (fun (_ : n) => isCompact_Icc))

theorem bmk_tendsto {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    Tendsto (cesaroMean P) atTop (𝓝 (limitMatrix P)) := by
  have hmem : ∀ N, cesaroMean P N ∈ {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} :=
    fun N i j => ⟨(bmk_cesaro hP N).1 i j, bmk_le_one (bmk_cesaro hP N) i j⟩
  obtain ⟨L, -, φ, hφ, hL⟩ := bmk_compact.tendsto_subseq hmem
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  obtain ⟨hPL, hLP⟩ := bmk_clus hP hφt hL
  have main : Tendsto (cesaroMean P) atTop (𝓝 L) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨L', -, ψ, hψ, hL'⟩ := bmk_compact.tendsto_subseq (fun j => hmem (ns j))
    refine ⟨ψ, ?_⟩
    have hnsψ : Tendsto (ns ∘ ψ) atTop atTop := hns.comp hψ.tendsto_atTop
    obtain ⟨hPL', hL'P⟩ := bmk_clus hP hnsψ hL'
    have e1 : L * L' = L' := by
      have t : Tendsto (fun j => cesaroMean P (φ j) * L') atTop (𝓝 (L * L')) := hL.mul_const L'
      simp_rw [bmk_cesaro_mul_fix hPL'] at t
      exact (tendsto_nhds_unique tendsto_const_nhds t).symm
    have e2 : L * L' = L := by
      have t : Tendsto (fun j => L * cesaroMean P ((ns ∘ ψ) j)) atTop (𝓝 (L * L')) :=
        hL'.const_mul L
      simp_rw [bmk_fix_mul_cesaro hLP] at t
      exact (tendsto_nhds_unique tendsto_const_nhds t).symm
    have : L' = L := e1.symm.trans e2
    rw [this] at hL'
    exact hL'
  rw [limitMatrix, main.limUnder_eq]
  exact main

variable {P : Matrix n n ℝ}

lemma bmk_PL (hP : IsMarkovMatrix P) : P * limitMatrix P = limitMatrix P :=
  (bmk_clus hP tendsto_id (bmk_tendsto hP)).1

lemma bmk_LP (hP : IsMarkovMatrix P) : limitMatrix P * P = limitMatrix P :=
  (bmk_clus hP tendsto_id (bmk_tendsto hP)).2

lemma bmk_LL (hP : IsMarkovMatrix P) : limitMatrix P * limitMatrix P = limitMatrix P := by
  have t : Tendsto (fun N => cesaroMean P N * limitMatrix P) atTop
      (𝓝 (limitMatrix P * limitMatrix P)) := (bmk_tendsto hP).mul_const _
  simp_rw [bmk_cesaro_mul_fix (bmk_PL hP)] at t
  exact (tendsto_nhds_unique tendsto_const_nhds t).symm

lemma bmk_fixvec (hP : IsMarkovMatrix P) {v : n → ℝ} (hv : P *ᵥ v = v) :
    limitMatrix P *ᵥ v = v := by
  have hk : ∀ k : ℕ, (P ^ k) *ᵥ v = v := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]
  have hA : ∀ N, cesaroMean P N *ᵥ v = v := by
    intro N
    rw [cesaroMean, Matrix.smul_mulVec, Matrix.sum_mulVec]
    simp_rw [hk]
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ (by positivity), one_smul]
  have t : Tendsto (fun N => cesaroMean P N *ᵥ v) atTop (𝓝 (limitMatrix P *ᵥ v)) :=
    ((continuous_id.matrix_mulVec continuous_const).tendsto _).comp (bmk_tendsto hP)
  simp_rw [hA] at t
  exact (tendsto_nhds_unique tendsto_const_nhds t).symm

lemma bmk_L_markov (hP : IsMarkovMatrix P) : IsMarkovMatrix (limitMatrix P) := by
  have hc : IsClosed {M : Matrix n n ℝ | IsMarkovMatrix M} := by
    have : {M : Matrix n n ℝ | IsMarkovMatrix M} =
        (⋂ i, ⋂ j, {M : Matrix n n ℝ | 0 ≤ M i j}) ∩ ⋂ i, {M : Matrix n n ℝ | ∑ j, M i j = 1} := by
      ext M; simp [IsMarkovMatrix]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
      (isClosed_iInter fun i => ?_)
    · exact isClosed_le continuous_const ((continuous_apply j).comp (continuous_apply i))
    · exact isClosed_eq (continuous_finsetSum _ fun j _ =>
        (continuous_apply j).comp (continuous_apply i)) continuous_const
  exact hc.mem_of_tendsto (bmk_tendsto hP) (Eventually.of_forall fun N => bmk_cesaro hP N)

lemma bmk_ZL_inj (hP : IsMarkovMatrix P) :
    Function.Injective (1 - P + limitMatrix P).mulVec := by
  set L := limitMatrix P
  have hLA : L * (1 - P + L) = L := by
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP]; abel
  intro v w hvw
  set d := v - w
  have hd : (1 - P + L) *ᵥ d = 0 := by
    simp only [d, Matrix.mulVec_sub, hvw, sub_self]
  have hLd : L *ᵥ d = 0 := by
    have := congrArg (fun z => L *ᵥ z) hd
    simp only [Matrix.mulVec_mulVec, hLA, Matrix.mulVec_zero] at this
    exact this
  have hPd : P *ᵥ d = d := by
    have := hd
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, hLd, Matrix.one_mulVec, add_zero, sub_eq_zero] at this
    exact this.symm
  have : d = 0 := by rw [← bmk_fixvec hP hPd, hLd]
  exact sub_eq_zero.1 this

lemma bmk_Z_unit (hP : IsMarkovMatrix P) : IsUnit (1 - P + limitMatrix P).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_injective_iff_isUnit.1 (bmk_ZL_inj hP))

lemma bmk_PH (hP : IsMarkovMatrix P) :
    P * deviationMatrix P = deviationMatrix P + limitMatrix P - 1 := by
  set L := limitMatrix P
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + L) * (1 - P + L)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hLZ : L * (1 - P + L)⁻¹ = L := by
    have hLA : L * (1 - P + L) = L := by
      rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP]; abel
    calc L * (1 - P + L)⁻¹ = (L * (1 - P + L)) * (1 - P + L)⁻¹ := by rw [hLA]
      _ = L * ((1 - P + L) * (1 - P + L)⁻¹) := Matrix.mul_assoc _ _ _
      _ = L := by rw [h1, Matrix.mul_one]
  have h2 : (1 - P + L) * (1 - P + L)⁻¹ = (1 - P + L)⁻¹ - P * (1 - P + L)⁻¹ + L * (1 - P + L)⁻¹ := by
    rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul]
  rw [h1, hLZ] at h2
  unfold deviationMatrix
  rw [Matrix.mul_sub, bmk_PL hP]
  change P * (1 - P + L)⁻¹ - L = (1 - P + L)⁻¹ - L + L - 1
  generalize (1 - P + L)⁻¹ = Z at h2 ⊢
  have : P * Z = Z + L - 1 := by rw [h2]; abel
  rw [this]; abel

lemma bmk_LH (hP : IsMarkovMatrix P) : limitMatrix P * deviationMatrix P = 0 := by
  set L := limitMatrix P
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + L) * (1 - P + L)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hLA : L * (1 - P + L) = L := by
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP]; abel
  have hLZ : L * (1 - P + L)⁻¹ = L := by
    calc L * (1 - P + L)⁻¹ = (L * (1 - P + L)) * (1 - P + L)⁻¹ := by rw [hLA]
      _ = L * ((1 - P + L) * (1 - P + L)⁻¹) := Matrix.mul_assoc _ _ _
      _ = L := by rw [h1, Matrix.mul_one]
  unfold deviationMatrix
  rw [Matrix.mul_sub, hLZ, bmk_LL hP, sub_self]

/-- maximum principle: if `w = c + β P w` and `c ≤ K` then `w ≤ K/(1-β)` -/
lemma bmk_upper (hP : IsMarkovMatrix P) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {w c : n → ℝ}
    (hw : ∀ s, w s = c s + β * (P *ᵥ w) s) {K : ℝ} (hc : ∀ s, c s ≤ K) [Nonempty n] (s : n) :
    w s ≤ K / (1 - β) := by
  obtain ⟨s0, hs0⟩ := Finite.exists_max w
  have hPw : (P *ᵥ w) s0 ≤ w s0 := by
    show ∑ j, P s0 j * w j ≤ w s0
    calc ∑ j, P s0 j * w j ≤ ∑ j, P s0 j * w s0 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hs0 j) (hP.1 s0 j)
      _ = w s0 := by rw [← Finset.sum_mul, hP.2 s0, one_mul]
  have h1 := hw s0
  have h2 : (1 - β) * w s0 ≤ K := by nlinarith [hc s0]
  rw [le_div_iff₀ (by linarith)]
  nlinarith [hs0 s]

lemma bmk_lower (hP : IsMarkovMatrix P) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {w c : n → ℝ}
    (hw : ∀ s, w s = c s + β * (P *ᵥ w) s) {K : ℝ} (hc : ∀ s, K ≤ c s) [Nonempty n] (s : n) :
    K / (1 - β) ≤ w s := by
  have := bmk_upper hP hβ0 hβ1 (w := -w) (c := -c) (K := -K)
    (fun s => by simp only [Pi.neg_apply, Matrix.mulVec_neg]; rw [hw s]; ring)
    (fun s => by simp only [Pi.neg_apply]; linarith [hc s]) s
  simp only [Pi.neg_apply, neg_div] at this
  linarith

lemma bmk_abs (hP : IsMarkovMatrix P) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {w c : n → ℝ}
    (hw : ∀ s, w s = c s + β * (P *ᵥ w) s) {K : ℝ} (hc : ∀ s, |c s| ≤ K) [Nonempty n] (s : n) :
    |w s| ≤ K / (1 - β) := by
  rw [abs_le]
  constructor
  · have := bmk_lower hP hβ0 hβ1 hw (K := -K) (fun s => (abs_le.1 (hc s)).1) s
    rw [neg_div] at this; exact this
  · exact bmk_upper hP hβ0 hβ1 hw (fun s => (abs_le.1 (hc s)).2) s

theorem lemma_1b_core [Nonempty n] (Q : Matrix n n ℝ) (hQ : IsMarkovMatrix Q) :
    (1 - Q).rank + (limitMatrix Q).rank = Fintype.card n := by
  have hker : LinearMap.ker (1 - Q).mulVecLin = LinearMap.range (limitMatrix Q).mulVecLin := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · intro h
      refine ⟨v, bmk_fixvec hQ ?_⟩
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
      exact h.symm
    · rintro ⟨w, rfl⟩
      rw [Matrix.mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul, bmk_PL hQ, sub_self,
        Matrix.zero_mulVec]
  unfold Matrix.rank
  rw [← hker, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]

end MarkovTheory

end BlackwellDiscreteDP.NearOne

open BlackwellDiscreteDP.NearOne


theorem solution {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (Q : Matrix n n ℝ) (hQ : IsMarkovMatrix Q) :
    (1 - Q).rank + (limitMatrix Q).rank = Fintype.card n := by
  exact lemma_1b_core Q hQ
