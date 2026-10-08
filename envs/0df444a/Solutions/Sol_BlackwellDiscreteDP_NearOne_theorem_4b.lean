-- Prove2me | solution 1 for BlackwellDiscreteDP.NearOne.theorem_4b
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T21:57:20.83327+00:00
-- url     : https://prove2.me/submissions/d359bfd2-bfff-4e66-84cd-9fcf083da675

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
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


section Port


open Model

variable {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]

def bwL (M : Model St Act) (β : ℝ) (f : St → Act) (w : St → ℝ) : St → ℝ :=
  M.r f + β • (M.Q f).mulVec w

def bwShift (π : Policy St Act) : Policy St Act := fun n => π (n + 1)

lemma bw_Qn_stoch (M : Model St Act) (π : Policy St Act) (n : ℕ) :
    (∀ i j, 0 ≤ M.Qn π n i j) ∧ ∀ i, ∑ j, M.Qn π n i j = 1 := by
  induction n with
  | zero =>
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · simp only [Model.Qn, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [Model.Qn, Matrix.one_apply]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · simp only [Model.Qn, Matrix.mul_apply, Model.Q, Matrix.of_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (h1 i k) (M.q_nonneg k (π n k) j)
    · simp only [Model.Qn, Matrix.mul_apply, Model.Q, Matrix.of_apply]
      rw [Finset.sum_comm]
      rw [← h2 i]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.mul_sum, M.q_sum_one k (π n k), mul_one]

/-- bound of a stochastic matrix applied to a vector -/
lemma bw_stoch_mulVec_le {A : Matrix St St ℝ} (h1 : ∀ i j, 0 ≤ A i j) (h2 : ∀ i, ∑ j, A i j = 1)
    {u v : St → ℝ} {c : ℝ} (huv : ∀ s, u s ≤ v s + c) (i : St) :
    (A.mulVec u) i ≤ (A.mulVec v) i + c := by
  show ∑ j, A i j * u j ≤ ∑ j, A i j * v j + c
  calc ∑ j, A i j * u j ≤ ∑ j, A i j * (v j + c) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (huv j) (h1 i j)
    _ = ∑ j, A i j * v j + c := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, h2 i, one_mul]

lemma bw_stoch_abs {A : Matrix St St ℝ} (h1 : ∀ i j, 0 ≤ A i j) (h2 : ∀ i, ∑ j, A i j = 1)
    {u : St → ℝ} {c : ℝ} (hu : ∀ s, |u s| ≤ c) (i : St) : |(A.mulVec u) i| ≤ c := by
  have e : ∀ v : St → ℝ, (A.mulVec v) i = ∑ j, A i j * v j := fun v => rfl
  rw [abs_le, e]
  constructor
  · calc -c = ∑ j, A i j * (-c) := by rw [← Finset.sum_mul, h2 i, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (abs_le.1 (hu j)).1 (h1 i j)
  · calc ∑ j, A i j * u j ≤ ∑ j, A i j * c :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (abs_le.1 (hu j)).2 (h1 i j)
      _ = c := by rw [← Finset.sum_mul, h2 i, one_mul]

noncomputable def bwR (M : Model St Act) : ℝ := ∑ s, ∑ a, |M.i s a|

lemma bw_r_abs (M : Model St Act) (f : St → Act) (s : St) : |M.r f s| ≤ bwR M := by
  unfold bwR Model.r
  calc |M.i s (f s)| ≤ ∑ a, |M.i s a| :=
        Finset.single_le_sum (f := fun a => |M.i s a|) (fun a _ => abs_nonneg _) (Finset.mem_univ _)
    _ ≤ ∑ s, ∑ a, |M.i s a| :=
        Finset.single_le_sum (f := fun s => ∑ a, |M.i s a|)
          (fun s _ => Finset.sum_nonneg fun a _ => abs_nonneg _) (Finset.mem_univ _)

lemma bwR_nonneg (M : Model St Act) : 0 ≤ bwR M :=
  Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun a _ => abs_nonneg _

lemma bw_term_abs (M : Model St Act) (π : Policy St Act) (β : ℝ) (hβ0 : 0 ≤ β) (n : ℕ) (s : St) :
    |β ^ n * (M.Qn π n).mulVec (M.r (π n)) s| ≤ bwR M * β ^ n := by
  rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 n), mul_comm]
  exact mul_le_mul_of_nonneg_right
    (bw_stoch_abs (bw_Qn_stoch M π n).1 (bw_Qn_stoch M π n).2 (bw_r_abs M (π n)) s)
    (pow_nonneg hβ0 n)

lemma bw_term_summable (M : Model St Act) (π : Policy St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (s : St) : Summable (fun n => β ^ n * (M.Qn π n).mulVec (M.r (π n)) s) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_left (bwR M))
    (fun n => by rw [Real.norm_eq_abs]; exact bw_term_abs M π β hβ0 n s)

lemma bw_V_apply (M : Model St Act) (π : Policy St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (s : St) : M.V β π s = ∑' n, β ^ n * (M.Qn π n).mulVec (M.r (π n)) s := by
  unfold Model.V
  rw [tsum_apply]
  · rfl
  · exact Pi.summable.2 fun s => bw_term_summable M π β hβ0 hβ1 s

lemma bw_V_abs (M : Model St Act) (π : Policy St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (s : St) : |M.V β π s| ≤ bwR M / (1 - β) := by
  rw [bw_V_apply M π β hβ0 hβ1]
  have hs : Summable (fun n => ‖β ^ n * (M.Qn π n).mulVec (M.r (π n)) s‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => by rw [Real.norm_eq_abs]; exact bw_term_abs M π β hβ0 n s)
      ((summable_geometric_of_lt_one hβ0 hβ1).mul_left (bwR M))
  calc |∑' n, β ^ n * (M.Qn π n).mulVec (M.r (π n)) s|
        = ‖∑' n, β ^ n * (M.Qn π n).mulVec (M.r (π n)) s‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n, ‖β ^ n * (M.Qn π n).mulVec (M.r (π n)) s‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, bwR M * β ^ n := Summable.tsum_le_tsum
          (fun n => by rw [Real.norm_eq_abs]; exact bw_term_abs M π β hβ0 n s) hs
          ((summable_geometric_of_lt_one hβ0 hβ1).mul_left (bwR M))
    _ = bwR M / (1 - β) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1, div_eq_mul_inv]

lemma bw_Qn_cons (M : Model St Act) (f : St → Act) (π : Policy St Act) (n : ℕ) :
    M.Qn (Policy.cons f π) (n + 1) = M.Q f * M.Qn π n := by
  induction n with
  | zero => simp [Model.Qn, Policy.cons]
  | succ n ih =>
    rw [Model.Qn, ih, Model.Qn, Matrix.mul_assoc]
    rfl

lemma bw_V_cons (M : Model St Act) (f : St → Act) (π : Policy St Act) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) : M.V β (Policy.cons f π) = bwL M β f (M.V β π) := by
  funext s
  rw [bw_V_apply M _ β hβ0 hβ1, (bw_term_summable M _ β hβ0 hβ1 s).tsum_eq_zero_add]
  simp only [bwL, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  · simp [Model.Qn, Policy.cons]
  · have : ∀ n, β ^ (n + 1) * (M.Qn (Policy.cons f π) (n + 1)).mulVec (M.r (Policy.cons f π (n + 1))) s
        = β * ∑ s', M.Q f s s' * (β ^ n * (M.Qn π n).mulVec (M.r (π n)) s') := by
      intro n
      rw [bw_Qn_cons, ← Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec, dotProduct, Policy.cons, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      ring_nf
    simp_rw [this]
    rw [tsum_mul_left, Summable.tsum_finsetSum (fun s' _ => (bw_term_summable M π β hβ0 hβ1 s').mul_left _)]
    congr 1
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [tsum_mul_left, bw_V_apply M π β hβ0 hβ1]
    rfl

lemma bw_cons_stationary (f : St → Act) : Policy.cons f (Policy.stationary f) = Policy.stationary f := by
  funext n; cases n <;> rfl

lemma bw_V_fix (M : Model St Act) (f : St → Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    M.V β (Policy.stationary f) = bwL M β f (M.V β (Policy.stationary f)) := by
  conv_lhs => rw [← bw_cons_stationary f]
  exact bw_V_cons M f _ β hβ0 hβ1

lemma bw_Q_stoch (M : Model St Act) (f : St → Act) :
    (∀ i j, 0 ≤ M.Q f i j) ∧ ∀ i, ∑ j, M.Q f i j = 1 :=
  ⟨fun i j => M.q_nonneg i (f i) j, fun i => M.q_sum_one i (f i)⟩

lemma bw_L_apply (M : Model St Act) (β : ℝ) (f : St → Act) (w : St → ℝ) (s : St) :
    bwL M β f w s = M.i s (f s) + β * ∑ s', M.q s (f s) s' * w s' := rfl

lemma bw_L_le (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (f : St → Act) {u v : St → ℝ} {c : ℝ}
    (huv : ∀ s, u s ≤ v s + c) (s : St) : bwL M β f u s ≤ bwL M β f v s + β * c := by
  have := bw_stoch_mulVec_le (bw_Q_stoch M f).1 (bw_Q_stoch M f).2 huv s
  show M.r f s + β * (M.Q f).mulVec u s ≤ M.r f s + β * (M.Q f).mulVec v s + β * c
  nlinarith

lemma bw_L_mono (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (f : St → Act) {u v : St → ℝ}
    (huv : u ≤ v) : bwL M β f u ≤ bwL M β f v := by
  intro s
  have := bw_L_le M β hβ0 f (u := u) (v := v) (c := 0) (fun s => by simpa using huv s) s
  simpa using this

lemma bw_cons_shift (π : Policy St Act) : Policy.cons (π 0) (bwShift π) = π := by
  funext n; cases n <;> rfl

theorem bw_thm1 (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (πstar : Policy St Act)
    (h : ∀ f : St → Act, M.V β (Policy.cons f πstar) ≤ M.V β πstar) :
    M.IsBetaOptimal β πstar := by
  set D := Set.range (fun p : Policy St Act × St => M.V β p.1 p.2 - M.V β πstar p.2) with hD
  have hbdd : BddAbove D := by
    refine ⟨2 * (bwR M / (1 - β)), ?_⟩
    rintro _ ⟨⟨π, s⟩, rfl⟩
    have h1 := (abs_le.1 (bw_V_abs M π β hβ0 hβ1 s)).2
    have h2 := (abs_le.1 (bw_V_abs M πstar β hβ0 hβ1 s)).1
    simp only; linarith
  have hne : D.Nonempty := ⟨_, ⟨(πstar, Classical.arbitrary St), rfl⟩⟩
  have hle : ∀ π s, M.V β π s - M.V β πstar s ≤ sSup D :=
    fun π s => le_csSup hbdd ⟨(π, s), rfl⟩
  have key : ∀ π s, M.V β π s - M.V β πstar s ≤ β * sSup D := by
    intro π s
    have e : M.V β π = bwL M β (π 0) (M.V β (bwShift π)) := by
      conv_lhs => rw [← bw_cons_shift π]
      exact bw_V_cons M _ _ β hβ0 hβ1
    have h1 := bw_L_le M β hβ0 (π 0) (u := M.V β (bwShift π)) (v := M.V β πstar)
      (c := sSup D) (fun s' => by linarith [hle (bwShift π) s']) s
    have h2 := h (π 0) s
    rw [bw_V_cons M _ _ β hβ0 hβ1] at h2
    rw [e]; linarith
  have hd : sSup D ≤ β * sSup D := csSup_le hne (by rintro _ ⟨⟨π, s⟩, rfl⟩; exact key π s)
  have hd0 : sSup D ≤ 0 := by nlinarith
  intro π s
  linarith [hle π s]

lemma bw_le_V_stat (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act)
    (w : St → ℝ) (hw : w ≤ bwL M β f w) : w ≤ M.V β (Policy.stationary f) := by
  set Vf := M.V β (Policy.stationary f)
  obtain ⟨s0, hs0⟩ := Finite.exists_max (fun s => w s - Vf s)
  have h1 := bw_L_le M β hβ0 f (u := w) (v := Vf) (c := w s0 - Vf s0)
    (fun s => by have : w s - Vf s ≤ w s0 - Vf s0 := hs0 s; linarith) s0
  have hfix := congrFun (bw_V_fix M f β hβ0 hβ1) s0
  have h2 := hw s0
  have hd : w s0 - Vf s0 ≤ 0 := by nlinarith
  intro s
  have : w s - Vf s ≤ w s0 - Vf s0 := hs0 s; linarith

theorem bw_thm2 (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act)
    (π : Policy St Act)
    (h : M.V β π ≤ M.V β (Policy.cons f π) ∧ M.V β (Policy.cons f π) ≠ M.V β π) :
    M.V β π ≤ M.V β (Policy.stationary f) ∧ M.V β (Policy.stationary f) ≠ M.V β π := by
  rw [bw_V_cons M f π β hβ0 hβ1] at h
  have hw := bw_le_V_stat M β hβ0 hβ1 f _ h.1
  refine ⟨hw, fun heq => h.2 ?_⟩
  have h3 : bwL M β f (M.V β π) ≤ M.V β π := by
    have := bw_L_mono M β hβ0 f hw
    rw [← bw_V_fix M f β hβ0 hβ1, heq] at this
    exact this
  exact le_antisymm h3 h.1

theorem bw_thm3 (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act) :
    ((∀ s : St, M.betaImprovementSet β f s = ∅) → M.IsBetaOptimal β (Policy.stationary f)) ∧
    (∀ g : St → Act, (∃ s : St, g s ∈ M.betaImprovementSet β f s) →
        (∀ s : St, g s ∉ M.betaImprovementSet β f s → g s = f s) →
        M.V β (Policy.stationary f) ≤ M.V β (Policy.stationary g) ∧
          M.V β (Policy.stationary g) ≠ M.V β (Policy.stationary f)) := by
  constructor
  · intro hG
    apply bw_thm1 M β hβ0 hβ1
    intro g s
    rw [bw_V_cons M g _ β hβ0 hβ1, bw_L_apply]
    by_contra hlt
    push Not at hlt
    have : g s ∈ M.betaImprovementSet β f s := hlt
    rw [hG s] at this
    exact this
  · intro g ⟨s0, hs0⟩ hb
    apply bw_thm2 M β hβ0 hβ1 g (Policy.stationary f)
    rw [bw_V_cons M g _ β hβ0 hβ1]
    have hfix := bw_V_fix M f β hβ0 hβ1
    have hge : ∀ s, M.V β (Policy.stationary f) s ≤ bwL M β g (M.V β (Policy.stationary f)) s := by
      intro s
      by_cases hs : g s ∈ M.betaImprovementSet β f s
      · rw [bw_L_apply]; exact le_of_lt hs
      · have e : bwL M β g (M.V β (Policy.stationary f)) s = bwL M β f (M.V β (Policy.stationary f)) s := by
          simp only [bw_L_apply, hb s hs]
        rw [e, ← hfix]
    refine ⟨hge, fun heq => ?_⟩
    have := congrFun heq s0
    have hs0' : M.V β (Policy.stationary f) s0 < bwL M β g (M.V β (Policy.stationary f)) s0 := by
      rw [bw_L_apply]; exact hs0
    linarith

lemma bw_improve (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act)
    (hs : ∃ s, (M.betaImprovementSet β f s).Nonempty) :
    ∃ g : St → Act, M.V β (Policy.stationary f) ≤ M.V β (Policy.stationary g) ∧
          M.V β (Policy.stationary g) ≠ M.V β (Policy.stationary f) := by
  classical
  let g : St → Act := fun s => if h : (M.betaImprovementSet β f s).Nonempty then h.some else f s
  refine ⟨g, (bw_thm3 M β hβ0 hβ1 f).2 g ?_ ?_⟩
  · obtain ⟨s, hs⟩ := hs
    refine ⟨s, ?_⟩
    simp only [g, dif_pos hs]; exact hs.some_mem
  · intro s hgs
    by_cases h : (M.betaImprovementSet β f s).Nonempty
    · exfalso; apply hgs; simp only [g, dif_pos h]; exact h.some_mem
    · simp only [g, dif_neg h]

lemma bw_opt_of_stat (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act)
    (h : ∀ g : St → Act, M.V β (Policy.stationary g) ≤ M.V β (Policy.stationary f)) :
    M.IsBetaOptimal β (Policy.stationary f) := by
  by_cases hs : ∃ s, (M.betaImprovementSet β f s).Nonempty
  · obtain ⟨g, h1, h2⟩ := bw_improve M β hβ0 hβ1 f hs
    exact absurd (le_antisymm (h g) h1) h2
  · push Not at hs
    exact (bw_thm3 M β hβ0 hβ1 f).1 fun s => hs s

lemma bw_exists_opt (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ f : St → Act, M.IsBetaOptimal β (Policy.stationary f) := by
  obtain ⟨f, hf⟩ := Finite.exists_max (fun f : St → Act => ∑ s, M.V β (Policy.stationary f) s)
  refine ⟨f, ?_⟩
  by_cases hs : ∃ s, (M.betaImprovementSet β f s).Nonempty
  · obtain ⟨g, h1, h2⟩ := bw_improve M β hβ0 hβ1 f hs
    exfalso
    have hne : ∃ s, M.V β (Policy.stationary f) s < M.V β (Policy.stationary g) s := by
      by_contra hc
      push Not at hc
      exact h2 (funext fun s => le_antisymm (hc s) (h1 s))
    obtain ⟨s, hs⟩ := hne
    have := Finset.sum_lt_sum (fun i _ => h1 i) ⟨s, Finset.mem_univ s, hs⟩
    have := hf g
    linarith
  · push Not at hs
    exact (bw_thm3 M β hβ0 hβ1 f).1 fun s => hs s

theorem bw_frequently (M : Model St Act) :
    ∃ fstar : St → Act, ∀ β₀ : ℝ, β₀ < 1 →
      ∃ β : ℝ, β₀ < β ∧ β < 1 ∧ M.IsBetaOptimal β (Policy.stationary fstar) := by
  by_contra H
  push Not at H
  choose b hb1 hb using H
  set m := Finset.univ.sup' Finset.univ_nonempty b with hm
  have hm1 : m < 1 := by
    rw [hm, Finset.sup'_lt_iff]; exact fun f _ => hb1 f
  set B := max m 0
  have hB1 : B < 1 := max_lt hm1 one_pos
  obtain ⟨f, hf⟩ := bw_exists_opt M ((B + 1) / 2) (by have := le_max_right m 0; linarith)
    (by linarith)
  have hbf : b f ≤ m := Finset.le_sup' b (Finset.mem_univ f)
  exact hb f ((B + 1) / 2) (by have := le_max_left m 0; linarith) (by linarith) hf


end Port

section RealAsymptotics

lemma bev {c : ℝ} (hc : c < 1) : ∀ᶠ β in 𝓝[<] (1 : ℝ), c < β ∧ β < 1 := by
  filter_upwards [Ioo_mem_nhdsLT hc] with β hβ using hβ

lemma bsmallK {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) : ∀ᶠ β in 𝓝[<] (1 : ℝ), K * (1 - β) < ε := by
  have hc : 1 - ε / (K + 1) < 1 := by have : 0 < ε / (K + 1) := by positivity
                                      linarith
  filter_upwards [bev hc] with β ⟨h1, h2⟩
  have h3 : 1 - β < ε / (K + 1) := by linarith
  rw [lt_div_iff₀ (by linarith)] at h3
  nlinarith

lemma binv_tendsto : Tendsto (fun β : ℝ => (1 - β)⁻¹) (𝓝[<] (1 : ℝ)) atTop := by
  have h1 : Tendsto (fun β : ℝ => 1 - β) (𝓝[<] (1 : ℝ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun β : ℝ => 1 - β) (𝓝 (1 : ℝ)) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      exact sub_pos.2 (show β < 1 from hβ)
  exact tendsto_inv_nhdsGT_zero.comp h1

lemma bneg_eventually {D : ℝ → ℝ} {A B K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ β, 0 ≤ β → β < 1 → |D β - (A * (β / (1 - β)) + B)| ≤ K * (1 - β))
    (h : A < 0 ∨ (A = 0 ∧ B < 0)) : ∀ᶠ β in 𝓝[<] (1 : ℝ), D β < 0 := by
  rcases h with hA | ⟨hA, hB⟩
  · have hg : Tendsto (fun β : ℝ => β / (1 - β)) (𝓝[<] (1 : ℝ)) atTop := by
      have : (fun β : ℝ => β / (1 - β)) =ᶠ[𝓝[<] (1 : ℝ)] (fun β => (1 - β)⁻¹ + (-1)) := by
        filter_upwards [self_mem_nhdsWithin] with β hβ
        have : (1 - β) ≠ 0 := by have := sub_pos.2 (show β < 1 from hβ); linarith
        field_simp; ring
      exact (tendsto_atTop_add_const_right _ _ binv_tendsto).congr' this.symm
    have hAg := (hg.const_mul_atTop_of_neg hA)
    filter_upwards [bev (show (0 : ℝ) < 1 by norm_num), tendsto_atBot.1 hAg (-(B + K + 1))]
      with β ⟨h0, h1⟩ h2
    have := (abs_le.1 (hD β h0.le h1)).2
    have : K * (1 - β) ≤ K := by nlinarith
    linarith
  · filter_upwards [bev (show (0 : ℝ) < 1 by norm_num), bsmallK hK (show 0 < -B by linarith)]
      with β ⟨h0, h1⟩ h2
    have := (abs_le.1 (hD β h0.le h1)).2
    rw [hA, zero_mul, zero_add] at this
    linarith

lemma bpos_eventually {D : ℝ → ℝ} {A B K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ β, 0 ≤ β → β < 1 → |D β - (A * (β / (1 - β)) + B)| ≤ K * (1 - β))
    (h : 0 < A ∨ (A = 0 ∧ 0 < B)) : ∀ᶠ β in 𝓝[<] (1 : ℝ), 0 < D β := by
  have := bneg_eventually (D := fun β => - D β) (A := -A) (B := -B) hK
    (fun β h0 h1 => by
      have := hD β h0 h1
      rw [← abs_neg]; convert this using 2; ring)
    (by rcases h with h | ⟨h1, h2⟩
        · left; linarith
        · right; exact ⟨by rw [h1]; ring, by linarith⟩)
  filter_upwards [this] with β hβ
  linarith

lemma bsmall_eventually {D : ℝ → ℝ} {A B K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ β, 0 ≤ β → β < 1 → |D β - (A * (β / (1 - β)) + B)| ≤ K * (1 - β))
    (h : A < 0 ∨ (A = 0 ∧ B ≤ 0)) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ β in 𝓝[<] (1 : ℝ), D β ≤ ε := by
  rcases h with hA | ⟨hA, hB⟩
  · filter_upwards [bneg_eventually hK hD (Or.inl hA)] with β hβ
    linarith
  · filter_upwards [bev (show (0 : ℝ) < 1 by norm_num), bsmallK hK hε] with β ⟨h0, h1⟩ h2
    have := (abs_le.1 (hD β h0.le h1)).2
    rw [hA, zero_mul, zero_add] at this
    linarith

/-- lexicographic extraction -/
lemma blex {X Y K : ℝ} (hK : 0 ≤ K)
    (h : ∀ ε > 0, ∃ᶠ β in 𝓝[<] (1 : ℝ), X * (1 - β)⁻¹ + Y ≤ ε + K * (1 - β)) :
    X ≤ 0 ∧ (X = 0 → Y ≤ 0) := by
  constructor
  · by_contra hX
    push Not at hX
    have hg := binv_tendsto.const_mul_atTop hX
    obtain ⟨β, h1, ⟨h0, h2⟩, h3⟩ := ((h 1 one_pos).and_eventually
      ((bev (show (0 : ℝ) < 1 by norm_num)).and (tendsto_atTop.1 hg (|Y| + K + 2)))).exists
    have : K * (1 - β) ≤ K := by nlinarith
    have := neg_abs_le Y
    linarith
  · intro hX
    by_contra hY
    push Not at hY
    obtain ⟨β, h1, h2⟩ := ((h (Y / 2) (by linarith)).and_eventually
      (bsmallK hK (show 0 < Y / 2 by linarith))).exists
    rw [hX, zero_mul, zero_add] at h1
    linarith

lemma bfreq_of {p : ℝ → Prop} (h : ∀ β₀ : ℝ, β₀ < 1 → ∃ β, β₀ < β ∧ β < 1 ∧ p β) :
    ∃ᶠ β in 𝓝[<] (1 : ℝ), p β := by
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hU
  obtain ⟨β, h1, h2, h3⟩ := h l hl
  exact ⟨β, hsub ⟨h1, h2⟩, h3⟩

lemma bex_of_ev {p : ℝ → Prop} (h : ∀ᶠ β in 𝓝[<] (1 : ℝ), p β) :
    ∃ β₀ < (1 : ℝ), ∀ β : ℝ, β₀ < β → β < 1 → p β := by
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 h
  exact ⟨l, hl, fun β h1 h2 => hsub ⟨h1, h2⟩⟩

lemma bev_of_ex {p : ℝ → Prop} (h : ∃ β₀ < (1 : ℝ), ∀ β : ℝ, β₀ < β → β < 1 → p β) :
    ∀ᶠ β in 𝓝[<] (1 : ℝ), p β := by
  obtain ⟨l, hl, hsub⟩ := h
  exact mem_nhdsLT_iff_exists_Ioo_subset.2 ⟨l, hl, fun β hβ => hsub β hβ.1 hβ.2⟩

end RealAsymptotics

section ModelTheory2
variable {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]

lemma bQ_mk (M : Model St Act) (f : St → Act) : IsMarkovMatrix (M.Q f) :=
  ⟨fun i j => M.q_nonneg i (f i) j, fun i => M.q_sum_one i (f i)⟩

lemma bQx (M : Model St Act) (f : St → Act) : M.Q f *ᵥ M.x f = M.x f := by
  simp only [Model.x, Model.Qstar, Matrix.mulVec_mulVec, bmk_PL (bQ_mk M f)]

lemma bQy (M : Model St Act) (f : St → Act) : M.Q f *ᵥ M.y f = M.y f + M.x f - M.r f := by
  simp only [Model.y, Model.x, Model.Hf, Model.Qstar, Matrix.mulVec_mulVec, bmk_PH (bQ_mk M f),
    Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]

lemma bLx (M : Model St Act) (f : St → Act) : M.Qstar f *ᵥ M.x f = M.x f := by
  simp only [Model.x, Model.Qstar, Matrix.mulVec_mulVec, bmk_LL (bQ_mk M f)]

lemma bLy (M : Model St Act) (f : St → Act) : M.Qstar f *ᵥ M.y f = 0 := by
  simp only [Model.y, Model.Hf, Model.Qstar, Matrix.mulVec_mulVec, bmk_LH (bQ_mk M f),
    Matrix.zero_mulVec]

lemma bV_fix' (M : Model St Act) (f : St → Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (s : St) :
    M.V β (Policy.stationary f) s =
      M.r f s + β * (M.Q f *ᵥ M.V β (Policy.stationary f)) s := by
  have := congrFun (bw_V_fix M f β hβ0 hβ1) s
  exact this

lemma bpDot_abs (M : Model St Act) (s : St) (a : Act) {w : St → ℝ} {C : ℝ}
    (hw : ∀ t, |w t| ≤ C) : |M.pDot s a w| ≤ C := by
  unfold Model.pDot
  rw [abs_le]; constructor
  · calc -C = ∑ t, M.q s a t * (-C) := by rw [← Finset.sum_mul, M.q_sum_one, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun t _ =>
          mul_le_mul_of_nonneg_left (abs_le.1 (hw t)).1 (M.q_nonneg s a t)
  · calc ∑ t, M.q s a t * w t ≤ ∑ t, M.q s a t * C := Finset.sum_le_sum fun t _ =>
          mul_le_mul_of_nonneg_left (abs_le.1 (hw t)).2 (M.q_nonneg s a t)
      _ = C := by rw [← Finset.sum_mul, M.q_sum_one, one_mul]

lemma babs_le_sum (w : St → ℝ) (s : St) : |w s| ≤ ∑ t, |w t| :=
  Finset.single_le_sum (f := fun t => |w t|) (fun t _ => abs_nonneg _) (Finset.mem_univ s)

theorem b_laurent (M : Model St Act) (f : St → Act) : ∃ K, 0 ≤ K ∧ ∀ β, 0 ≤ β → β < 1 → ∀ s,
    |M.V β (Policy.stationary f) s - M.x f s / (1 - β) - M.y f s| ≤ K * (1 - β) := by
  have hP := bQ_mk M f
  set u : St → ℝ := M.r f - M.x f - M.y f with hu
  set Hu := M.Hf f *ᵥ u with hHu
  have hLu : limitMatrix (M.Q f) *ᵥ u = 0 := by
    have h1 := bLx M f
    have h2 := bLy M f
    simp only [Model.Qstar] at h1 h2
    simp only [u, Matrix.mulVec_sub, h1, h2]
    simp [Model.x, Model.Qstar]
  have hQHu : M.Q f *ᵥ Hu = Hu - u := by
    simp only [Hu, Model.Hf, Matrix.mulVec_mulVec, bmk_PH hP, Matrix.sub_mulVec,
      Matrix.add_mulVec, Matrix.one_mulVec, hLu, add_zero]
  refine ⟨∑ t, (|Hu t| + |u t - Hu t|), by positivity, ?_⟩
  intro β hβ0 hβ1 s
  have h1β : (0 : ℝ) < 1 - β := by linarith
  set V := M.V β (Policy.stationary f) with hV
  set e : St → ℝ := V - (1 - β)⁻¹ • M.x f - M.y f - (1 - β) • Hu with he_def
  have he : ∀ t, e t = (1 - β) ^ 2 * (u t - Hu t) + β * (M.Q f *ᵥ e) t := by
    intro t
    have hPe : M.Q f *ᵥ e = M.Q f *ᵥ V - (1 - β)⁻¹ • (M.Q f *ᵥ M.x f) - M.Q f *ᵥ M.y f
        - (1 - β) • (M.Q f *ᵥ Hu) := by
      simp only [e, Matrix.mulVec_sub, Matrix.mulVec_smul]
    rw [hPe, bQx, bQy, hQHu]
    have hVt := bV_fix' M f β hβ0 hβ1 t
    rw [← hV] at hVt
    simp only [e, u, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    have hinv : (1 - β)⁻¹ * (1 - β) = 1 := inv_mul_cancel₀ h1β.ne'
    linear_combination hVt - M.x f t * hinv
  have hbd := bmk_abs hP hβ0 hβ1 (w := e) (c := fun t => (1 - β) ^ 2 * (u t - Hu t)) he
    (K := (1 - β) ^ 2 * ∑ t, |u t - Hu t|) (fun t => by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (babs_le_sum (fun t => u t - Hu t) t) (by positivity)) s
  have e1 : ((1 - β) ^ 2 * ∑ t, |u t - Hu t|) / (1 - β) = (1 - β) * ∑ t, |u t - Hu t| := by
    field_simp
  rw [e1] at hbd
  have hes : V s - M.x f s / (1 - β) - M.y f s = e s + (1 - β) * Hu s := by
    simp only [e, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; rw [div_eq_inv_mul]; ring
  rw [hes, Finset.sum_add_distrib, add_mul]
  have h3 : |(1 - β) * Hu s| ≤ (1 - β) * ∑ t, |Hu t| := by
    rw [abs_mul, abs_of_pos h1β]
    exact mul_le_mul_of_nonneg_left (babs_le_sum Hu s) h1β.le
  calc |e s + (1 - β) * Hu s| ≤ |e s| + |(1 - β) * Hu s| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- the one-step advantage of action `a` at `s` against `V_β(f^∞)` -/
noncomputable def bδ (M : Model St Act) (β : ℝ) (f : St → Act) (s : St) (a : Act) : ℝ :=
  M.i s a + β * M.pDot s a (M.V β (Policy.stationary f)) - M.V β (Policy.stationary f) s

noncomputable def bA (M : Model St Act) (f : St → Act) (s : St) (a : Act) : ℝ :=
  M.pDot s a (M.x f) - M.x f s

noncomputable def bB (M : Model St Act) (f : St → Act) (s : St) (a : Act) : ℝ :=
  M.i s a + M.pDot s a (M.y f) - M.x f s - M.y f s

theorem b_delta (M : Model St Act) (f : St → Act) (s : St) (a : Act) :
    ∃ K, 0 ≤ K ∧ ∀ β, 0 ≤ β → β < 1 →
      |bδ M β f s a - (bA M f s a * (β / (1 - β)) + bB M f s a)| ≤ K * (1 - β) := by
  obtain ⟨K, hK, hL⟩ := b_laurent M f
  refine ⟨∑ t, |M.y f t| + 2 * K, by positivity, ?_⟩
  intro β hβ0 hβ1
  have h1β : (0 : ℝ) < 1 - β := by linarith
  set V := M.V β (Policy.stationary f) with hV
  set E : St → ℝ := fun t => V t - M.x f t / (1 - β) - M.y f t with hE
  have hp : M.pDot s a V = M.pDot s a (M.x f) / (1 - β) + M.pDot s a (M.y f) + M.pDot s a E := by
    simp only [Model.pDot, E]
    rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    field_simp
    ring
  have hEs : |E s| ≤ K * (1 - β) := hL β hβ0 hβ1 s
  have hpE : |M.pDot s a E| ≤ K * (1 - β) := bpDot_abs M s a (fun t => hL β hβ0 hβ1 t)
  have hpy : |M.pDot s a (M.y f)| ≤ ∑ t, |M.y f t| := bpDot_abs M s a (fun t => babs_le_sum _ t)
  have key : bδ M β f s a - (bA M f s a * (β / (1 - β)) + bB M f s a) =
      -(1 - β) * M.pDot s a (M.y f) + β * M.pDot s a E - E s := by
    simp only [bδ, bA, bB]
    rw [← hV, hp]
    have : V s = M.x f s / (1 - β) + M.y f s + E s := by simp only [E]; ring
    rw [this]
    field_simp
    ring
  rw [key]
  have h4 : |-(1 - β) * M.pDot s a (M.y f)| ≤ (1 - β) * ∑ t, |M.y f t| := by
    rw [abs_mul, abs_neg, abs_of_pos h1β]
    exact mul_le_mul_of_nonneg_left hpy h1β.le
  have h5 : |β * M.pDot s a E| ≤ K * (1 - β) := by
    rw [abs_mul, abs_of_nonneg hβ0]
    calc β * |M.pDot s a E| ≤ 1 * |M.pDot s a E| :=
          mul_le_mul_of_nonneg_right hβ1.le (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hpE
  calc |-(1 - β) * M.pDot s a (M.y f) + β * M.pDot s a E - E s|
      ≤ |-(1 - β) * M.pDot s a (M.y f) + β * M.pDot s a E| + |E s| := abs_sub _ _
    _ ≤ |-(1 - β) * M.pDot s a (M.y f)| + |β * M.pDot s a E| + |E s| := by
        linarith [abs_add_le (-(1 - β) * M.pDot s a (M.y f)) (β * M.pDot s a E)]
    _ ≤ _ := by nlinarith

lemma bδ_self (M : Model St Act) (f : St → Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (s : St) :
    bδ M β f s (f s) = 0 := by
  have := bV_fix' M f β hβ0 hβ1 s
  simp only [bδ]
  have e : M.pDot s (f s) (M.V β (Policy.stationary f)) =
      (M.Q f *ᵥ M.V β (Policy.stationary f)) s := rfl
  rw [e]
  have e2 : M.r f s = M.i s (f s) := rfl
  rw [e2] at this
  linarith

lemma bdiff (M : Model St Act) (f g : St → Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (s : St) :
    (M.V β (Policy.stationary g) - M.V β (Policy.stationary f)) s =
      bδ M β f s (g s) + β * (M.Q g *ᵥ (M.V β (Policy.stationary g) - M.V β (Policy.stationary f))) s := by
  have h1 := bV_fix' M g β hβ0 hβ1 s
  simp only [bδ, Pi.sub_apply, Matrix.mulVec_sub]
  have e : M.pDot s (g s) (M.V β (Policy.stationary f)) =
      (M.Q g *ᵥ M.V β (Policy.stationary f)) s := rfl
  have e2 : M.r g s = M.i s (g s) := rfl
  rw [e]
  rw [e2] at h1
  linarith

lemma bE_self (M : Model St Act) (f : St → Act) (s : St) : f s ∈ M.gainBiasEqualSet f s := by
  have h1 := congrFun (bQx M f) s
  have h2 := congrFun (bQy M f) s
  refine ⟨h1, ?_⟩
  have e : M.pDot s (f s) (M.y f) = (M.Q f *ᵥ M.y f) s := rfl
  have e2 : M.r f s = M.i s (f s) := rfl
  rw [e, h2]
  simp only [Pi.add_apply, Pi.sub_apply, e2]
  ring

/-- difference expansion of two stationary policies -/
theorem b_laurent2 (M : Model St Act) (f g : St → Act) : ∃ K, 0 ≤ K ∧ ∀ β, 0 ≤ β → β < 1 → ∀ s,
    |(M.V β (Policy.stationary g) s - M.V β (Policy.stationary f) s)
      - ((M.x g s - M.x f s) * (1 - β)⁻¹ + (M.y g s - M.y f s))| ≤ K * (1 - β) := by
  obtain ⟨K1, hK1, h1⟩ := b_laurent M f
  obtain ⟨K2, hK2, h2⟩ := b_laurent M g
  refine ⟨K1 + K2, by positivity, fun β hβ0 hβ1 s => ?_⟩
  have a1 := h1 β hβ0 hβ1 s
  have a2 := h2 β hβ0 hβ1 s
  have : (M.V β (Policy.stationary g) s - M.V β (Policy.stationary f) s)
      - ((M.x g s - M.x f s) * (1 - β)⁻¹ + (M.y g s - M.y f s)) =
      (M.V β (Policy.stationary g) s - M.x g s / (1 - β) - M.y g s) -
      (M.V β (Policy.stationary f) s - M.x f s / (1 - β) - M.y f s) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  rw [this]
  calc _ ≤ |M.V β (Policy.stationary g) s - M.x g s / (1 - β) - M.y g s| +
        |M.V β (Policy.stationary f) s - M.x f s / (1 - β) - M.y f s| := abs_sub _ _
    _ ≤ _ := by linarith

lemma bnear_of (M : Model St Act) (g : St → Act)
    (h : ∀ h' : St → Act, ∀ ε > 0, ∀ᶠ β in 𝓝[<] (1 : ℝ),
      ∀ s, M.V β (Policy.stationary h') s ≤ M.V β (Policy.stationary g) s + ε) :
    M.IsNearlyOptimal (Policy.stationary g) := by
  intro ε hε
  have H := (bev (show (0 : ℝ) < 1 by norm_num)).and (Filter.eventually_all.2 fun h' => h h' ε hε)
  obtain ⟨β₀, hβ₀, hsub⟩ := bex_of_ev H
  refine ⟨β₀, hβ₀, fun β h1 h2 π' s => ?_⟩
  obtain ⟨⟨hb0, hb1⟩, hall⟩ := hsub β h1 h2
  obtain ⟨f, hf⟩ := bw_exists_opt M β hb0.le hb1
  exact (hf π' s).trans (hall f s)

lemma bnear_to (M : Model St Act) (g : St → Act) (hg : M.IsNearlyOptimal (Policy.stationary g))
    (π' : Policy St Act) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ β in 𝓝[<] (1 : ℝ),
      ∀ s, M.V β π' s ≤ M.V β (Policy.stationary g) s + ε := by
  obtain ⟨β₀, hβ₀, h⟩ := hg ε hε
  exact bev_of_ex ⟨β₀, hβ₀, fun β h1 h2 => h β h1 h2 π'⟩

end ModelTheory2

section Theorems
variable {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]

lemma b_notG (M : Model St Act) (f : St → Act) (s : St) (a : Act)
    (h : a ∉ M.gainBiasImprovementSet f s) :
    bA M f s a < 0 ∨ (bA M f s a = 0 ∧ bB M f s a ≤ 0) := by
  have h1 : ¬ (M.pDot s a (M.x f) > M.x f s) := fun hh => h (Or.inl hh)
  have h2 : M.pDot s a (M.x f) = M.x f s →
      ¬ (M.i s a + M.pDot s a (M.y f) > M.x f s + M.y f s) := fun he hb => h (Or.inr ⟨he, hb⟩)
  simp only [bA, bB]
  rcases lt_or_eq_of_le (not_lt.1 h1) with hl | he
  · left; linarith
  · right
    refine ⟨by linarith, ?_⟩
    have := not_lt.1 (h2 he)
    linarith

lemma b_notGE (M : Model St Act) (f : St → Act) (s : St) (a : Act)
    (h : a ∉ M.gainBiasImprovementSet f s) (h' : a ∉ M.gainBiasEqualSet f s) :
    bA M f s a < 0 ∨ (bA M f s a = 0 ∧ bB M f s a < 0) := by
  rcases b_notG M f s a h with hl | ⟨he, hb⟩
  · left; exact hl
  · right
    refine ⟨he, lt_of_le_of_ne hb ?_⟩
    intro hc
    apply h'
    simp only [bA, bB] at he hc
    exact ⟨by linarith, by linarith⟩

theorem lemma_2_core (M : Model St Act) (f g : St → Act)
    (hE : ∀ s, g s ∈ M.gainBiasEqualSet f s) :
    M.x g = M.x f ∧ (M.Qstar g * M.Qstar f = M.Qstar g → M.y g = M.y f) := by
  have hQx : M.Q g *ᵥ M.x f = M.x f := funext fun s => (hE s).1
  have hQy : M.Q g *ᵥ M.y f = M.x f + M.y f - M.r g := funext fun s => by
    have := (hE s).2
    show M.pDot s (g s) (M.y f) = M.x f s + M.y f s - M.i s (g s)
    linarith
  have hPg := bQ_mk M g
  have hLP : M.Qstar g * M.Q g = M.Qstar g := bmk_LP hPg
  have hxg : M.x g = M.x f := by
    have hr : M.r g = M.x f + M.y f - M.Q g *ᵥ M.y f := by rw [hQy]; abel
    have h1 : M.Qstar g *ᵥ M.x f = M.x f := bmk_fixvec hPg hQx
    calc M.x g = M.Qstar g *ᵥ M.r g := rfl
      _ = M.Qstar g *ᵥ M.x f + M.Qstar g *ᵥ M.y f - (M.Qstar g * M.Q g) *ᵥ M.y f := by
          rw [hr, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_mulVec]
      _ = M.x f := by rw [hLP, h1]; abel
  refine ⟨hxg, fun hQQ => ?_⟩
  set d := M.y g - M.y f with hd_def
  have hd : M.Q g *ᵥ d = d := by
    simp only [d, Matrix.mulVec_sub, bQy M g, hQy, hxg]; abel
  have hLd : M.Qstar g *ᵥ d = 0 := by
    have e1 : M.Qstar g *ᵥ M.y f = 0 := by
      rw [← hQQ, ← Matrix.mulVec_mulVec, bLy M f, Matrix.mulVec_zero]
    simp only [d, Matrix.mulVec_sub, bLy M g, e1, sub_zero]
  have : d = 0 := by
    have h2 : limitMatrix (M.Q g) *ᵥ d = d := bmk_fixvec hPg hd
    rw [← h2]; exact hLd
  exact sub_eq_zero.1 this

theorem theorem_4b_core (M : Model St Act) (f g : St → Act)
    (hG : ∃ s, g s ∈ M.gainBiasImprovementSet f s)
    (hfix : ∀ s, g s ∉ M.gainBiasImprovementSet f s → g s = f s) :
    ∃ β₀ < (1 : ℝ), ∀ β : ℝ, β₀ < β → β < 1 →
      VecGt (M.V β (Policy.stationary g)) (M.V β (Policy.stationary f)) := by
  obtain ⟨s0, hs0⟩ := hG
  have hev : ∀ s, g s ∈ M.gainBiasImprovementSet f s →
      ∀ᶠ β in 𝓝[<] (1 : ℝ), 0 < bδ M β f s (g s) := by
    intro s hs
    obtain ⟨K, hK, hD⟩ := b_delta M f s (g s)
    apply bpos_eventually hK hD
    rcases hs with h | ⟨h1, h2⟩
    · left; simp only [bA]; linarith
    · right; simp only [bA, bB]; constructor <;> linarith
  have hall : ∀ᶠ β in 𝓝[<] (1 : ℝ), ∀ s, g s ∈ M.gainBiasImprovementSet f s →
      0 < bδ M β f s (g s) := by
    refine Filter.eventually_all.2 fun s => ?_
    by_cases hs : g s ∈ M.gainBiasImprovementSet f s
    · filter_upwards [hev s hs] with β h _ using h
    · exact Eventually.of_forall fun β h => absurd h hs
  apply bex_of_ev
  filter_upwards [hall, bev (show (0 : ℝ) < 1 by norm_num)] with β hβ ⟨h0, h1⟩
  have hw := bdiff M f g β h0.le h1
  set w := M.V β (Policy.stationary g) - M.V β (Policy.stationary f) with hw_def
  have hδ : ∀ s, 0 ≤ bδ M β f s (g s) := by
    intro s
    by_cases hs : g s ∈ M.gainBiasImprovementSet f s
    · exact (hβ s hs).le
    · rw [hfix s hs, bδ_self M f β h0.le h1]
  have hw0 : ∀ s, 0 ≤ w s := fun s => by
    have := bmk_lower (bQ_mk M g) h0.le h1 hw (K := 0) hδ s
    rwa [zero_div] at this
  refine ⟨fun s => ?_, fun heq => ?_⟩
  · have := hw0 s
    simp only [w, Pi.sub_apply] at this
    linarith
  · have hpos : 0 < w s0 := by
      rw [hw s0]
      have : 0 ≤ (M.Q g *ᵥ w) s0 :=
        Finset.sum_nonneg fun j _ => mul_nonneg ((bQ_mk M g).1 s0 j) (hw0 j)
      have := hβ s0 hs0
      nlinarith
    have : w s0 = 0 := by simp [w, heq]
    linarith

theorem theorem_4c_core (M : Model St Act) (f : St → Act) :
    (∀ s, f s ∈ M.gainBiasEqualSet f s) ∧
      ((∀ s, M.gainBiasImprovementSet f s = ∅) → (∀ s, M.gainBiasEqualSet f s = {f s}) →
        M.IsOptimal (Policy.stationary f)) := by
  refine ⟨bE_self M f, fun hG hE => ?_⟩
  have hneg : ∀ s a, a ≠ f s → ∀ᶠ β in 𝓝[<] (1 : ℝ), bδ M β f s a < 0 := by
    intro s a ha
    obtain ⟨K, hK, hD⟩ := b_delta M f s a
    apply bneg_eventually hK hD
    apply b_notGE
    · rw [hG s]; exact Set.notMem_empty a
    · rw [hE s]; intro h; exact ha (Set.mem_singleton_iff.1 h)
  have hall : ∀ᶠ β in 𝓝[<] (1 : ℝ), ∀ s a, a ≠ f s → bδ M β f s a < 0 := by
    refine Filter.eventually_all.2 fun s => Filter.eventually_all.2 fun a => ?_
    by_cases ha : a = f s
    · exact Eventually.of_forall fun _ h => absurd ha h
    · filter_upwards [hneg s a ha] with β h _ using h
  obtain ⟨β₀, hβ₀, H⟩ := bex_of_ev (hall.and (bev (show (0 : ℝ) < 1 by norm_num)))
  refine ⟨β₀, hβ₀, fun β h1 h2 => ?_⟩
  obtain ⟨hδ, h0, h1'⟩ := H β h1 h2
  apply (bw_thm3 M β h0.le h1' f).1
  intro s
  refine Set.eq_empty_iff_forall_notMem.2 fun a ha => ?_
  have ha' : M.i s a + β * M.pDot s a (M.V β (Policy.stationary f)) >
      M.V β (Policy.stationary f) s := ha
  have hpos : 0 < bδ M β f s a := by simp only [bδ]; linarith
  by_cases haf : a = f s
  · rw [haf, bδ_self M f β h0.le h1'] at hpos; exact lt_irrefl _ hpos
  · linarith [hδ s a haf]

theorem theorem_4d_core (M : Model St Act) (f : St → Act)
    (hG : ∀ s, M.gainBiasImprovementSet f s = ∅)
    (hE : ∀ g : St → Act, (∀ s, g s ∈ M.gainBiasEqualSet f s) →
      M.Qstar g * M.Qstar f = M.Qstar g) :
    M.IsNearlyOptimal (Policy.stationary f) := by
  classical
  apply bnear_of
  intro h ε hε
  let g : St → Act := fun s => if h s ∈ M.gainBiasEqualSet f s then h s else f s
  have hgE : ∀ s, g s ∈ M.gainBiasEqualSet f s := by
    intro s
    by_cases hs : h s ∈ M.gainBiasEqualSet f s
    · simp only [g, if_pos hs]; exact hs
    · simp only [g, if_neg hs]; exact bE_self M f s
  obtain ⟨hx, hy⟩ := lemma_2_core M f g hgE
  have hy' := hy (hE g hgE)
  obtain ⟨K, hK, hL2⟩ := b_laurent2 M f g
  have hneg : ∀ s, ∀ᶠ β in 𝓝[<] (1 : ℝ), bδ M β g s (h s) ≤ 0 := by
    intro s
    by_cases hs : h s ∈ M.gainBiasEqualSet f s
    · have hgs : g s = h s := by simp only [g, if_pos hs]
      filter_upwards [bev (show (0 : ℝ) < 1 by norm_num)] with β ⟨h0, h1⟩
      rw [← hgs, bδ_self M g β h0.le h1]
    · obtain ⟨K', hK', hD⟩ := b_delta M g s (h s)
      have hAB : bA M g s (h s) < 0 ∨ (bA M g s (h s) = 0 ∧ bB M g s (h s) < 0) := by
        have := b_notGE M f s (h s) (by rw [hG s]; exact Set.notMem_empty _) hs
        simpa only [bA, bB, hx, hy'] using this
      filter_upwards [bneg_eventually hK' hD hAB] with β hβ using hβ.le
  filter_upwards [Filter.eventually_all.2 hneg, bev (show (0 : ℝ) < 1 by norm_num),
    bsmallK hK hε] with β hδ ⟨h0, h1⟩ hsm
  intro s
  have hw := bdiff M g h β h0.le h1
  have hwle := bmk_upper (bQ_mk M h) h0.le h1 hw (K := 0) hδ s
  rw [zero_div] at hwle
  simp only [Pi.sub_apply] at hwle
  have := hL2 β h0.le h1 s
  rw [hx, hy', sub_self, sub_self, zero_mul, add_zero, sub_zero] at this
  have := (abs_le.1 this).2
  linarith

lemma blex2 {X Y K : ℝ} (hK : 0 ≤ K)
    (h : ∀ ε > 0, ∃ᶠ β in 𝓝[<] (1 : ℝ), X * (1 - β)⁻¹ + Y ≤ ε * (1 - β)⁻¹ + K * (1 - β)) :
    X ≤ 0 := by
  by_contra hX
  push Not at hX
  have hg := binv_tendsto.const_mul_atTop (show 0 < X / 2 by linarith)
  obtain ⟨β, h1, ⟨h0, h2⟩, h3⟩ := ((h (X / 2) (by linarith)).and_eventually
    ((bev (show (0 : ℝ) < 1 by norm_num)).and (tendsto_atTop.1 hg (|Y| + K + 2)))).exists
  have : K * (1 - β) ≤ K := by nlinarith
  have := neg_abs_le Y
  have e : X * (1 - β)⁻¹ = X / 2 * (1 - β)⁻¹ + X / 2 * (1 - β)⁻¹ := by ring
  linarith

theorem theorem_4e_core (M : Model St Act) (f₀ : St → Act)
    (hG : ∀ s, M.gainBiasImprovementSet f₀ s = ∅) :
    (∀ g : St → Act, M.x g ≤ M.x f₀) ∧
      ∃ fstar : St → Act, M.x fstar = M.x f₀ ∧
        (∀ g : St → Act, M.x g = M.x f₀ → M.y g ≤ M.y fstar) ∧
        ∀ g : St → Act,
          (M.IsNearlyOptimal (Policy.stationary g) ↔ M.x g = M.x fstar ∧ M.y g = M.y fstar) := by
  have part1 : ∀ g, M.x g ≤ M.x f₀ := by
    intro g s
    obtain ⟨K, hK, hL2⟩ := b_laurent2 M f₀ g
    have hsmall : ∀ ε > 0, ∀ᶠ β in 𝓝[<] (1 : ℝ), ∀ t, bδ M β f₀ t (g t) ≤ ε :=
      fun ε hε => Filter.eventually_all.2 fun t => by
        obtain ⟨K', hK', hD⟩ := b_delta M f₀ t (g t)
        exact bsmall_eventually hK' hD
          (b_notG M f₀ t (g t) (by rw [hG t]; exact Set.notMem_empty _)) hε
    have := blex2 (X := M.x g s - M.x f₀ s) (Y := M.y g s - M.y f₀ s) hK (fun ε hε => by
      refine Eventually.frequently ?_
      filter_upwards [hsmall ε hε, bev (show (0 : ℝ) < 1 by norm_num)] with β hδ ⟨h0, h1⟩
      have hw := bdiff M f₀ g β h0.le h1
      have hwle := bmk_upper (bQ_mk M g) h0.le h1 hw hδ s
      simp only [Pi.sub_apply] at hwle
      have := (abs_le.1 (hL2 β h0.le h1 s)).1
      rw [div_eq_mul_inv] at hwle
      linarith)
    linarith
  obtain ⟨fs, hfs⟩ := bw_frequently M
  have LEX : ∀ h s, M.x h s ≤ M.x fs s ∧ (M.x h s = M.x fs s → M.y h s ≤ M.y fs s) := by
    intro h s
    obtain ⟨K, hK, hL2⟩ := b_laurent2 M fs h
    have hb := blex (X := M.x h s - M.x fs s) (Y := M.y h s - M.y fs s) hK (fun ε hε => by
      have hfr := bfreq_of (p := fun β => 0 ≤ β ∧ M.IsBetaOptimal β (Policy.stationary fs))
        (fun β₀ hβ₀ => by
          obtain ⟨β, h1, h2, h3⟩ := hfs (max β₀ 0) (max_lt hβ₀ one_pos)
          exact ⟨β, lt_of_le_of_lt (le_max_left _ _) h1, h2,
            le_trans (le_max_right _ _) h1.le, h3⟩)
      refine (hfr.and_eventually (bev (show (0 : ℝ) < 1 by norm_num))).mono ?_
      rintro β ⟨⟨h0, hopt⟩, -, h1⟩
      have := hopt (Policy.stationary h) s
      have := (abs_le.1 (hL2 β h0 h1 s)).1
      have : 0 ≤ K * (1 - β) := mul_nonneg hK (by linarith)
      linarith)
    refine ⟨by linarith [hb.1], fun he => ?_⟩
    have := hb.2 (by rw [he]; ring)
    linarith
  have hxfs : M.x fs = M.x f₀ := funext fun s => le_antisymm (part1 fs s) (LEX f₀ s).1
  have nearopt : ∀ g, M.x g = M.x fs → M.y g = M.y fs →
      M.IsNearlyOptimal (Policy.stationary g) := by
    intro g hxg hyg
    apply bnear_of
    intro h' ε hε
    refine Filter.eventually_all.2 fun s => ?_
    obtain ⟨K, hK, hL2⟩ := b_laurent2 M g h'
    have hD : ∀ β, 0 ≤ β → β < 1 →
        |(M.V β (Policy.stationary h') s - M.V β (Policy.stationary g) s) -
          ((M.x h' s - M.x g s) * (β / (1 - β)) + ((M.x h' s - M.x g s) + (M.y h' s - M.y g s)))|
          ≤ K * (1 - β) := by
      intro β h0 h1
      have e : (M.x h' s - M.x g s) * (β / (1 - β)) + ((M.x h' s - M.x g s) + (M.y h' s - M.y g s))
          = (M.x h' s - M.x g s) * (1 - β)⁻¹ + (M.y h' s - M.y g s) := by
        have : (1 - β) ≠ 0 := by linarith
        field_simp
        ring
      rw [e]; exact hL2 β h0 h1 s
    have hAB : (M.x h' s - M.x g s) < 0 ∨ ((M.x h' s - M.x g s) = 0 ∧
        (M.x h' s - M.x g s) + (M.y h' s - M.y g s) ≤ 0) := by
      have l := LEX h' s
      rw [← hxg, ← hyg] at l
      rcases lt_or_eq_of_le l.1 with hl | he
      · left; linarith
      · right; have := l.2 he; constructor <;> linarith
    filter_upwards [bsmall_eventually hK hD hAB hε] with β hβ
    linarith
  refine ⟨part1, fs, hxfs, fun g hg => fun s => (LEX g s).2 ?_, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · rw [congrFun hg s, congrFun hxfs s]
  · have hxy : ∀ s, M.x g s = M.x fs s ∧ M.y g s = M.y fs s := by
      intro s
      obtain ⟨K, hK, hL2⟩ := b_laurent2 M g fs
      have hb := blex (X := M.x fs s - M.x g s) (Y := M.y fs s - M.y g s) hK (fun ε hε => by
        refine Eventually.frequently ?_
        filter_upwards [bnear_to M g hg (Policy.stationary fs) hε,
          bev (show (0 : ℝ) < 1 by norm_num)] with β hv ⟨h0, h1⟩
        have := hv s
        have := (abs_le.1 (hL2 β h0.le h1 s)).1
        linarith)
      have l := LEX g s
      have hx : M.x g s = M.x fs s := le_antisymm l.1 (by linarith [hb.1])
      refine ⟨hx, le_antisymm (l.2 hx) ?_⟩
      have := hb.2 (by rw [hx]; ring)
      linarith
    exact ⟨funext fun s => (hxy s).1, funext fun s => (hxy s).2⟩
  · rintro ⟨h1, h2⟩
    exact nearopt g h1 h2

end Theorems

end BlackwellDiscreteDP.NearOne

open BlackwellDiscreteDP.NearOne


theorem solution {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f g : St → Act) (hG : ∃ s, g s ∈ M.gainBiasImprovementSet f s)
    (hfix : ∀ s, g s ∉ M.gainBiasImprovementSet f s → g s = f s) :
    ∃ β₀ < (1 : ℝ), ∀ β : ℝ, β₀ < β → β < 1 →
      VecGt (M.V β (Policy.stationary g)) (M.V β (Policy.stationary f)) := by
  exact theorem_4b_core M f g hG hfix
