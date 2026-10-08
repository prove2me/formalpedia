-- Prove2me | solution 1 for BurkholderDFI.ConvexPhi.eq_14_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:05:34.065981+00:00
-- url     : https://prove2.me/submissions/a7a0bbae-e6a4-4c70-a82a-225c71144855

import Mathlib
import Definitions.Def_BurkholderDFI_ConvexPhi_Davis

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.ConvexPhi

open BurkholderDFI.SquareFnLp

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}

lemma dseq_sm (hf : Martingale f ℱ P) (k : ℕ) : StronglyMeasurable[ℱ k] (dseq f k) := by
  unfold dseq
  split_ifs with h0 h1
  · exact stronglyMeasurable_const
  · subst h1; exact hf.stronglyMeasurable 1
  · exact (hf.stronglyMeasurable k).sub
      ((hf.stronglyMeasurable (k - 1)).mono (ℱ.mono (Nat.sub_le k 1)))

lemma dseq_int (hf : Martingale f ℱ P) (k : ℕ) : Integrable (dseq f k) P := by
  unfold dseq
  split_ifs with h0 h1
  · exact integrable_const 0
  · exact hf.integrable 1
  · exact (hf.integrable k).sub (hf.integrable (k - 1))

lemma maxFnN_meas (hf : Martingale f ℱ P) (n : ℕ) :
    Measurable[ℱ n] (maxFnN (dseq f) n) := by
  unfold maxFnN
  apply Measurable.iSup
  intro j
  apply Measurable.iSup
  intro hj
  have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
  exact ENNReal.measurable_ofReal.comp
    (measurable_abs.comp ((dseq_sm hf j).measurable.mono (ℱ.mono hjn) le_rfl))

lemma maxFnN_le_sum (n : ℕ) (ω : Ω) :
    maxFnN (dseq f) n ω ≤ ∑ j ∈ Finset.Icc 1 n, ENNReal.ofReal |dseq f j ω| := by
  unfold maxFnN
  refine iSup₂_le (fun j hj => ?_)
  exact Finset.single_le_sum (f := fun j => ENNReal.ofReal |dseq f j ω|)
    (fun _ _ => zero_le) hj

lemma maxFnN_ne_top (n : ℕ) (ω : Ω) : maxFnN (dseq f) n ω ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (maxFnN_le_sum n ω)
  exact (ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.ofReal_lt_top)).ne

lemma maxFnN_toReal_le (n : ℕ) (ω : Ω) :
    (maxFnN (dseq f) n ω).toReal ≤ ∑ j ∈ Finset.Icc 1 n, |dseq f j ω| := by
  have h := ENNReal.toReal_mono
    (ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.ofReal_lt_top)).ne (maxFnN_le_sum (f := f) n ω)
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ENNReal.toReal_ofReal (abs_nonneg _)]

/-- `M_k = (d*_{k-1}).toReal`. -/
noncomputable def davM (f : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  (maxFnN (dseq f) (k - 1) ω).toReal

lemma davM_nonneg (k : ℕ) (ω : Ω) : 0 ≤ davM f k ω := ENNReal.toReal_nonneg

lemma davM_sm (hf : Martingale f ℱ P) (k : ℕ) : StronglyMeasurable[ℱ (k - 1)] (davM f k) :=
  (ENNReal.measurable_toReal.comp (maxFnN_meas hf (k - 1))).stronglyMeasurable

lemma davM_int (hf : Martingale f ℱ P) (k : ℕ) : Integrable (davM f k) P := by
  refine Integrable.mono' (g := fun ω => ∑ j ∈ Finset.Icc 1 (k - 1), |dseq f j ω|)
    (integrable_finsetSum _ (fun j _ => (dseq_int hf j).abs))
    ((davM_sm hf k).mono (ℱ.le _)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (davM_nonneg k ω)]
  exact maxFnN_toReal_le (k - 1) ω

lemma davisY_sm (hf : Martingale f ℱ P) (k : ℕ) : StronglyMeasurable[ℱ k] (davisY f k) := by
  unfold davisY
  refine Measurable.stronglyMeasurable ?_
  refine Measurable.ite ?_ (dseq_sm hf k).measurable measurable_const
  refine measurableSet_le (measurable_abs.comp (dseq_sm hf k).measurable) ?_
  exact ((davM_sm hf k).measurable.mono (ℱ.mono (Nat.sub_le k 1)) le_rfl).const_mul 2

lemma davisZ_sm (hf : Martingale f ℱ P) (k : ℕ) : StronglyMeasurable[ℱ k] (davisZ f k) := by
  unfold davisZ
  refine Measurable.stronglyMeasurable ?_
  refine Measurable.ite ?_ (dseq_sm hf k).measurable measurable_const
  refine measurableSet_lt ?_ (measurable_abs.comp (dseq_sm hf k).measurable)
  exact ((davM_sm hf k).measurable.mono (ℱ.mono (Nat.sub_le k 1)) le_rfl).const_mul 2

lemma abs_davisY_le_dseq (k : ℕ) (ω : Ω) : |davisY f k ω| ≤ |dseq f k ω| := by
  unfold davisY
  split_ifs
  · exact le_rfl
  · simp

lemma abs_davisZ_le_dseq (k : ℕ) (ω : Ω) : |davisZ f k ω| ≤ |dseq f k ω| := by
  unfold davisZ
  split_ifs
  · exact le_rfl
  · simp

lemma abs_davisY_le_M (k : ℕ) (ω : Ω) : |davisY f k ω| ≤ 2 * davM f k ω := by
  unfold davisY davM
  split_ifs with h
  · exact h
  · simp [ENNReal.toReal_nonneg]

lemma davisY_add_davisZ (k : ℕ) (ω : Ω) : davisY f k ω + davisZ f k ω = dseq f k ω := by
  unfold davisY davisZ
  by_cases h : |dseq f k ω| ≤ 2 * (maxFnN (dseq f) (k - 1) ω).toReal
  · rw [if_pos h, if_neg (not_lt.mpr h), add_zero]
  · rw [if_neg h, if_pos (not_le.mp h), zero_add]

lemma davisY_int (hf : Martingale f ℱ P) (k : ℕ) : Integrable (davisY f k) P :=
  Integrable.mono' (dseq_int hf k).abs
    ((davisY_sm hf k).mono (ℱ.le k)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs]; exact abs_davisY_le_dseq k ω))

lemma davisZ_int (hf : Martingale f ℱ P) (k : ℕ) : Integrable (davisZ f k) P :=
  Integrable.mono' (dseq_int hf k).abs
    ((davisZ_sm hf k).mono (ℱ.le k)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs]; exact abs_davisZ_le_dseq k ω))

lemma davisA_sm (hf : Martingale f ℱ P) (k : ℕ) : StronglyMeasurable[ℱ k] (davisA ℱ P f k) :=
  StronglyMeasurable.sub (f := davisY f k) (g := P[davisY f k | ℱ (k - 1)]) (davisY_sm hf k)
    (stronglyMeasurable_condExp.mono (ℱ.mono (Nat.sub_le k 1)))

lemma davisB_sm (hf : Martingale f ℱ P) (k : ℕ) : StronglyMeasurable[ℱ k] (davisB ℱ P f k) :=
  StronglyMeasurable.add (f := davisZ f k) (g := P[davisY f k | ℱ (k - 1)]) (davisZ_sm hf k)
    (stronglyMeasurable_condExp.mono (ℱ.mono (Nat.sub_le k 1)))

lemma davisA_int (hf : Martingale f ℱ P) (k : ℕ) : Integrable (davisA ℱ P f k) P :=
  (davisY_int hf k).sub integrable_condExp

lemma davisB_int (hf : Martingale f ℱ P) (k : ℕ) : Integrable (davisB ℱ P f k) P :=
  (davisZ_int hf k).add integrable_condExp

lemma davisA_add_davisB (k : ℕ) (ω : Ω) :
    davisA ℱ P f k ω + davisB ℱ P f k ω = dseq f k ω := by
  unfold davisA davisB
  rw [← davisY_add_davisZ (f := f) k ω]
  ring

lemma davisG_sm (hf : Martingale f ℱ P) (n : ℕ) : StronglyMeasurable[ℱ n] (davisG ℱ P f n) := by
  unfold davisG
  have heq : (fun ω => ∑ k ∈ Finset.Icc 1 n, davisA ℱ P f k ω)
      = ∑ k ∈ Finset.Icc 1 n, davisA ℱ P f k := by
    ext ω; simp [Finset.sum_apply]
  rw [heq]
  exact Finset.stronglyMeasurable_sum (Finset.Icc 1 n) (f := fun k => davisA ℱ P f k)
    (fun k hk => (davisA_sm hf k).mono (ℱ.mono (Finset.mem_Icc.mp hk).2))

lemma davisH_sm (hf : Martingale f ℱ P) (n : ℕ) : StronglyMeasurable[ℱ n] (davisH ℱ P f n) := by
  unfold davisH
  have heq : (fun ω => ∑ k ∈ Finset.Icc 1 n, davisB ℱ P f k ω)
      = ∑ k ∈ Finset.Icc 1 n, davisB ℱ P f k := by
    ext ω; simp [Finset.sum_apply]
  rw [heq]
  exact Finset.stronglyMeasurable_sum (Finset.Icc 1 n) (f := fun k => davisB ℱ P f k)
    (fun k hk => (davisB_sm hf k).mono (ℱ.mono (Finset.mem_Icc.mp hk).2))

lemma davisG_int (hf : Martingale f ℱ P) (n : ℕ) : Integrable (davisG ℱ P f n) P := by
  unfold davisG
  exact integrable_finsetSum _ (fun k _ => davisA_int hf k)

lemma davisH_int (hf : Martingale f ℱ P) (n : ℕ) : Integrable (davisH ℱ P f n) P := by
  unfold davisH
  exact integrable_finsetSum _ (fun k _ => davisB_int hf k)

lemma davisG_succ (n : ℕ) :
    davisG ℱ P f (n + 1) = davisG ℱ P f n + davisA ℱ P f (n + 1) := by
  ext ω
  unfold davisG
  simp only [Pi.add_apply]
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma davisH_succ (n : ℕ) :
    davisH ℱ P f (n + 1) = davisH ℱ P f n + davisB ℱ P f (n + 1) := by
  ext ω
  unfold davisH
  simp only [Pi.add_apply]
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma davisG_zero : davisG ℱ P f 0 = fun _ => 0 := by
  ext ω; unfold davisG; simp

lemma davisH_zero : davisH ℱ P f 0 = fun _ => 0 := by
  ext ω; unfold davisH; simp

/-- `E(a_{n+1} | 𝒜_n) = 0`. -/
lemma condExp_davisA (hf : Martingale f ℱ P) [IsProbabilityMeasure P] (n : ℕ) :
    P[davisA ℱ P f (n + 1) | ℱ n] =ᵐ[P] 0 := by
  have h1 : davisA ℱ P f (n + 1) = davisY f (n + 1) - P[davisY f (n + 1) | ℱ n] := by
    ext ω; unfold davisA; simp
  rw [h1]
  refine (condExp_sub (davisY_int hf (n + 1)) integrable_condExp _).trans ?_
  rw [condExp_of_stronglyMeasurable (ℱ.le n) stronglyMeasurable_condExp integrable_condExp]
  simp

/-- `E(b_{n+1} | 𝒜_n) = E(d_{n+1} | 𝒜_n)`. -/
lemma condExp_davisB (hf : Martingale f ℱ P) [IsProbabilityMeasure P] (n : ℕ) :
    P[davisB ℱ P f (n + 1) | ℱ n] =ᵐ[P] P[dseq f (n + 1) | ℱ n] := by
  have h1 : davisB ℱ P f (n + 1) = davisZ f (n + 1) + P[davisY f (n + 1) | ℱ n] := by
    ext ω; unfold davisB; simp
  have h2 : dseq f (n + 1) = davisZ f (n + 1) + davisY f (n + 1) := by
    ext ω; simp only [Pi.add_apply]; rw [← davisY_add_davisZ (f := f) (n + 1) ω, add_comm]
  rw [h1, h2]
  refine (condExp_add (davisZ_int hf (n + 1)) integrable_condExp _).trans ?_
  refine Filter.EventuallyEq.trans ?_ (condExp_add (davisZ_int hf (n + 1)) (davisY_int hf (n + 1)) _).symm
  rw [condExp_of_stronglyMeasurable (ℱ.le n) stronglyMeasurable_condExp integrable_condExp]

lemma condExp_dseq_succ (hf : Martingale f ℱ P) [IsProbabilityMeasure P] (n : ℕ) (hn : 1 ≤ n) :
    P[dseq f (n + 1) | ℱ n] =ᵐ[P] 0 := by
  have h : dseq f (n + 1) = f (n + 1) - f n := by
    ext ω; unfold dseq; rw [if_neg (by omega), if_neg (by omega)]; rfl
  rw [h]
  refine (condExp_sub (hf.integrable (n + 1)) (hf.integrable n) _).trans ?_
  filter_upwards [hf.condExp_ae_eq (Nat.le_succ n)] with ω hω
  rw [Pi.sub_apply, hω,
    condExp_of_stronglyMeasurable (ℱ.le n) (hf.stronglyMeasurable n) (hf.integrable n)]
  simp

lemma condExp_dseq_one (hf : Martingale f ℱ P) [IsProbabilityMeasure P] :
    P[dseq f 1 | ℱ 0] =ᵐ[P] f 0 := by
  have h : dseq f 1 = f 1 := by
    ext ω; unfold dseq; simp
  rw [h]
  exact hf.condExp_ae_eq (Nat.zero_le 1)

theorem eq_14_1_core {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) :
    Martingale (fun n => if n = 0 then (fun _ => (0 : ℝ)) else davisG ℱ P f n) ℱ P ∧
    Martingale (fun n => if n = 0 then f 0 else davisH ℱ P f n) ℱ P ∧
    ∀ n, 1 ≤ n → ∀ ω, f n ω = davisG ℱ P f n ω + davisH ℱ P f n ω := by
  refine ⟨?_, ?_, ?_⟩
  · have hg : (fun n => if n = 0 then (fun _ => (0 : ℝ)) else davisG ℱ P f n) = davisG ℱ P f := by
      ext n ω
      split_ifs with h
      · subst h; rw [davisG_zero]
      · rfl
    rw [hg]
    refine martingale_nat (fun n => davisG_sm hf n) (fun n => davisG_int hf n) (fun n => ?_)
    rw [davisG_succ]
    refine Filter.EventuallyEq.trans ?_ (condExp_add (davisG_int hf n) (davisA_int hf (n + 1)) _).symm
    rw [condExp_of_stronglyMeasurable (ℱ.le n) (davisG_sm hf n) (davisG_int hf n)]
    filter_upwards [condExp_davisA hf n] with ω hω
    rw [Pi.add_apply, hω]; simp
  · refine martingale_nat (fun n => ?_) (fun n => ?_) (fun n => ?_)
    · split_ifs with h
      · subst h; exact hf.stronglyMeasurable 0
      · exact davisH_sm hf n
    · split_ifs with h
      · subst h; exact hf.integrable 0
      · exact davisH_int hf n
    · simp only [Nat.succ_ne_zero, if_false]
      rw [davisH_succ]
      refine Filter.EventuallyEq.trans ?_ (condExp_add (davisH_int hf n) (davisB_int hf (n + 1)) _).symm
      rw [condExp_of_stronglyMeasurable (ℱ.le n) (davisH_sm hf n) (davisH_int hf n)]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp only [if_true]
        rw [davisH_zero]
        filter_upwards [condExp_davisB hf 0, condExp_dseq_one hf] with ω h1 h2
        rw [Pi.add_apply, h1, h2]; simp
      · simp only [show n ≠ 0 by omega, if_false]
        filter_upwards [condExp_davisB hf n, condExp_dseq_succ hf n hn] with ω h1 h2
        rw [Pi.add_apply, h1, h2]; simp
  · intro n hn ω
    unfold davisG davisH
    rw [← Finset.sum_add_distrib]
    simp_rw [davisA_add_davisB]
    -- telescoping: Σ_{k=1}^n dseq f k = f n
    induction n with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; unfold dseq; simp
      · rw [Finset.sum_Icc_succ_top (by omega), ← ih hm]
        unfold dseq
        rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
        ring

theorem eq_14_3_core {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) :
    ∀ k, 1 ≤ k → ∀ᵐ ω ∂P,
      ENNReal.ofReal |davisA ℱ P f k ω| ≤
        4 * BurkholderDFI.SquareFnLp.maxFnN (BurkholderDFI.SquareFnLp.dseq f) (k - 1) ω := by
  intro k hk
  have hM : (2 : ℝ) • davM f k = fun ω => 2 * davM f k ω := by ext ω; simp
  have h1 : abs (P[davisY f k | ℱ (k - 1)]) ≤ᵐ[P] P[abs (davisY f k) | ℱ (k - 1)] :=
    abs_condExp_ae_le_condExp_abs _
  have h2 : P[abs (davisY f k) | ℱ (k - 1)] ≤ᵐ[P] P[fun ω => 2 * davM f k ω | ℱ (k - 1)] :=
    condExp_mono (davisY_int hf k).abs ((davM_int hf k).const_mul 2)
      (Filter.Eventually.of_forall (fun ω => abs_davisY_le_M k ω))
  have h3 : P[fun ω => 2 * davM f k ω | ℱ (k - 1)] = fun ω => 2 * davM f k ω :=
    condExp_of_stronglyMeasurable (ℱ.le _) ((davM_sm hf k).const_mul 2)
      ((davM_int hf k).const_mul 2)
  rw [h3] at h2
  filter_upwards [h1, h2] with ω hω1 hω2
  have hA : |davisA ℱ P f k ω| ≤ 4 * davM f k ω := by
    unfold davisA
    calc |davisY f k ω - (P[davisY f k | ℱ (k - 1)]) ω|
        ≤ |davisY f k ω| + |(P[davisY f k | ℱ (k - 1)]) ω| := abs_sub _ _
      _ ≤ 2 * davM f k ω + 2 * davM f k ω := by
          gcongr
          · exact abs_davisY_le_M k ω
          · exact (hω1).trans hω2
      _ = 4 * davM f k ω := by ring
  calc ENNReal.ofReal |davisA ℱ P f k ω| ≤ ENNReal.ofReal (4 * davM f k ω) :=
        ENNReal.ofReal_le_ofReal hA
    _ = 4 * maxFnN (dseq f) (k - 1) ω := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        unfold davM
        rw [ENNReal.ofReal_toReal (maxFnN_ne_top _ _)]
        norm_num

end BurkholderDFI.ConvexPhi

open BurkholderDFI.ConvexPhi


theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) :
    Martingale (fun n => if n = 0 then (fun _ => (0 : ℝ)) else davisG ℱ P f n) ℱ P ∧
    Martingale (fun n => if n = 0 then f 0 else davisH ℱ P f n) ℱ P ∧
    ∀ n, 1 ≤ n → ∀ ω, f n ω = davisG ℱ P f n ω + davisH ℱ P f n ω := by
  exact eq_14_1_core hf
