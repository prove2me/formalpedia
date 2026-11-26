-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.primitive_fluid_limits_ae
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:42:37.541102+00:00
-- url     : https://prove2.me/submissions/31f66ab8-c551-4583-89a2-efa126066e06

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_renewal_fluid_path

open BellWilliams2001.ThresholdPolicy
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

private theorem partialSum_index (f : ℕ → ℝ) (m : ℕ) :
    partialSum f m = ∑ j ∈ Finset.range m, f (j + 1) := by
  have he : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  simp only [partialSum, he, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel,
    Nat.add_comm 1]

private theorem one_primitive_fluid {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : ℕ → Ω → ℝ) (hInt : Integrable (f 1) P) (hMean : ∫ ω, f 1 ω ∂P = 1)
    (hInd : iIndepFun (fun j => f (j + 1)) P)
    (hIdent : ∀ j, 1 ≤ j → IdentDistrib (f j) (f 1) P P)
    (hpos : ∀ j ω, 1 ≤ j → 0 < f j ω)
    (hUnbounded : ∀ ω, Tendsto (fun j => partialSum (fun i => f i ω) j) atTop atTop)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (rate : ℕ → ℝ) (hrate : ∀ n, 0 < rate n) (a : ℝ) (ha : 0 < a)
    (hlim : Tendsto rate atTop (𝓝 a)) :
    ∀ᵐ ω ∂P, ∀ H : ℝ, 0 ≤ H → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ t ∈ Icc 0 H,
      |((renewalCount (partialSum (fun i => f i ω / rate n)) (R n * t)).toNat : ℝ) / R n
        - a * t| < ε := by
  have hLaw := strong_law_ae_real (fun j => f (j + 1)) hInt
    (fun _ _ hij => hInd.indepFun hij) (fun j => hIdent (j+1) (by omega))
  rw [hMean] at hLaw
  filter_upwards [hLaw] with ω hω
  let e := partialSum (fun i => f i ω)
  have he0 : e 0 = 0 := by simp [e, partialSum_index]
  have heMono : StrictMono e := strictMono_nat_of_lt_succ fun j => by
    have h := hpos (j + 1) ω (by omega)
    simpa [e, partialSum_index, Finset.sum_range_succ] using h
  have heMean : Tendsto (fun m : ℕ => e m / (m : ℝ)) atTop (𝓝 1) := by
    simpa [e, partialSum_index] using hω
  intro H hH ε hε
  let H' := (a + 1) * H
  have hH' : 0 ≤ H' := by dsimp [H']; positivity
  have hInv := renewal_fluid_path e heMono he0 (hUnbounded ω) heMean R hR H' hH'
    (ε / 3) (by positivity)
  have hrateNear := (Metric.tendsto_nhds.1 hlim) (min 1 (ε / (3 * (H + 1)))) (by positivity)
  filter_upwards [hInv, hrateNear, hR.eventually_ge_atTop 1] with n hn hnr hR1
  rw [Real.dist_eq] at hnr
  have hR0 : 0 < R n := zero_lt_one.trans_le hR1
  intro t ht
  have hrt : rate n * t ∈ Icc 0 H' := by
    refine ⟨mul_nonneg (hrate n).le ht.1, ?_⟩
    have hUp : rate n ≤ a + 1 := by linarith [(abs_lt.1 ((lt_min_iff.mp hnr).1)).2]
    exact mul_le_mul hUp ht.2 ht.1 (by positivity)
  let s := rate n * (R n * t)
  have hs : s ∈ Icc 0 (R n * H') := by
    have h : s = R n * (rate n * t) := by dsimp [s]; ring
    rw [h]
    exact ⟨mul_nonneg hR0.le hrt.1, mul_le_mul_of_nonneg_left hrt.2 hR0.le⟩
  have hCount : renewalCount (partialSum (fun i => f i ω / rate n)) (R n * t) =
      renewalCount e s := by
    unfold renewalCount
    have heq : ∀ j, partialSum (fun i => f i ω / rate n) j ≤ R n * t ↔ e j ≤ s := by
      intro j
      simp only [e, partialSum, ← Finset.sum_div, div_le_iff₀ (hrate n), s, mul_comm (R n * t)]
    simp only [heq]
  have hNear := hn s hs
  have herror : |((renewalCount e s).toNat : ℝ) / R n - rate n * t| ≤ ε / 3 := by
    have h : s / R n = rate n * t := by dsimp [s]; field_simp
    rw [← h, ← sub_div, abs_div, abs_of_pos hR0, div_le_iff₀ hR0]
    exact hNear
  have herror' : |rate n * t - a * t| ≤ ε / 3 := by
    rw [← sub_mul, abs_mul, abs_of_nonneg ht.1]
    have hδ := (lt_min_iff.mp hnr).2.le
    calc
      _ ≤ ε / (3 * (H + 1)) * (H + 1) :=
        mul_le_mul hδ (by linarith [ht.2]) ht.1 (by positivity)
      _ = _ := by field_simp
  rw [hCount]
  have hsum := abs_add_le (((renewalCount e s).toNat : ℝ) / R n - rate n * t) (rate n * t - a * t)
  have heq : ((renewalCount e s).toNat : ℝ) / R n - rate n * t + (rate n * t - a * t) =
      ((renewalCount e s).toNat : ℝ) / R n - a * t := by ring
  rw [heq] at hsum
  linarith

set_option maxHeartbeats 900000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∀ᵐ ω ∂M.P, ∀ H : ℝ, 0 ≤ H → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ t ∈ Icc 0 H,
        (∀ k, |M.Abar n ω t k - M.lam k * t| < ε) ∧
        (∀ j, |M.Sbar n ω t j - M.mu j * t| < ε) := by
  letI : IsProbabilityMeasure M.P := M.isProb
  have hR : Tendsto (fun n => M.r n ^ 2) atTop atTop := (tendsto_pow_atTop (by norm_num)).comp M.r_tendsto
  have ha (k : Fin 2) := one_primitive_fluid (M.uC k) ((M.uC_memLp k).integrable (by norm_num))
    (M.uC_mean k) (M.indep.precomp (g := fun j => Sum.inl (k, j)) (by
      intro i j h; exact congrArg Prod.snd (Sum.inl.inj h)))
    (M.uC_ident k) (M.uC_pos k) (M.uC_finite k) _ hR
    (fun n => M.lamR n k) (fun n => M.lamR_pos n k) (M.lam k) (M.lam_pos k) (M.a31_iii k)
  have hs (j : Fin 3) := one_primitive_fluid (M.vC j) ((M.vC_memLp j).integrable (by norm_num))
    (M.vC_mean j) (M.indep.precomp (g := fun i => Sum.inr (j, i)) (by
      intro i k h; exact congrArg Prod.snd (Sum.inr.inj h)))
    (M.vC_ident j) (M.vC_pos j) (M.vC_finite j) _ hR
    (fun n => M.muR n j) (fun n => M.muR_pos n j) (M.mu j) (M.mu_pos j) (M.a31_iv j)
  filter_upwards [ae_all_iff.2 ha, ae_all_iff.2 hs] with ω hA hS H hH ε hε
  have h1 := Filter.eventually_all.2 (fun k => hA k H hH ε hε)
  have h2 := Filter.eventually_all.2 (fun j => hS j H hH ε hε)
  filter_upwards [h1,h2] with n hn1 hn2 t ht
  exact ⟨fun k => hn1 k t ht, fun j => hn2 j t ht⟩
