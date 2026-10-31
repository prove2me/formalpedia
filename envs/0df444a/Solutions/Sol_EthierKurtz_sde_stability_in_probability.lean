-- Prove2me | solution 1 for EthierKurtz.sde_stability_in_probability
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T19:07:40.654382+00:00
-- url     : https://prove2.me/submissions/020b4b43-d563-46f7-b209-48c1fc81963f

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_StochKolmogorov_Persist_Model
import Theorems.Thm_EthierKurtz_brownian_ito_integral_and_formula

set_option linter.all false

-- ===== ItoM1 =====

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

namespace ItoLib
open EthierKurtz

variable {Ω : Type*} {d : ℕ}

section BM
variable [MeasurableSpace Ω]

end BM

section AEC
variable {mΩ : MeasurableSpace Ω}

end AEC

section CP
variable [MeasurableSpace Ω]

end CP

section M2

variable [MeasurableSpace Ω]

end M2

section M3
variable [MeasurableSpace Ω]

theorem completedBrownianPast_mono (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (ξ : Ω → SDEState d) {s t : ℝ≥0} (hst : s ≤ t) :
    completedBrownianPast P W ξ s ≤ completedBrownianPast P W ξ t := by
  unfold completedBrownianPast
  refine sup_le_sup_right (sup_le_sup_right ?_ _) _
  refine iSup_le fun r => ?_
  have hr : r.val ≤ t := r.2.trans hst
  exact le_iSup (fun q : Set.Iic t => MeasurableSpace.comap (W q.val) inferInstance) ⟨r.val, hr⟩

end M3

section M4
variable [MeasurableSpace Ω]

end M4

section StopCoef

end StopCoef

section M5
variable [MeasurableSpace Ω]

end M5

section M5b

theorem itoStepValue_eq_sum_indicator (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    itoStepValue t n c u ω = ∑ k ∈ Finset.range (2 ^ n),
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω) u := by
  unfold itoStepValue
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Set.indicator_apply, Set.mem_Ioc]

theorem intervalIntegrable_indicator_Ioc_const (T a b C : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (fun u => (Set.Ioc a b).indicator (fun _ => C) u) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  exact (integrableOn_const (by simp)).indicator measurableSet_Ioc

theorem itoStepValue_intervalIntegrable (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    IntervalIntegrable (fun u => itoStepValue t n c u ω) volume 0 t.val := by
  have heq : (fun u => itoStepValue t n c u ω) = ∑ k ∈ Finset.range (2 ^ n), fun u =>
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω) u := by
    funext u; rw [Finset.sum_apply, itoStepValue_eq_sum_indicator]
  rw [heq]
  exact IntervalIntegrable.sum _ (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ t.2)

end M5b

section M5c
variable [MeasurableSpace Ω]

end M5c

section M6refine

end M6refine

section M6osc

/-- The dyadic time `j t / 2^N`. -/
noncomputable def dyTime (t : ℝ≥0) (N j : ℕ) : ℝ≥0 := (j : ℝ≥0) * t / (2 : ℝ≥0) ^ N

/-- Oscillation event: two dyadic times in `[0,t]` at distance at most `δ` at which `H` differs
by more than `η`. -/
def oscSet (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (δ η : ℝ) : Set Ω :=
  ⋃ p : (ℕ × ℕ) × (ℕ × ℕ), {ω | p.1.2 ≤ 2 ^ p.1.1 ∧ p.2.2 ≤ 2 ^ p.2.1 ∧
    |(dyTime t p.1.1 p.1.2 : ℝ) - dyTime t p.2.1 p.2.2| ≤ δ ∧
    η < |H (dyTime t p.1.1 p.1.2) ω - H (dyTime t p.2.1 p.2.2) ω|}

theorem dyTime_le (t : ℝ≥0) {N j : ℕ} (h : j ≤ 2 ^ N) : dyTime t N j ≤ t := by
  unfold dyTime
  rw [div_le_iff₀ (by positivity)]
  calc (j : ℝ≥0) * t ≤ (2 : ℝ≥0) ^ N * t :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h) zero_le
    _ = t * 2 ^ N := mul_comm _ _

theorem oscSet_mono (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) {δ δ' : ℝ} (hδ : δ ≤ δ') (η : ℝ) :
    oscSet H t δ η ⊆ oscSet H t δ' η := by
  intro ω hω
  obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hω
  exact Set.mem_iUnion.2 ⟨p, hp.1, hp.2.1, hp.2.2.1.trans hδ, hp.2.2.2⟩

theorem iInter_oscSet_eq_empty {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    (⋂ n : ℕ, oscSet H t ((t : ℝ) / 2 ^ n) η) = ∅ := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
  intro hall
  have huc : UniformContinuousOn (fun s => H s ω) (Set.Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hHc ω).continuousOn
  obtain ⟨δ, hδ, hδuc⟩ := Metric.uniformContinuousOn_iff.1 huc η hη
  obtain ⟨n, hn⟩ := exists_nat_gt ((t : ℝ) / δ)
  have h2n : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
  have htn : (t : ℝ) / 2 ^ n < δ := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hn
    have hnδ := mul_lt_mul_of_pos_right h2n hδ
    linarith only [hn, hnδ]
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ := Set.mem_iUnion.1 (hall n)
  have := hδuc (dyTime t p.1.1 p.1.2) ⟨zero_le, dyTime_le t hp1⟩
    (dyTime t p.2.1 p.2.2) ⟨zero_le, dyTime_le t hp2⟩
    (by rw [NNReal.dist_eq]; exact lt_of_le_of_lt hp3 htn)
  rw [Real.dist_eq] at this
  exact absurd hp4 (not_lt.2 this.le)

end M6osc

section M6cauchy
variable [MeasurableSpace Ω]

end M6cauchy

section M6limit
variable [MeasurableSpace Ω]

end M6limit

section M6trunc

/-- Every `u ∈ (0,t]` lies in a cell `(t_k, t_{k+1}]` of the dyadic grid, where the step process
takes the value `c k`. -/
theorem itoStepValue_eq_cell (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) {u : ℝ}
    (hu : u ∈ Set.Ioc 0 t.val) (ω : Ω) :
    ∃ k : ℕ, k < 2 ^ n ∧ (k : ℝ) * t.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n ∧
      itoStepValue t n c u ω = c k ω := by
  have ht : (0 : ℝ) < t.val := lt_of_lt_of_le hu.1 hu.2
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hx0 : 0 < u * 2 ^ n / t.val := by have := hu.1; positivity
  have hxle : u * 2 ^ n / t.val ≤ 2 ^ n := by
    rw [div_le_iff₀ ht, mul_comm (2 ^ n : ℝ)]; exact mul_le_mul_of_nonneg_right hu.2 h2.le
  have hc1 : 0 < ⌈u * 2 ^ n / t.val⌉₊ := Nat.ceil_pos.2 hx0
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = ⌈u * 2 ^ n / t.val⌉₊ := ⟨⌈u * 2 ^ n / t.val⌉₊ - 1, by omega⟩
  have hkR : (k : ℝ) + 1 = ⌈u * 2 ^ n / t.val⌉₊ := by exact_mod_cast hk
  have hlt : (k : ℝ) < u * 2 ^ n / t.val := by
    have := Nat.ceil_lt_add_one hx0.le; linarith only [this, hkR]
  have hge : u * 2 ^ n / t.val ≤ (k : ℝ) + 1 := by rw [hkR]; exact Nat.le_ceil _
  have hk2 : k < 2 ^ n := by
    have : ⌈u * 2 ^ n / t.val⌉₊ ≤ 2 ^ n := Nat.ceil_le.2 (by exact_mod_cast hxle)
    omega
  have hlo : (k : ℝ) * t.val / 2 ^ n < u := by
    rw [div_lt_iff₀ h2]; rw [lt_div_iff₀ ht] at hlt; linarith only [hlt]
  have hhi : u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n := by
    rw [le_div_iff₀ h2]; rw [div_le_iff₀ ht] at hge; linarith only [hge]
  refine ⟨k, hk2, hlo, hhi, ?_⟩
  unfold itoStepValue
  rw [Finset.sum_eq_single k]
  · rw [if_pos ⟨hlo, hhi⟩]
  · intro l _ hlk
    rw [if_neg]
    rintro ⟨h1, h1'⟩
    rcases lt_or_gt_of_ne hlk with hl | hl
    · have hl' : (l : ℝ) + 1 ≤ k := by exact_mod_cast hl
      have : ((l : ℝ) + 1) * t.val / 2 ^ n ≤ (k : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      linarith only [h1', this, hlo]
    · have hl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hl
      have : ((k : ℝ) + 1) * t.val / 2 ^ n ≤ (l : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      linarith only [h1, this, hhi]
  · intro hk'; exact absurd (Finset.mem_range.2 hk2) hk'

/-- Off the oscillation event of mesh `t/2^n`, `H` at the left grid point `t_k` is within `η` of
`H u` for every `u ∈ [t_k, t_{k+1}]` (dyadic approximation of `u` from the left + continuity). -/
theorem abs_H_sub_le_of_not_mem_oscSet {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) (n k : ℕ) {η : ℝ} (hη : 0 ≤ η) {ω : Ω}
    (hω : ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η) (hk : k < 2 ^ n) {u : ℝ} (hu0 : 0 ≤ u)
    (hlo : (k : ℝ) * t.val / 2 ^ n ≤ u) (hhi : u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n)
    (hut : u ≤ t.val) :
    |H (dyTime t n k) ω - H u.toNNReal ω| ≤ η := by
  have ht : (0 : ℝ) ≤ t.val := t.2
  rcases ht.eq_or_lt with h0 | hpos
  · have hu : u = 0 := le_antisymm (h0 ▸ hut) hu0
    have hd : dyTime t n k = 0 := by
      have : t = 0 := NNReal.coe_eq_zero.1 h0.symm
      simp [dyTime, this]
    rw [hu, hd, Real.toNNReal_zero, sub_self, abs_zero]
    exact hη
  set y : ℕ → ℝ := fun m => u * 2 ^ (m + n) / t.val with hy
  set s : ℕ → ℝ≥0 := fun m => dyTime t (m + n) ⌊y m⌋₊ with hs
  have hsR : ∀ m, (s m : ℝ) = (⌊y m⌋₊ : ℝ) * t.val / 2 ^ (m + n) := fun m => by
    simp [hs, dyTime]
  have hy0 : ∀ m, 0 ≤ y m := fun m => by simp only [hy]; positivity
  have hyt : ∀ m, y m * t.val / 2 ^ (m + n) = u := fun m => by
    simp only [hy]; field_simp
  have hs_le : ∀ m, (s m : ℝ) ≤ u := fun m => by
    rw [hsR, ← hyt m]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.floor_le (hy0 m)) ht)
      (by positivity)
  have hs_gt : ∀ m, u - t.val / 2 ^ (m + n) ≤ (s m : ℝ) := fun m => by
    have h1 := Nat.lt_floor_add_one (y m)
    have h3 : u - t.val / 2 ^ (m + n) = (y m - 1) * t.val / 2 ^ (m + n) := by
      rw [← hyt m]; field_simp; try ring
    rw [hsR, h3]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [h1]) ht)
      (by positivity)
  have hs_ge : ∀ m, (dyTime t n k : ℝ) ≤ (s m : ℝ) := fun m => by
    have hkm : ((k * 2 ^ m : ℕ) : ℝ) ≤ y m := by
      push_cast
      simp only [hy]
      rw [le_div_iff₀ hpos, pow_add]
      rw [div_le_iff₀ (by positivity)] at hlo
      have h2m := mul_le_mul_of_nonneg_left hlo (pow_pos (two_pos (α := ℝ)) m).le
      linarith only [h2m]
    have hfl : ((k * 2 ^ m : ℕ) : ℝ) ≤ (⌊y m⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor hkm
    have e : (dyTime t n k : ℝ) = ((k * 2 ^ m : ℕ) : ℝ) * t.val / 2 ^ (m + n) := by
      simp only [dyTime]; push_cast; rw [pow_add]; field_simp; try rfl
    rw [e, hsR]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hfl ht) (by positivity)
  have hdk : (dyTime t n k : ℝ) = (k : ℝ) * t.val / 2 ^ n := by simp [dyTime]
  have hbound : ∀ m, |H (dyTime t n k) ω - H (s m) ω| ≤ η := fun m => by
    by_contra hc
    refine hω (Set.mem_iUnion.2 ⟨((n, k), (m + n, ⌊y m⌋₊)), hk.le, ?_, ?_, lt_of_not_ge hc⟩)
    · refine Nat.floor_le_of_le ?_
      simp only [hy]
      rw [div_le_iff₀ hpos]; push_cast
      exact (mul_le_mul_of_nonneg_right hut (by positivity)).trans_eq (mul_comm _ _)
    · show |(dyTime t n k : ℝ) - (s m : ℝ)| ≤ (t : ℝ) / 2 ^ n
      rw [abs_sub_comm, abs_of_nonneg (by linarith only [hs_ge m])]
      have hcell : ((k : ℝ) + 1) * t.val / 2 ^ n - (k : ℝ) * t.val / 2 ^ n = t.val / 2 ^ n := by
        ring
      have hsm := hs_le m
      rw [hdk]
      show (s m : ℝ) - (k : ℝ) * t.val / 2 ^ n ≤ t.val / 2 ^ n
      linarith only [hcell, hsm, hhi]
  have hreal : Tendsto (fun m => (s m : ℝ)) atTop (𝓝 u) := by
    have hpow : Tendsto (fun m : ℕ => t.val / 2 ^ (m + n)) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ))).comp
        (tendsto_add_atTop_nat n)
      exact Tendsto.div_atTop tendsto_const_nhds h
    have hlow : Tendsto (fun m : ℕ => u - t.val / 2 ^ (m + n)) atTop (𝓝 u) := by
      simpa using (tendsto_const_nhds (x := u)).sub hpow
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hs_gt hs_le
  have hnn : Tendsto s atTop (𝓝 u.toNNReal) := by
    have := (continuous_real_toNNReal.tendsto u).comp hreal
    simpa [Function.comp_def] using this
  have hcont : Continuous fun x : ℝ≥0 => |H (dyTime t n k) ω - H x ω| :=
    (continuous_const.sub (hHc ω)).abs
  exact le_of_tendsto' ((hcont.tendsto u.toNNReal).comp hnn) (fun m => hbound m)

end M6trunc

section M6exist
variable [MeasurableSpace Ω]

/-- M6: every continuous process adapted to the completed Brownian past has an Ito integral
against each Brownian coordinate. -/
theorem exists_hasBrownianItoIntegral {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω) :
    ∃ J : ℝ≥0 → Ω → ℝ, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J := by
  exact (EthierKurtz.brownian_ito_integral_and_formula hW x₀).1 j H hHm hHc
end M6exist

section M7grid

end M7grid

section M7zero
variable [MeasurableSpace Ω]

end M7zero

section M7qv
variable [MeasurableSpace Ω]

end M7qv

section M7c
variable [MeasurableSpace Ω]

end M7c

section M8a
variable [MeasurableSpace Ω]

end M8a

section M8b
variable [MeasurableSpace Ω]

end M8b

section M8c
variable [MeasurableSpace Ω]

end M8c

section M8d
variable [MeasurableSpace Ω]

end M8d

section M8e
variable [MeasurableSpace Ω]

end M8e

section M8f
variable [MeasurableSpace Ω]

end M8f

section M8f2
variable [MeasurableSpace Ω]

theorem itoStepValue_integral (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    ∫ u in (0 : ℝ)..t.val, itoStepValue t n c u ω =
      (∑ k ∈ Finset.range (2 ^ n), c k ω) * ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
  have hT : (0 : ℝ) ≤ t.val := t.2
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  simp_rw [itoStepValue_eq_sum_indicator]
  rw [intervalIntegral.integral_finsetSum
    (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ hT), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 := Finset.mem_range.1 hk
  have hk' : (k : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.succ_le_of_lt hk0
  have ha : 0 ≤ (k : ℝ) * t.val / (2 : ℝ) ^ n :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg k) hT) h2.le
  have hab : (k : ℝ) * t.val / (2 : ℝ) ^ n ≤ ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hT) h2.le
  have hbT : ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n ≤ t.val := by
    rw [div_le_iff₀ h2]
    have := mul_le_mul_of_nonneg_right hk' hT
    linarith only [this]
  rw [intervalIntegral.integral_of_le hT, integral_indicator_const _ measurableSet_Ioc,
    measureReal_restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.2 (Set.Ioc_subset_Ioc ha hbT), Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  simp only [NNReal.val_eq_coe, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
  field_simp
  ring

/-- M8f: left-point Riemann sums of a pathwise continuous process converge pathwise. -/
theorem riemann_tendsto {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range (2 ^ n), H (dyTime t n k) ω) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop (𝓝 (∫ u in (0 : ℝ)..t.val, H u.toNNReal ω)) := by
  have ht : (0 : ℝ) ≤ t.val := t.2
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / (2 * (t.val + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hempty := iInter_oscSet_eq_empty hHc t hη
  have hex : ∃ n0 : ℕ, ω ∉ oscSet H t ((t : ℝ) / 2 ^ n0) η := by
    by_contra h
    push_neg at h
    have hmem : ω ∈ (⋂ n : ℕ, oscSet H t ((t : ℝ) / 2 ^ n) η) := Set.mem_iInter.2 h
    rw [hempty] at hmem
    exact hmem
  obtain ⟨n0, hn0⟩ := hex
  refine ⟨n0, fun n hn => ?_⟩
  have hω : ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η := fun h => hn0 (oscSet_mono H t
    (div_le_div_of_nonneg_left (NNReal.coe_nonneg t) (by positivity)
      (pow_le_pow_right₀ one_le_two hn)) η h)
  have hI := itoStepValue_integral t n (fun k ω => H (dyTime t n k) ω) ω
  have hHi : IntervalIntegrable (fun u : ℝ => H u.toNNReal ω) volume 0 t.val :=
    ((hHc ω).comp continuous_real_toNNReal).intervalIntegrable _ _
  rw [Real.dist_eq, ← hI, ← intervalIntegral.integral_sub
    (itoStepValue_intervalIntegrable _ _ _ _) hHi]
  have hb : ∀ u ∈ Set.uIoc (0 : ℝ) t.val,
      ‖itoStepValue t n (fun k ω => H (dyTime t n k) ω) u ω - H u.toNNReal ω‖ ≤ η := by
    intro u hu
    rw [Set.uIoc_of_le ht] at hu
    obtain ⟨k, hk, hlo, hhi, hval⟩ :=
      itoStepValue_eq_cell t n (fun k ω => H (dyTime t n k) ω) hu ω
    rw [hval, Real.norm_eq_abs]
    exact abs_H_sub_le_of_not_mem_oscSet hHc t n k hη.le hω hk hu.1.le hlo.le hhi hu.2
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg ht, Real.norm_eq_abs] at hle
  refine lt_of_le_of_lt hle ?_
  rw [hηdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  linarith only [mul_nonneg hε.le ht, hε]

end M8f2

section M8f3
variable [MeasurableSpace Ω]

end M8f3

section M8gTaylor
open Set

end M8gTaylor

section M8g
variable [MeasurableSpace Ω]

end M8g

section M8g2

end M8g2

section M8g3
variable [MeasurableSpace Ω]

end M8g3

section M8g4
variable [MeasurableSpace Ω]

/-- Coordinates of a linear functional on `SDEState d`. -/
theorem clm_coord (L : SDEState d →L[ℝ] ℝ) (v : SDEState d) :
    L v = ∑ i, v i * L (EuclideanSpace.single i 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
  simp [map_sum, map_smul, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]

theorem clm2_coord (B : SDEState d →L[ℝ] SDEState d →L[ℝ] ℝ) (v w : SDEState d) :
    B v w = ∑ i, ∑ i', v i * w i' *
      B (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1) := by
  rw [clm_coord (B v) w]
  have h : ∀ i', B v (EuclideanSpace.single i' 1) =
      ∑ i, v i * B (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1) := fun i' =>
    clm_coord (B.flip (EuclideanSpace.single i' 1)) v
  simp only [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring

end M8g4

section M8g5
variable [MeasurableSpace Ω]

/-- M8g5: **Ito's formula** for a `C²` function of a `d`-dimensional Ito process
`X^i = X^i_0 + Σ_j ∫ H^{ij} dW^j + ∫ b^i du` (continuous adapted coefficients). -/
theorem ito_formula {P : Measure Ω} [IsFiniteMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) {e : ℕ} {X : ℝ≥0 → Ω → SDEState e}
    (hXm : ∀ s, Measurable (X s)) (hXc : ∀ ω, Continuous fun s => X s ω)
    (hXa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (X s))
    {H J : Fin e → Fin d → ℝ≥0 → Ω → ℝ} {b : Fin e → ℝ≥0 → Ω → ℝ}
    (hHm : ∀ i j s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H i j s))
    (hHc : ∀ i j ω, Continuous fun s => H i j s ω)
    (hJ : ∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) (H i j) (J i j))
    (hbm : ∀ i s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (b i s))
    (hbc : ∀ i ω, Continuous fun s => b i s ω)
    (hX : ∀ᵐ ω ∂P, ∀ (s : ℝ≥0) (i : Fin e), X s ω i = X 0 ω i + (∑ j, J i j s ω) +
      ∫ u in (0 : ℝ)..s.val, b i u.toNNReal ω)
    {f : SDEState e → ℝ} (hf : ContDiff ℝ 2 f) {K : Fin e → Fin d → ℝ≥0 → Ω → ℝ}
    (hK : ∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j)
      (fun s ω => fderiv ℝ f (X s ω) (EuclideanSpace.single i 1) * H i j s ω) (K i j))
    (t : ℝ≥0) :
    ∀ᵐ ω ∂P, f (X t ω) = f (X 0 ω) + (∑ i, ∑ j, K i j t ω) +
      (∑ i, ∫ u in (0 : ℝ)..t.val,
        fderiv ℝ f (X u.toNNReal ω) (EuclideanSpace.single i 1) * b i u.toNNReal ω) +
      (1 / 2) * ∑ i, ∑ i', ∑ j, ∫ u in (0 : ℝ)..t.val,
        fderiv ℝ (fderiv ℝ f) (X u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * H i j u.toNNReal ω * H i' j u.toNNReal ω := by
  exact (EthierKurtz.brownian_ito_integral_and_formula hW x₀).2.2 e X hXm hXc hXa H J b hHm hHc hJ hbm hbc hX f hf K hK t
end M8g5

section M9a
variable [MeasurableSpace Ω]

/-- M9a: the Ito integral of a bounded continuous adapted integrand is square integrable,
with `E[J_t²] ≤ C² t` and mean zero. -/
theorem ito_integral_memLp_meanZero {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H J : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ} (hC : ∀ s ω, |H s ω| ≤ C)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J) (t : ℝ≥0) :
    MemLp (J t) 2 P ∧ ∫ ω, J t ω ^ 2 ∂P ≤ C ^ 2 * t ∧ ∫ ω, J t ω ∂P = 0 := by
  exact (EthierKurtz.brownian_ito_integral_and_formula hW x₀).2.1 j H J hHm hHc C hC hJ t
end M9a

section M9c
/-! M9c: calculus for the pathwise-uniqueness test function (line derivatives, cutoff). -/

/-- Smooth cutoff: `1` on `(-∞, r]`, `0` on `[r+1, ∞)`, values in `[0,1]`. -/
noncomputable def cutoff (r : ℝ) (x : ℝ) : ℝ := Real.smoothTransition (r + 1 - x)

theorem cutoff_contDiff (r : ℝ) {n : ℕ∞} : ContDiff ℝ n (cutoff r) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem cutoff_eq_one {r x : ℝ} (h : x ≤ r) : cutoff r x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cutoff_eq_zero {r x : ℝ} (h : r + 1 ≤ x) : cutoff r x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutoff_nonneg (r x : ℝ) : 0 ≤ cutoff r x := Real.smoothTransition.nonneg _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem line_hasDerivAt {f : E → ℝ} (hf : Differentiable ℝ f) (u v : E) (s : ℝ) :
    HasDerivAt (fun r : ℝ => f (u + r • v)) (fderiv ℝ f (u + s • v) v) s := by
  have h := (hf (u + s • v)).hasFDerivAt.comp_hasDerivAt s
    (((hasDerivAt_id s).smul_const v).const_add u)
  simpa [Function.comp_def] using h

theorem line_hasDerivAt2 {f : E → ℝ} (hf : ContDiff ℝ 2 f) (u v : E) :
    HasDerivAt (fun r : ℝ => fderiv ℝ f (u + r • v) v) (fderiv ℝ (fderiv ℝ f) u v v) 0 := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hc : ∀ w, HasFDerivAt (fun w => fderiv ℝ f w v) ((fderiv ℝ (fderiv ℝ f) w).flip v) w :=
    fun w => by simpa using (hd w).hasFDerivAt.clm_apply (hasFDerivAt_const v w)
  have h := (hc (u + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ)
    (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u)
  simpa [Function.comp_def] using h

/-- First directional derivative from an explicit line derivative. -/
theorem fderiv_eq_of_line {f : E → ℝ} (hf : Differentiable ℝ f) (u v : E) {c : ℝ}
    (h1 : HasDerivAt (fun r : ℝ => f (u + r • v)) c 0) : fderiv ℝ f u v = c := by
  have h := line_hasDerivAt hf u v 0
  simp only [zero_smul, add_zero] at h
  exact h.unique h1

/-- Second directional derivative `D²f(u)(v,v)` from explicit line derivatives. -/
theorem fderiv2_eq_of_line {f : E → ℝ} (hf : ContDiff ℝ 2 f) (u v : E) {φ' : ℝ → ℝ} {c : ℝ}
    (h1 : ∀ s, HasDerivAt (fun r : ℝ => f (u + r • v)) (φ' s) s) (h2 : HasDerivAt φ' c 0) :
    fderiv ℝ (fderiv ℝ f) u v v = c := by
  have hdf : Differentiable ℝ f := hf.differentiable two_ne_zero
  have e : (fun r : ℝ => fderiv ℝ f (u + r • v) v) = φ' :=
    funext fun s => (line_hasDerivAt hdf u v s).unique (h1 s)
  have h := line_hasDerivAt2 hf u v
  rw [e] at h
  exact h.unique h2

theorem fderiv12_congr_nhds {f g : E → ℝ} {u : E} (h : f =ᶠ[𝓝 u] g) :
    fderiv ℝ f u = fderiv ℝ g u ∧ fderiv ℝ (fderiv ℝ f) u = fderiv ℝ (fderiv ℝ g) u :=
  ⟨h.fderiv_eq, h.fderiv.fderiv_eq⟩

/-- Derivatives of a function that scales under a translation. -/
theorem fderiv12_translate {f : E → ℝ} (hf : ContDiff ℝ 2 f) (z : E) (k : ℝ)
    (hfz : ∀ w, f (w + z) = k * f w) (u : E) :
    fderiv ℝ f (u + z) = k • fderiv ℝ f u ∧
      fderiv ℝ (fderiv ℝ f) (u + z) = k • fderiv ℝ (fderiv ℝ f) u := by
  have hd : Differentiable ℝ f := hf.differentiable two_ne_zero
  have hd2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have h1 : ∀ w, fderiv ℝ f (w + z) = k • fderiv ℝ f w := fun w => by
    rw [← fderiv_comp_add_right]
    have : (fun x => f (x + z)) = fun x => k * f x := funext hfz
    rw [this, fderiv_const_mul (hd w)]
  refine ⟨h1 u, ?_⟩
  rw [← fderiv_comp_add_right]
  have : (fun x => fderiv ℝ f (x + z)) = fun x => k • fderiv ℝ f x := funext h1
  rw [this]
  exact ((hd2 u).hasFDerivAt.const_smul k).fderiv

theorem hasDerivAt_sq_affine (α β r : ℝ) :
    HasDerivAt (fun s : ℝ => (α + s * β) ^ 2) (2 * (α + r * β) * β) r := by
  have h := (((hasDerivAt_id r).mul_const β).const_add α).pow 2
  exact h.congr_deriv (by simp only [id]; ring)

end M9c

section M9cF
/-! The concrete test function on `SDEState (d + d + 1)` = (x, y, a). -/

def ixc (k : Fin d) : Fin (d + d + 1) := Fin.castSucc (Fin.castAdd d k)
def iyc (k : Fin d) : Fin (d + d + 1) := Fin.castSucc (Fin.natAdd d k)
def iac : Fin (d + d + 1) := Fin.last _

/-- `Q(u) = |x - y|²`. -/
noncomputable def Qf (u : SDEState (d + d + 1)) : ℝ := ∑ k, (u (ixc k) - u (iyc k)) ^ 2
theorem coord_contDiff {e : ℕ} (i : Fin e) {n : ℕ∞} :
    ContDiff ℝ n (fun u : SDEState e => u i) :=
  (EuclideanSpace.proj i : SDEState e →L[ℝ] ℝ).contDiff

theorem Qf_contDiff {n : ℕ∞} : ContDiff ℝ n (Qf (d := d)) := by
  unfold Qf
  exact ContDiff.sum fun k _ => ((coord_contDiff _).sub (coord_contDiff _)).pow 2

end M9cF

section M9c2
/-! Packing `(x, y, a)` into `SDEState (d + d + 1)` and the structure of `Ff`. -/

/-- `(x, y, a) ↦ u` with `u (ixc k) = x k`, `u (iyc k) = y k`, `u iac = a`. -/
noncomputable def pack (x y : SDEState d) (a : ℝ) : SDEState (d + d + 1) :=
  WithLp.toLp 2 (fun i => Fin.lastCases a (fun j => Fin.addCases (fun k => x k) (fun k => y k) j) i)

@[simp] theorem pack_ixc (x y : SDEState d) (a : ℝ) (k : Fin d) : pack x y a (ixc k) = x k := by
  simp [pack, ixc]

@[simp] theorem pack_iyc (x y : SDEState d) (a : ℝ) (k : Fin d) : pack x y a (iyc k) = y k := by
  show Fin.lastCases a (fun j => Fin.addCases (fun k => x k) (fun k => y k) j)
    (Fin.castSucc (Fin.natAdd d k)) = y k
  rw [Fin.lastCases_castSucc, Fin.addCases_right]

@[simp] theorem pack_iac (x y : SDEState d) (a : ℝ) : pack x y a iac = a := by
  simp [pack, iac]

theorem pack_ext {u w : SDEState (d + d + 1)} (hx : ∀ k, u (ixc k) = w (ixc k))
    (hy : ∀ k, u (iyc k) = w (iyc k)) (ha : u iac = w iac) : u = w := by
  refine PiLp.ext fun i => ?_
  induction i using Fin.lastCases with
  | last => exact ha
  | cast j =>
    induction j using Fin.addCases with
    | left k => exact hx k
    | right k => exact hy k

/-- The `a`-direction. -/
noncomputable def eac : SDEState (d + d + 1) := pack 0 0 1

theorem pack_add_eac (x y : SDEState d) (a c : ℝ) :
    pack x y a + c • (eac (d := d)) = pack x y (a + c) :=
  pack_ext (fun k => by simp [eac]) (fun k => by simp [eac]) (by simp [eac])

theorem Qf_pack (x y : SDEState d) (a : ℝ) : Qf (pack x y a) = ‖x - y‖ ^ 2 := by
  simp only [Qf, pack_ixc, pack_iyc, EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply]

end M9c2

section M9d
/-! The generator of `Ff` along the coupled pair (x, y, a) and its sign inside the ball. -/

/-- Column `j` of a diffusion matrix. -/
noncomputable def scol (s : SDEDiffusion d) (j : Fin d) : SDEState d :=
  WithLp.toLp 2 (fun k => s (k, j))

theorem sum_scol_sq (s s' : SDEDiffusion d) :
    ∑ j, ∑ k, (scol s j k - scol s' j k) ^ 2 = ‖s - s'‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by simp [scol]

end M9d

section M9d2
/-! Global bounds for the generator and the integrands (compact support of `Ff` in (x, y)). -/

theorem pack_continuous {α : Type*} [TopologicalSpace α] {f g : α → SDEState d} {h : α → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous fun p => pack (f p) (g p) (h p) := by
  unfold pack
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  induction i using Fin.lastCases with
  | last => simp only [Fin.lastCases_last]; exact hh
  | cast j =>
    induction j using Fin.addCases with
    | left k =>
      simp only [Fin.lastCases_castSucc, Fin.addCases_left]
      exact (continuous_apply k).comp ((PiLp.continuous_ofLp 2 _).comp hf)
    | right k =>
      simp only [Fin.lastCases_castSucc, Fin.addCases_right]
      exact (continuous_apply k).comp ((PiLp.continuous_ofLp 2 _).comp hg)

theorem scol_continuous {α : Type*} [TopologicalSpace α] {s : α → SDEDiffusion d}
    (hs : Continuous s) (j : Fin d) : Continuous fun p => scol (s p) j := by
  unfold scol
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
    (continuous_apply (k, j)).comp ((PiLp.continuous_ofLp 2 _).comp hs))

end M9d2

section M9e1
/-! Zero integral, measurability of time integrals, the exponential primitive identity, and the
pointwise generator bound with the localizing rate `kap`. -/

theorem hasBrownianItoIntegral_zero [MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : ℝ≥0 → MeasurableSpace Ω) (W : ℝ≥0 → Ω → ℝ) :
    HasBrownianItoIntegral P ℱ W (fun _ _ => 0) (fun _ _ => 0) := by
  refine ⟨fun t ω => by simp, fun t => ⟨fun _ _ _ => 0, fun _ _ _ => measurable_const,
    fun _ => ⟨0, fun _ _ _ => by simp⟩, ?_, ?_⟩⟩
  · convert (show TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) atTop fun _ => 0 from
      fun ε hε => by simp [hε.ne']) using 1
    funext n ω
    have hz : ∀ u, itoStepValue t n (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) u ω = 0 := fun u =>
      Finset.sum_eq_zero fun k _ => ite_self _
    simp [hz]
  · convert (show TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) atTop fun _ => 0 from
      fun ε hε => by simp [hε.ne']) using 1
    funext n ω; simp [itoStepSum]

theorem measurable_intervalIntegral_of_continuous [MeasurableSpace Ω] (m : MeasurableSpace Ω)
    {H : ℝ≥0 → Ω → ℝ} (t : ℝ≥0) (hHm : ∀ s, s ≤ t → Measurable[m] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω) :
    Measurable[m] (fun ω => ∫ u in (0 : ℝ)..t.val, H u.toNNReal ω) := by
  refine measurable_of_tendsto_metrizable (f := fun n ω => (∑ k ∈ Finset.range (2 ^ n), H (dyTime t n k) ω) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) (fun n => ?_)
    (tendsto_pi_nhds.2 fun ω => riemann_tendsto hHc t ω)
  refine Measurable.mul_const ?_ _
  exact Finset.measurable_sum _ fun k hk =>
    hHm _ (dyTime_le t (Finset.mem_range.1 hk).le)

/-- `∫_0^t e^{-A(u)} g(u) du = 1 - e^{-A(t)}` for `A(u) = ∫_0^u g`. -/
theorem integral_exp_neg_primitive {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    ∫ u in (0 : ℝ)..t, Real.exp (-(∫ v in (0 : ℝ)..u, g v)) * g u =
      1 - Real.exp (-(∫ v in (0 : ℝ)..t, g v)) := by
  have h1 : ∀ u, HasDerivAt (fun u => ∫ v in (0 : ℝ)..u, g v) (g u) u := fun u =>
    (hg.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hd : ∀ u, HasDerivAt (fun u => -Real.exp (-(∫ v in (0 : ℝ)..u, g v)))
      (Real.exp (-(∫ v in (0 : ℝ)..u, g v)) * g u) u := by
    intro u
    have h2 := ((h1 u).neg.exp).neg
    exact h2.congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hpc : Continuous fun u => ∫ v in (0 : ℝ)..u, g v :=
    continuous_iff_continuousAt.2 fun u => (h1 u).continuousAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (((Real.continuous_exp.comp hpc.neg).mul hg).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_same, neg_zero, Real.exp_zero]
  ring

/-- Distance of `x` from the closed ball of radius `R`. -/
noncomputable def distB (R : ℝ) (x : SDEState d) : ℝ := max 0 (‖x‖ - R)

theorem distB_continuous (R : ℝ) : Continuous (distB (d := d) R) :=
  continuous_const.max (continuous_norm.sub continuous_const)

theorem distB_nonneg (R : ℝ) (x : SDEState d) : 0 ≤ distB R x := le_max_left _ _

theorem distB_eq_zero {R : ℝ} {x : SDEState d} (h : ‖x‖ ≤ R) : distB R x = 0 :=
  max_eq_left (by linarith)

end M9e1

section M9e2
/-! Ito formula for `Ff r (X, Y, A)` and pathwise uniqueness for time-homogeneous, locally
Lipschitz coefficients (no stopping times: localization through the rate `kap`). -/

end M9e2

end ItoLib

-- ===== E =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10b1
/-! M10b-1: pathwise identification of Ito integrals. For an integrand that is an indefinite
integral in time (`h s = h 0 + ∫₀ˢ D`), left-point sums converge pathwise to the integration by
parts value `h t w t - h 0 w 0 - ∫₀ᵗ w D`; and pathwise limits of left-point sums are Ito
integrals in the sense of `HasBrownianItoIntegral`. -/

end M10b1

section M10b2
/-! M10b-2 (generic part): piecewise-linear interpolation of a sequence on the grid `k h`,
defined as a primitive of the piecewise-constant slope. -/

end M10b2

section M10b2s
/-! M10b-2: the truncated Euler scheme with lagged, linearly interpolated coefficients, driven by a
deterministic path `w`. `eulerZZ k = (Z_{k-1}, Z_k)`. -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)
  (w : ℝ≥0 → SDEState d)

variable {s₁ b₁ h w}

end M10b2s

section M10b2w
/-! M10b-2 (random part): the scheme driven by a Brownian path is adapted, continuous, and an
Ito process. Measurability is proved for any monotone family `G` of σ-algebras that sees the
past of `W` (used with `G = completedBrownianPast` and with the ambient σ-algebra). -/

variable {W : ℝ≥0 → Ω → SDEState d} {G : ℝ≥0 → MeasurableSpace Ω}
  {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10b2w

section M10b2i
/-! M10b-2: the scheme driven by standard Brownian motion is an Ito process in the sense of
`ito_formula`. -/

variable [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
  {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10b2i

section M10b4a
/-! M10b-4 (a): Ito formula for `Ff r` along `(X, Y, A)` where `X`, `Y` are general Ito
processes (matrix integrands `HX`, `HY`, drifts `bX`, `bY`), `A = ∫ κ(X, Y)`. -/

theorem abs_packcol_le (σx σy : SDEDiffusion d) (j : Fin d) (i : Fin (d + d + 1)) :
    |pack (scol σx j) (scol σy j) 0 i| ≤ ‖σx‖ + ‖σy‖ := by
  have h1 := norm_nonneg σx
  have h2 := norm_nonneg σy
  induction i using Fin.lastCases with
  | last => rw [show pack (scol σx j) (scol σy j) 0 (Fin.last _) = 0 from pack_iac _ _ _]; simp; linarith
  | cast i' =>
    induction i' using Fin.addCases with
    | left k =>
      rw [show pack (scol σx j) (scol σy j) 0 (Fin.castSucc (Fin.castAdd d k)) = σx (k, j) from
        pack_ixc _ _ _ k]
      have := PiLp.norm_apply_le σx (k, j)
      rw [Real.norm_eq_abs] at this
      linarith
    | right k =>
      rw [show pack (scol σx j) (scol σy j) 0 (Fin.castSucc (Fin.natAdd d k)) = σy (k, j) from
        pack_iyc _ _ _ k]
      have := PiLp.norm_apply_le σy (k, j)
      rw [Real.norm_eq_abs] at this
      linarith

end M10b4a

section M10b4b
/-! M10b-4 (b): pathwise bounds for the generator `driftG` when `X` has coefficients
`σ₀(X), b₀(X)` and `Y` has arbitrary coefficients `σy, by'`. -/

theorem abs_pack0_le (u v : SDEState d) (i : Fin (d + d + 1)) :
    |pack u v 0 i| ≤ ‖u‖ + ‖v‖ := by
  have h1 := norm_nonneg u
  have h2 := norm_nonneg v
  induction i using Fin.lastCases with
  | last => rw [show pack u v 0 (Fin.last _) = 0 from pack_iac _ _ _]; simp; linarith
  | cast i' =>
    induction i' using Fin.addCases with
    | left k =>
      rw [show pack u v 0 (Fin.castSucc (Fin.castAdd d k)) = u k from pack_ixc _ _ _ k]
      have := PiLp.norm_apply_le u k
      rw [Real.norm_eq_abs] at this
      linarith
    | right k =>
      rw [show pack u v 0 (Fin.castSucc (Fin.natAdd d k)) = v k from pack_iyc _ _ _ k]
      have := PiLp.norm_apply_le v k
      rw [Real.norm_eq_abs] at this
      linarith

/-- Expectation bound from an Ito decomposition `F = c + Z + D` with `E Z = 0`, `F ≥ 0`. -/
theorem lintegral_le_of_ito [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F Z D E : Ω → ℝ} {c β : ℝ} (hF0 : ∀ᵐ ω ∂P, 0 ≤ F ω) (hZi : Integrable Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (hEq : ∀ᵐ ω ∂P, F ω = c + Z ω + D ω)
    (hD : ∀ᵐ ω ∂P, D ω ≤ β + E ω) (hE : Integrable E P) :
    ∫⁻ ω, ENNReal.ofReal (F ω) ∂P ≤ ENNReal.ofReal (c + β + ∫ ω, E ω ∂P) := by
  have hle : ∀ᵐ ω ∂P, F ω ≤ Z ω + (c + β) + E ω := by
    filter_upwards [hEq, hD] with ω h1 h2
    rw [h1]; linarith
  have hi : Integrable (fun ω => Z ω + (c + β) + E ω) P :=
    (hZi.add (integrable_const _)).add hE
  calc _ ≤ ∫⁻ ω, ENNReal.ofReal (Z ω + (c + β) + E ω) ∂P :=
        lintegral_mono_ae (hle.mono fun ω h => ENNReal.ofReal_le_ofReal h)
    _ = ENNReal.ofReal (∫ ω, (Z ω + (c + β) + E ω) ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hi
          (by filter_upwards [hle, hF0] with ω h h0 using h0.trans h)).symm
    _ = ENNReal.ofReal (c + β + ∫ ω, E ω ∂P) := by
        have e1 : ∫ ω, (Z ω + (c + β) + E ω) ∂P = ∫ ω, (Z ω + (c + β)) ∂P + ∫ ω, E ω ∂P :=
          integral_add (hZi.add (integrable_const _)) hE
        have e2 : ∫ ω, (Z ω + (c + β)) ∂P = ∫ ω, Z ω ∂P + ∫ _ω, (c + β) ∂P :=
          integral_add hZi (integrable_const _)
        rw [e1, e2, hZ0, integral_const]
        simp

end M10b4b

end ItoLib

-- ===== F =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c1
/-! M10c-1: the saturating profile `ψ(Q) = 1 - (1 - st(Q/4)) e^{-Q}` (`ψ(0) = 0`, `ψ = 1` for
`Q ≥ 4`, `ψ(Q) ≥ Q/5` on `[0,4]`) and the test function
`Gf r (x, y, a) = e^{-a} χ_r(|x|²) ψ(|x-y|²)` (cut-off in `x` only). -/

noncomputable def psiQ (q : ℝ) : ℝ := 1 - (1 - Real.smoothTransition (q / 4)) * Real.exp (-q)

theorem psiQ_contDiff {n : ℕ∞} : ContDiff ℝ n psiQ :=
  contDiff_const.sub ((contDiff_const.sub
    (Real.smoothTransition.contDiff.comp (contDiff_id.div_const 4))).mul
    (Real.contDiff_exp.comp contDiff_id.neg))

theorem psiQ_eq_one {q : ℝ} (h : 4 ≤ q) : psiQ q = 1 := by
  unfold psiQ
  rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith)]
  simp

theorem psiQ_ge (q : ℝ) : 1 - Real.exp (-q) ≤ psiQ q := by
  unfold psiQ
  have := Real.smoothTransition.nonneg (q / 4)
  have := Real.exp_pos (-q)
  nlinarith

theorem psiQ_nonneg {q : ℝ} (h0 : 0 ≤ q) : 0 ≤ psiQ q := by
  have h1 := psiQ_ge q
  have h2 : Real.exp (-q) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  linarith

theorem psiQ_ge_lin {q : ℝ} (h0 : 0 ≤ q) (h4 : q ≤ 4) : q / 5 ≤ psiQ q := by
  have h1 := psiQ_ge q
  have h2 : Real.exp (-q) ≤ 1 / (1 + q) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp q])
  have h3 : q / 5 ≤ q / (1 + q) := div_le_div_of_nonneg_left h0 (by linarith) (by linarith)
  have h4 : q / (1 + q) = 1 - 1 / (1 + q) := by field_simp; ring
  linarith

theorem psiQ_eventually_one {q : ℝ} (h : 4 < q) : psiQ =ᶠ[𝓝 q] fun _ => (1 : ℝ) := by
  filter_upwards [lt_mem_nhds h] with x hx using psiQ_eq_one hx.le

theorem deriv_psiQ_zero {q : ℝ} (h : 4 < q) : deriv psiQ q = 0 ∧ deriv (deriv psiQ) q = 0 := by
  have e := psiQ_eventually_one h
  refine ⟨by rw [e.deriv_eq]; simp, ?_⟩
  have e2 : deriv psiQ =ᶠ[𝓝 q] fun _ => (0 : ℝ) := by
    filter_upwards [lt_mem_nhds h] with x hx
    rw [(psiQ_eventually_one hx).deriv_eq]; simp
  rw [e2.deriv_eq]; simp

theorem psiQ_differentiable : Differentiable ℝ psiQ :=
  (psiQ_contDiff (n := 1)).differentiable_one

theorem deriv_psiQ_contDiff {n : ℕ∞} : ContDiff ℝ n (deriv psiQ) :=
  ((contDiff_infty_iff_deriv.1 (psiQ_contDiff (n := ⊤))).2).of_le (by exact_mod_cast le_top)

/-- `|x|²` read off the `x`-block. -/
noncomputable def Nxf (u : SDEState (d + d + 1)) : ℝ := ∑ k, u (ixc k) ^ 2

theorem Nxf_contDiff {n : ℕ∞} : ContDiff ℝ n (Nxf (d := d)) := by
  unfold Nxf
  exact ContDiff.sum fun k _ => (coord_contDiff _).pow 2

theorem Nxf_pack (x y : SDEState d) (a : ℝ) : Nxf (pack x y a) = ‖x‖ ^ 2 := by
  simp only [Nxf, pack_ixc, EuclideanSpace.real_norm_sq_eq]

/-- Inner test function `e^{-a} ψ(|x-y|²)`. -/
noncomputable def G0f (u : SDEState (d + d + 1)) : ℝ := Real.exp (-u iac) * psiQ (Qf u)

/-- Test function `e^{-a} χ_r(|x|²) ψ(|x-y|²)`. -/
noncomputable def Gf (r : ℝ) (u : SDEState (d + d + 1)) : ℝ :=
  Real.exp (-u iac) * (cutoff r (Nxf u) * psiQ (Qf u))

theorem G0f_contDiff {n : ℕ∞} : ContDiff ℝ n (G0f (d := d)) :=
  (Real.contDiff_exp.comp (coord_contDiff _).neg).mul (psiQ_contDiff.comp Qf_contDiff)

theorem Gf_contDiff (r : ℝ) {n : ℕ∞} : ContDiff ℝ n (Gf (d := d) r) :=
  (Real.contDiff_exp.comp (coord_contDiff _).neg).mul
    (((cutoff_contDiff r).comp Nxf_contDiff).mul (psiQ_contDiff.comp Qf_contDiff))

theorem Gf_eq_G0f_nhds {r : ℝ} {u : SDEState (d + d + 1)} (hu : Nxf u < r) :
    Gf r =ᶠ[𝓝 u] G0f := by
  have hc : ContinuousAt (Nxf (d := d)) u := (Nxf_contDiff (n := 0)).continuous.continuousAt
  filter_upwards [hc.eventually (gt_mem_nhds hu)] with w hw
  simp only [Gf, G0f, cutoff_eq_one hw.le, one_mul]

theorem Gf_zero_nhds {r : ℝ} {u : SDEState (d + d + 1)} (hu : r + 1 < Nxf u) :
    Gf r =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
  have hc : ContinuousAt (Nxf (d := d)) u := (Nxf_contDiff (n := 0)).continuous.continuousAt
  filter_upwards [hc.eventually (lt_mem_nhds hu)] with w hw
  simp only [Gf, cutoff_eq_zero hw.le, zero_mul, mul_zero]

theorem Gf_fderiv_zero {r : ℝ} {u : SDEState (d + d + 1)} (hu : r + 1 < Nxf u) :
    fderiv ℝ (Gf r) u = 0 ∧ fderiv ℝ (fderiv ℝ (Gf r)) u = 0 := by
  obtain ⟨h1, h2⟩ := fderiv12_congr_nhds (Gf_zero_nhds hu)
  refine ⟨h1.trans (fderiv_const_apply _), h2.trans ?_⟩
  rw [show (fderiv ℝ fun _ : SDEState (d + d + 1) => (0 : ℝ)) = fun _ => 0 from
    funext fun w => fderiv_const_apply _]
  exact fderiv_const_apply _

theorem Gf_translate (r c : ℝ) (w : SDEState (d + d + 1)) :
    Gf r (w + c • (eac (d := d))) = Real.exp (-c) * Gf r w := by
  have hx : ∀ k, (w + c • (eac (d := d))) (ixc k) = w (ixc k) := fun k => by
    have : (eac (d := d)) (ixc k) = 0 := by simp [eac]
    simp [this]
  have hy : ∀ k, (w + c • (eac (d := d))) (iyc k) = w (iyc k) := fun k => by
    have : (eac (d := d)) (iyc k) = 0 := by simp [eac]
    simp [this]
  have ha : (w + c • (eac (d := d))) iac = w iac + c := by
    have : (eac (d := d)) iac = 1 := by simp [eac]
    simp [this]
  simp only [Gf, Nxf, Qf, hx, hy, ha]
  rw [show -(w iac + c) = -c + -w iac by ring, Real.exp_add]
  ring

theorem Gf_fderiv_pack (r : ℝ) (x y : SDEState d) (a : ℝ) :
    fderiv ℝ (Gf r) (pack x y a) = Real.exp (-a) • fderiv ℝ (Gf r) (pack x y 0) ∧
      fderiv ℝ (fderiv ℝ (Gf r)) (pack x y a) =
        Real.exp (-a) • fderiv ℝ (fderiv ℝ (Gf r)) (pack x y 0) := by
  have h := fderiv12_translate (Gf_contDiff r) (a • (eac (d := d))) (Real.exp (-a))
    (fun w => Gf_translate r a w) (pack x y 0)
  rwa [pack_add_eac, zero_add] at h

theorem Gf_fderiv_eac (r : ℝ) (u : SDEState (d + d + 1)) :
    fderiv ℝ (Gf r) u (eac (d := d)) = -Gf r u := by
  refine fderiv_eq_of_line ((Gf_contDiff r (n := 1)).differentiable_one) u _ ?_
  have e : (fun s : ℝ => Gf r (u + s • (eac (d := d)))) = fun s => Real.exp (-s) * Gf r u :=
    funext fun s => Gf_translate r s u
  rw [e]
  have := ((hasDerivAt_id (0 : ℝ)).neg.exp).mul_const (Gf r u)
  simpa using this

theorem Gf_nonneg (r : ℝ) (u : SDEState (d + d + 1)) : 0 ≤ Gf r u := by
  unfold Gf
  refine mul_nonneg (Real.exp_pos _).le (mul_nonneg (cutoff_nonneg _ _) (psiQ_nonneg ?_))
  unfold Qf
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-- Line expansion of `G0f`. -/
theorem G0f_line (u v : SDEState (d + d + 1)) (s : ℝ) :
    G0f (u + s • v) = Real.exp (-(u iac + s * v iac)) *
      psiQ (∑ k, ((u (ixc k) - u (iyc k)) + s * (v (ixc k) - v (iyc k))) ^ 2) := by
  simp only [G0f, Qf, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  congr 2
  exact Finset.sum_congr rfl fun k _ => by ring

/-- `D G0(u) v = e^{-a} (ψ'(Q) · 2 Σ (x-y)(v_x - v_y) - v_a ψ(Q))`. -/
theorem G0f_fderiv (u v : SDEState (d + d + 1)) :
    fderiv ℝ G0f u v = Real.exp (-u iac) *
      (deriv psiQ (Qf u) * (2 * ∑ k, (u (ixc k) - u (iyc k)) * (v (ixc k) - v (iyc k))) -
        v iac * psiQ (Qf u)) := by
  refine fderiv_eq_of_line (G0f_contDiff (n := 1)).differentiable_one u v ?_
  simp only [G0f_line]
  have he := (((hasDerivAt_mul_const (v iac)).const_add (u iac)).neg (x := (0 : ℝ))).exp
  have hs : HasDerivAt (fun r : ℝ => ∑ k, ((u (ixc k) - u (iyc k)) + r * (v (ixc k) - v (iyc k))) ^ 2)
      (∑ k, 2 * ((u (ixc k) - u (iyc k)) + 0 * (v (ixc k) - v (iyc k))) *
        (v (ixc k) - v (iyc k))) 0 :=
    HasDerivAt.fun_sum fun k _ => hasDerivAt_sq_affine _ _ 0
  have hp := (psiQ_differentiable _).hasDerivAt.comp (0 : ℝ) hs
  refine (he.mul hp).congr_deriv ?_
  simp only [Pi.neg_apply, zero_mul, add_zero, Qf, Function.comp_apply]
  have h2 : ∑ k, 2 * (u (ixc k) - u (iyc k)) * (v (ixc k) - v (iyc k)) =
      2 * ∑ k, (u (ixc k) - u (iyc k)) * (v (ixc k) - v (iyc k)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [h2]; ring

/-- `D² G0(u)(v,v) = e^{-a} (ψ''(Q) (2 Σ (x-y)(v_x-v_y))² + ψ'(Q) · 2 |v_x - v_y|²)`, `v_a = 0`. -/
theorem G0f_fderiv2 (u v : SDEState (d + d + 1)) (hv : v iac = 0) :
    fderiv ℝ (fderiv ℝ G0f) u v v = Real.exp (-u iac) *
      (deriv (deriv psiQ) (Qf u) *
          (2 * ∑ k, (u (ixc k) - u (iyc k)) * (v (ixc k) - v (iyc k))) ^ 2 +
        deriv psiQ (Qf u) * (2 * ∑ k, (v (ixc k) - v (iyc k)) ^ 2)) := by
  set q : ℝ → ℝ := fun s => ∑ k, ((u (ixc k) - u (iyc k)) + s * (v (ixc k) - v (iyc k))) ^ 2
    with hqdef
  set q' : ℝ → ℝ := fun s => ∑ k, 2 * ((u (ixc k) - u (iyc k)) +
      s * (v (ixc k) - v (iyc k))) * (v (ixc k) - v (iyc k)) with hq'def
  have hq : ∀ s, HasDerivAt q (q' s) s := fun s =>
    HasDerivAt.fun_sum fun k _ => hasDerivAt_sq_affine _ _ s
  have hq2 : HasDerivAt q' (∑ k, 2 * (v (ixc k) - v (iyc k)) * (v (ixc k) - v (iyc k))) 0 := by
    refine HasDerivAt.fun_sum fun k _ => ?_
    have := ((((hasDerivAt_id (0 : ℝ)).mul_const (v (ixc k) - v (iyc k))).const_add
      (u (ixc k) - u (iyc k))).const_mul 2).mul_const (v (ixc k) - v (iyc k))
    exact this.congr_deriv (by first | ring | (simp; ring) | simp)
  refine fderiv2_eq_of_line G0f_contDiff u v
    (φ' := fun s => Real.exp (-u iac) * (deriv psiQ (q s) * q' s)) (fun s => ?_) ?_
  · simp only [G0f_line, hv, mul_zero, add_zero]
    exact (((psiQ_differentiable _).hasDerivAt.comp s (hq s))).const_mul _
  · have hd := ((deriv_psiQ_contDiff (n := 1)).differentiable_one _).hasDerivAt.comp (0 : ℝ) (hq 0)
    refine ((hd.mul hq2).const_mul (Real.exp (-u iac))).congr_deriv ?_
    have hq0 : q 0 = Qf u := by simp [hqdef, Qf]
    have hq'0 : q' 0 = 2 * ∑ k, (u (ixc k) - u (iyc k)) * (v (ixc k) - v (iyc k)) := by
      simp only [hq'def, zero_mul, add_zero, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hs2 : ∑ k, 2 * (v (ixc k) - v (iyc k)) * (v (ixc k) - v (iyc k)) =
        2 * ∑ k, (v (ixc k) - v (iyc k)) ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    simp only [Function.comp_apply, hq0, hq'0, hs2]
    ring

end M10c1

section M10c2
/-! M10c-2: the generator of `Gf r` along `(X, Y, A)` and its form inside the `x`-ball. -/

/-- Generator of `Gf r` along `(X, Y, A)` with coefficient values `σx, bx`, `σy, by'`. -/
noncomputable def driftH (r κ : ℝ) (σx : SDEDiffusion d) (bx : SDEState d) (σy : SDEDiffusion d)
    (by' : SDEState d) (x y : SDEState d) (a : ℝ) : ℝ :=
  fderiv ℝ (Gf r) (pack x y a) (pack bx by' κ) +
    (1 / 2) * ∑ j, fderiv ℝ (fderiv ℝ (Gf r)) (pack x y a)
      (pack (scol σx j) (scol σy j) 0) (pack (scol σx j) (scol σy j) 0)

theorem driftH_inside {r κ : ℝ} (σx : SDEDiffusion d) (bx : SDEState d) (σy : SDEDiffusion d)
    (by' : SDEState d) {x y : SDEState d} (a : ℝ) (h : ‖x‖ ^ 2 < r) :
    driftH r κ σx bx σy by' x y a = Real.exp (-a) *
      (deriv psiQ (‖x - y‖ ^ 2) * (2 * ∑ k, (x k - y k) * (bx k - by' k) + ‖σx - σy‖ ^ 2) +
        (1 / 2) * deriv (deriv psiQ) (‖x - y‖ ^ 2) *
          ∑ j, (2 * ∑ k, (x k - y k) * (scol σx j k - scol σy j k)) ^ 2 -
        κ * psiQ (‖x - y‖ ^ 2)) := by
  have hN : Nxf (pack x y a) < r := by rw [Nxf_pack]; exact h
  obtain ⟨h1, h2⟩ := fderiv12_congr_nhds (Gf_eq_G0f_nhds hN)
  unfold driftH
  rw [h1, h2, G0f_fderiv]
  rw [Finset.sum_congr rfl fun j _ => G0f_fderiv2 (pack x y a)
    (pack (scol σx j) (scol σy j) 0) (pack_iac _ _ _)]
  simp only [pack_ixc, pack_iyc, pack_iac, Qf_pack]
  have hsq := sum_scol_sq σx σy
  have e : ∑ j, Real.exp (-a) * (deriv (deriv psiQ) (‖x - y‖ ^ 2) *
        (2 * ∑ k, (x k - y k) * (scol σx j k - scol σy j k)) ^ 2 +
      deriv psiQ (‖x - y‖ ^ 2) * (2 * ∑ k, (scol σx j k - scol σy j k) ^ 2)) =
      Real.exp (-a) * (deriv (deriv psiQ) (‖x - y‖ ^ 2) *
        ∑ j, (2 * ∑ k, (x k - y k) * (scol σx j k - scol σy j k)) ^ 2 +
      deriv psiQ (‖x - y‖ ^ 2) * (2 * ‖σx - σy‖ ^ 2)) := by
    rw [← hsq]
    have hj : ∀ j, Real.exp (-a) * (deriv (deriv psiQ) (‖x - y‖ ^ 2) *
          (2 * ∑ k, (x k - y k) * (scol σx j k - scol σy j k)) ^ 2 +
        deriv psiQ (‖x - y‖ ^ 2) * (2 * ∑ k, (scol σx j k - scol σy j k) ^ 2)) =
        (Real.exp (-a) * deriv (deriv psiQ) (‖x - y‖ ^ 2)) *
          (2 * ∑ k, (x k - y k) * (scol σx j k - scol σy j k)) ^ 2 +
        (Real.exp (-a) * deriv psiQ (‖x - y‖ ^ 2) * 2) *
          ∑ k, (scol σx j k - scol σy j k) ^ 2 := fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    ring
  rw [e]
  ring

end M10c2

section M10c3
/-! M10c-3: pointwise bounds for the generator `driftH` of `Gf r`. -/

theorem psiQ_deriv_bounds : ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ q : ℝ, 0 ≤ q →
    |deriv psiQ q| ≤ C1 ∧ |deriv (deriv psiQ) q| ≤ C2 := by
  have hc1 : Continuous (deriv psiQ) := (deriv_psiQ_contDiff (n := 0)).continuous
  have hc2 : Continuous (deriv (deriv psiQ)) :=
    (contDiff_infty_iff_deriv.1 (deriv_psiQ_contDiff (n := ⊤))).2.continuous
  obtain ⟨B1, hB1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    hc1.continuousOn
  obtain ⟨B2, hB2⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    hc2.continuousOn
  refine ⟨max B1 0, max B2 0, le_max_right _ _, le_max_right _ _, fun q hq => ?_⟩
  by_cases h4 : q ≤ 4
  · have h1 := hB1 q ⟨hq, h4⟩
    have h2 := hB2 q ⟨hq, h4⟩
    rw [Real.norm_eq_abs] at h1 h2
    exact ⟨h1.trans (le_max_left _ _), h2.trans (le_max_left _ _)⟩
  · obtain ⟨e1, e2⟩ := deriv_psiQ_zero (not_le.1 h4)
    rw [e1, e2]
    simp

theorem sum_inner_col_sq_le (x y : SDEState d) (σx σy : SDEDiffusion d) :
    ∑ j, (2 * ∑ k, (x k - y k) * (scol σx j k - scol σy j k)) ^ 2 ≤
      4 * ‖x - y‖ ^ 2 * ‖σx - σy‖ ^ 2 := by
  rw [← sum_scol_sq σx σy]
  conv_rhs => rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => x k - y k)
    (fun k => scol σx j k - scol σy j k)
  have hn : ‖x - y‖ ^ 2 = ∑ k, (x k - y k) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]; simp
  rw [hn]
  calc (2 * ∑ k, (x k - y k) * (scol σx j k - scol σy j k)) ^ 2
      = 4 * (∑ k, (x k - y k) * (scol σx j k - scol σy j k)) ^ 2 := by ring
    _ ≤ 4 * ((∑ k, (x k - y k) ^ 2) * ∑ k, (scol σx j k - scol σy j k) ^ 2) := by gcongr
    _ = 4 * (∑ k, (x k - y k) ^ 2) * ∑ k, (scol σx j k - scol σy j k) ^ 2 := by ring

/-- The inside bound for `driftH` with constant `C`: wherever `|x|² < r`, if the `X`-coefficients
are `L`-close to reference values `σ', b'` when `|x-y|² ≤ 4` and `κ ≥ C(1+L)²`, the generator is at
most `C e^{-a}` times the squared reference error of the `Y`-coefficients. -/
def DrHin (d : ℕ) (C : ℝ) : Prop :=
  ∀ (r κ L : ℝ) (σx : SDEDiffusion d) (bx : SDEState d) (σy : SDEDiffusion d) (by' : SDEState d)
    (σ' : SDEDiffusion d) (b' : SDEState d) (x y : SDEState d) (a : ℝ), ‖x‖ ^ 2 < r → 0 ≤ L →
    0 ≤ κ → (‖x - y‖ ^ 2 ≤ 4 → ‖bx - b'‖ ≤ L * ‖x - y‖ ∧ ‖σx - σ'‖ ≤ L * ‖x - y‖) →
    C * (1 + L) ^ 2 ≤ κ →
    driftH r κ σx bx σy by' x y a ≤ Real.exp (-a) * (C * (‖b' - by'‖ ^ 2 + ‖σ' - σy‖ ^ 2))

set_option maxHeartbeats 1000000 in
theorem driftH_le_inside : ∃ C : ℝ, 0 ≤ C ∧ DrHin d C := by
  obtain ⟨C1, C2, hC1, hC2, hD⟩ := psiQ_deriv_bounds
  refine ⟨10 * (C1 + 16 * C2 + 1), by positivity, ?_⟩
  intro r κ L σx bx σy by' σ' b' x y a hx hL hκ0 hLip hκ
  rw [driftH_inside σx bx σy by' a hx]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hQ0 : 0 ≤ ‖x - y‖ ^ 2 := sq_nonneg _
  have hψ0 := psiQ_nonneg hQ0
  have heb := norm_nonneg (b' - by')
  have hes := norm_nonneg (σ' - σy)
  have hE0 : 0 ≤ 10 * (C1 + 16 * C2 + 1) * (‖b' - by'‖ ^ 2 + ‖σ' - σy‖ ^ 2) := by positivity
  by_cases h4 : ‖x - y‖ ^ 2 ≤ 4
  · obtain ⟨hb, hσ⟩ := hLip h4
    obtain ⟨hd1, hd2⟩ := hD _ hQ0
    have hqn := norm_nonneg (x - y)
    have hin : |∑ k, (x k - y k) * (bx k - by' k)| ≤ ‖x - y‖ * ‖bx - by'‖ := by
      have := abs_real_inner_le_norm (x - y) (bx - by')
      rw [PiLp.inner_apply] at this
      simpa [mul_comm] using this
    have e1 : ‖bx - by'‖ ≤ L * ‖x - y‖ + ‖b' - by'‖ :=
      (norm_sub_le_norm_sub_add_norm_sub bx b' by').trans (by linarith)
    have e2 : ‖σx - σy‖ ≤ L * ‖x - y‖ + ‖σ' - σy‖ :=
      (norm_sub_le_norm_sub_add_norm_sub σx σ' σy).trans (by linarith)
    have hn2 := norm_nonneg (σx - σy)
    have hS : ‖σx - σy‖ ^ 2 ≤ 2 * L ^ 2 * ‖x - y‖ ^ 2 + 2 * ‖σ' - σy‖ ^ 2 := by
      linarith only [pow_le_pow_left₀ hn2 e2 2, sq_nonneg (L * ‖x - y‖ - ‖σ' - σy‖)]
    have hT1 : |2 * ∑ k, (x k - y k) * (bx k - by' k)| ≤
        2 * L * ‖x - y‖ ^ 2 + ‖x - y‖ ^ 2 + ‖b' - by'‖ ^ 2 := by
      rw [abs_mul, abs_two]
      have h4' : ‖x - y‖ * ‖bx - by'‖ ≤ L * ‖x - y‖ ^ 2 + ‖x - y‖ * ‖b' - by'‖ := by
        linarith only [mul_le_mul_of_nonneg_left e1 hqn]
      linarith only [hin, h4', sq_nonneg (‖x - y‖ - ‖b' - by'‖)]
    have hT3 := sum_inner_col_sq_le x y σx σy
    have hT3' : ∑ j, (2 * ∑ k, (x k - y k) * (scol σx j k - scol σy j k)) ^ 2 ≤
        16 * ‖σx - σy‖ ^ 2 := by
      have : 4 * ‖x - y‖ ^ 2 * ‖σx - σy‖ ^ 2 ≤ 4 * 4 * ‖σx - σy‖ ^ 2 := by gcongr
      linarith only [hT3, this]
    have hT3n : 0 ≤ ∑ j, (2 * ∑ k, (x k - y k) * (scol σx j k - scol σy j k)) ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    set T1 := 2 * ∑ k, (x k - y k) * (bx k - by' k) with hT1def
    set T3 := ∑ j, (2 * ∑ k, (x k - y k) * (scol σx j k - scol σy j k)) ^ 2 with hT3def
    set D1 := deriv psiQ (‖x - y‖ ^ 2) with hD1def
    set D2 := deriv (deriv psiQ) (‖x - y‖ ^ 2) with hD2def
    have hA : D1 * (T1 + ‖σx - σy‖ ^ 2) ≤ C1 * (|T1| + ‖σx - σy‖ ^ 2) := by
      calc D1 * (T1 + ‖σx - σy‖ ^ 2) ≤ |D1 * (T1 + ‖σx - σy‖ ^ 2)| := le_abs_self _
        _ = |D1| * |T1 + ‖σx - σy‖ ^ 2| := abs_mul _ _
        _ ≤ C1 * (|T1| + ‖σx - σy‖ ^ 2) := by
          refine mul_le_mul hd1 ?_ (abs_nonneg _) hC1
          calc |T1 + ‖σx - σy‖ ^ 2| ≤ |T1| + |‖σx - σy‖ ^ 2| := abs_add_le _ _
            _ = |T1| + ‖σx - σy‖ ^ 2 := by rw [abs_of_nonneg (sq_nonneg ‖σx - σy‖)]
    have hB : 1 / 2 * D2 * T3 ≤ 8 * C2 * ‖σx - σy‖ ^ 2 := by
      have h1 : D2 * T3 ≤ C2 * T3 := mul_le_mul_of_nonneg_right ((le_abs_self _).trans hd2) hT3n
      have h2 : C2 * T3 ≤ C2 * (16 * ‖σx - σy‖ ^ 2) := mul_le_mul_of_nonneg_left hT3' hC2
      linarith only [h1, h2]
    have hlin := psiQ_ge_lin hQ0 h4
    have hK0 : 0 ≤ C1 * (2 * L + 1 + 2 * L ^ 2) + 16 * C2 * L ^ 2 := by positivity
    have h5K : 5 * (C1 * (2 * L + 1 + 2 * L ^ 2) + 16 * C2 * L ^ 2) ≤ κ := by
      have : 5 * (C1 * (2 * L + 1 + 2 * L ^ 2) + 16 * C2 * L ^ 2) ≤
          10 * (C1 + 16 * C2 + 1) * (1 + L) ^ 2 := by
        have e : 10 * (C1 + 16 * C2 + 1) * (1 + L) ^ 2 -
            5 * (C1 * (2 * L + 1 + 2 * L ^ 2) + 16 * C2 * L ^ 2) =
            C1 * (5 + 10 * L) + C2 * (160 + 320 * L + 80 * L ^ 2) + 10 * (1 + L) ^ 2 := by ring
        have f1 := mul_nonneg hC1 (show (0 : ℝ) ≤ 5 + 10 * L by linarith)
        have f2 := mul_nonneg hC2 (show (0 : ℝ) ≤ 160 + 320 * L + 80 * L ^ 2 by positivity)
        have f3 := sq_nonneg (1 + L)
        linarith only [e, f1, f2, f3]
      linarith only [this, hκ]
    have hKQ : (C1 * (2 * L + 1 + 2 * L ^ 2) + 16 * C2 * L ^ 2) * ‖x - y‖ ^ 2 ≤
        κ * psiQ (‖x - y‖ ^ 2) := by
      calc (C1 * (2 * L + 1 + 2 * L ^ 2) + 16 * C2 * L ^ 2) * ‖x - y‖ ^ 2
          ≤ (C1 * (2 * L + 1 + 2 * L ^ 2) + 16 * C2 * L ^ 2) * (5 * psiQ (‖x - y‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left (by linarith) hK0
        _ = (5 * (C1 * (2 * L + 1 + 2 * L ^ 2) + 16 * C2 * L ^ 2)) * psiQ (‖x - y‖ ^ 2) := by
            ring
        _ ≤ κ * psiQ (‖x - y‖ ^ 2) := mul_le_mul_of_nonneg_right h5K hψ0
    have hA' : C1 * (|T1| + ‖σx - σy‖ ^ 2) ≤ C1 * (2 * L * ‖x - y‖ ^ 2 + ‖x - y‖ ^ 2 +
        ‖b' - by'‖ ^ 2 + (2 * L ^ 2 * ‖x - y‖ ^ 2 + 2 * ‖σ' - σy‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC1
    have hB' : 8 * C2 * ‖σx - σy‖ ^ 2 ≤ 8 * C2 * (2 * L ^ 2 * ‖x - y‖ ^ 2 + 2 * ‖σ' - σy‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    have hErr : C1 * ‖b' - by'‖ ^ 2 + (2 * C1 + 16 * C2) * ‖σ' - σy‖ ^ 2 ≤
        10 * (C1 + 16 * C2 + 1) * (‖b' - by'‖ ^ 2 + ‖σ' - σy‖ ^ 2) := by
      have e : 10 * (C1 + 16 * C2 + 1) * (‖b' - by'‖ ^ 2 + ‖σ' - σy‖ ^ 2) -
          (C1 * ‖b' - by'‖ ^ 2 + (2 * C1 + 16 * C2) * ‖σ' - σy‖ ^ 2) =
          (9 * C1 + 160 * C2 + 10) * ‖b' - by'‖ ^ 2 + (8 * C1 + 144 * C2 + 10) * ‖σ' - σy‖ ^ 2 := by
        ring
      have f1 := mul_nonneg (show (0 : ℝ) ≤ 9 * C1 + 160 * C2 + 10 by linarith) (sq_nonneg ‖b' - by'‖)
      have f2 := mul_nonneg (show (0 : ℝ) ≤ 8 * C1 + 144 * C2 + 10 by linarith) (sq_nonneg ‖σ' - σy‖)
      linarith
    have eK : C1 * (2 * L * ‖x - y‖ ^ 2 + ‖x - y‖ ^ 2 + ‖b' - by'‖ ^ 2 +
        (2 * L ^ 2 * ‖x - y‖ ^ 2 + 2 * ‖σ' - σy‖ ^ 2)) +
        8 * C2 * (2 * L ^ 2 * ‖x - y‖ ^ 2 + 2 * ‖σ' - σy‖ ^ 2) =
        (C1 * (2 * L + 1 + 2 * L ^ 2) + 16 * C2 * L ^ 2) * ‖x - y‖ ^ 2 +
        (C1 * ‖b' - by'‖ ^ 2 + (2 * C1 + 16 * C2) * ‖σ' - σy‖ ^ 2) := by ring
    linarith only [hA, hB, hA', hB', hKQ, hErr, eK]
  · obtain ⟨e1, e2⟩ := deriv_psiQ_zero (not_le.1 h4)
    rw [e1, e2]
    linarith only [mul_nonneg hκ0 hψ0, hE0]

/-- Far from the diagonal (`|x-y|² > 4`) inside the `x`-ball the generator is `≤ 0`. -/
theorem driftH_far {r κ : ℝ} (σx : SDEDiffusion d) (bx : SDEState d) (σy : SDEDiffusion d)
    (by' : SDEState d) {x y : SDEState d} (a : ℝ) (h : ‖x‖ ^ 2 < r) (h4 : 4 < ‖x - y‖ ^ 2)
    (hκ : 0 ≤ κ) : driftH r κ σx bx σy by' x y a ≤ 0 := by
  rw [driftH_inside σx bx σy by' a h]
  obtain ⟨e1, e2⟩ := deriv_psiQ_zero h4
  rw [e1, e2]
  have hψ0 := psiQ_nonneg (sq_nonneg ‖x - y‖)
  have := mul_nonneg hκ hψ0
  have hea := Real.exp_pos (-a)
  nlinarith

/-- The `x`-only part `e^{-a} χ_r(|x|²)` of `Gf r`. -/
noncomputable def H1f (r : ℝ) (u : SDEState (d + d + 1)) : ℝ :=
  Real.exp (-u iac) * cutoff r (Nxf u)

theorem H1f_contDiff (r : ℝ) {n : ℕ∞} : ContDiff ℝ n (H1f (d := d) r) :=
  (Real.contDiff_exp.comp (coord_contDiff _).neg).mul ((cutoff_contDiff r).comp Nxf_contDiff)

theorem Gf_eq_H1f_nhds {r : ℝ} {u : SDEState (d + d + 1)} (hu : 4 < Qf u) :
    Gf r =ᶠ[𝓝 u] H1f r := by
  have hc : ContinuousAt (Qf (d := d)) u := (Qf_contDiff (n := 0)).continuous.continuousAt
  filter_upwards [hc.eventually (lt_mem_nhds hu)] with w hw
  simp only [Gf, H1f, psiQ_eq_one hw.le, mul_one]

theorem H1f_translate_y (r : ℝ) (c : SDEState d) (w : SDEState (d + d + 1)) :
    H1f r (w + pack 0 c 0) = 1 * H1f r w := by
  have hx : ∀ k, (w + pack 0 c 0) (ixc k) = w (ixc k) := fun k => by simp
  have ha : (w + pack 0 c 0) iac = w iac := by simp
  simp only [H1f, Nxf, hx, ha, one_mul]

theorem pack_split (x y : SDEState d) : pack x y 0 = pack x 0 0 + pack 0 y 0 :=
  pack_ext (fun k => by simp) (fun k => by simp) (by simp)

theorem H1f_fderiv_y (r : ℝ) (x y : SDEState d) :
    fderiv ℝ (H1f r) (pack x y 0) = fderiv ℝ (H1f r) (pack x 0 0) ∧
      fderiv ℝ (fderiv ℝ (H1f r)) (pack x y 0) = fderiv ℝ (fderiv ℝ (H1f r)) (pack x 0 0) := by
  have h := fderiv12_translate (H1f_contDiff r) (pack 0 y 0) 1
    (fun w => H1f_translate_y r y w) (pack x 0 0)
  rw [← pack_split, one_smul, one_smul] at h
  exact h

/-- First and second derivatives of `Gf r` are bounded on all of `(x, y)` (at `a = 0`). -/
theorem Gf_deriv_bound (r : ℝ) (w w' : SDEState (d + d + 1)) :
    ∃ B, 0 ≤ B ∧ ∀ x y : SDEState d, |fderiv ℝ (Gf r) (pack x y 0) w| ≤ B ∧
      |fderiv ℝ (fderiv ℝ (Gf r)) (pack x y 0) w w'| ≤ B := by
  set ρ : ℝ := |r| + 2 with hρ
  have hD1 : Continuous (fderiv ℝ (Gf (d := d) r)) :=
    (Gf_contDiff r (n := 2)).continuous_fderiv two_ne_zero
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ (Gf (d := d) r))) :=
    ((Gf_contDiff r (n := 2)).fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hE1 : Continuous (fderiv ℝ (H1f (d := d) r)) :=
    (H1f_contDiff r (n := 2)).continuous_fderiv two_ne_zero
  have hE2 : Continuous (fderiv ℝ (fderiv ℝ (H1f (d := d) r))) :=
    ((H1f_contDiff r (n := 2)).fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hp2 : Continuous fun p : SDEState d × SDEState d => pack p.1 p.2 0 :=
    pack_continuous continuous_fst continuous_snd continuous_const
  have hp1 : Continuous fun x : SDEState d => pack x (0 : SDEState d) 0 :=
    pack_continuous continuous_id continuous_const continuous_const
  have K1 := (isCompact_closedBall (0 : SDEState d) ρ).prod
    (isCompact_closedBall (0 : SDEState d) (ρ + 3))
  have K2 := isCompact_closedBall (0 : SDEState d) ρ
  obtain ⟨B1, hB1⟩ := K1.exists_bound_of_continuousOn
    (f := fun p : SDEState d × SDEState d => fderiv ℝ (Gf r) (pack p.1 p.2 0) w)
    ((hD1.comp hp2).clm_apply continuous_const).continuousOn
  obtain ⟨B2, hB2⟩ := K1.exists_bound_of_continuousOn
    (f := fun p : SDEState d × SDEState d => fderiv ℝ (fderiv ℝ (Gf r)) (pack p.1 p.2 0) w w')
    (((hD2.comp hp2).clm_apply continuous_const).clm_apply continuous_const).continuousOn
  obtain ⟨B3, hB3⟩ := K2.exists_bound_of_continuousOn
    (f := fun x : SDEState d => fderiv ℝ (H1f r) (pack x 0 0) w)
    ((hE1.comp hp1).clm_apply continuous_const).continuousOn
  obtain ⟨B4, hB4⟩ := K2.exists_bound_of_continuousOn
    (f := fun x : SDEState d => fderiv ℝ (fderiv ℝ (H1f r)) (pack x 0 0) w w')
    (((hE2.comp hp1).clm_apply continuous_const).clm_apply continuous_const).continuousOn
  set M := max (max B1 B2) (max (max B3 B4) 0) with hM
  have hM0 : 0 ≤ M := le_max_of_le_right (le_max_right _ _)
  have hM1 : B1 ≤ M := le_max_of_le_left (le_max_left _ _)
  have hM2 : B2 ≤ M := le_max_of_le_left (le_max_right _ _)
  have hM3 : B3 ≤ M := le_max_of_le_right (le_max_of_le_left (le_max_left _ _))
  have hM4 : B4 ≤ M := le_max_of_le_right (le_max_of_le_left (le_max_right _ _))
  refine ⟨M, hM0, fun x y => ?_⟩
  by_cases hN : r + 1 < ‖x‖ ^ 2
  · obtain ⟨h1, h2⟩ := Gf_fderiv_zero (r := r) (u := pack x y 0) (by rw [Nxf_pack]; exact hN)
    rw [h1, h2]
    simp only [zero_apply, abs_zero]
    exact ⟨hM0, hM0⟩
  · have hxρ : ‖x‖ ≤ ρ := by
      by_contra hc
      push_neg at hc
      have hr0 := abs_nonneg r
      have hr1 := le_abs_self r
      have hxn := norm_nonneg x
      nlinarith
    by_cases hQ : ‖x - y‖ ^ 2 ≤ 5
    · have hy : ‖y‖ ≤ ρ + 3 := by
        have h3 : ‖x - y‖ ≤ 3 := by nlinarith [norm_nonneg (x - y)]
        have := norm_sub_norm_le y x
        rw [norm_sub_rev] at this
        linarith
      have hmem : (x, y) ∈ Metric.closedBall (0 : SDEState d) ρ ×ˢ
          Metric.closedBall (0 : SDEState d) (ρ + 3) :=
        ⟨mem_closedBall_zero_iff.2 hxρ, mem_closedBall_zero_iff.2 hy⟩
      have h1 := hB1 _ hmem
      have h2 := hB2 _ hmem
      rw [Real.norm_eq_abs] at h1 h2
      exact ⟨h1.trans hM1, h2.trans hM2⟩
    · have hQ4 : 4 < Qf (pack x y 0 : SDEState (d + d + 1)) := by rw [Qf_pack]; linarith
      obtain ⟨e1, e2⟩ := fderiv12_congr_nhds (Gf_eq_H1f_nhds (r := r) hQ4)
      obtain ⟨f1, f2⟩ := H1f_fderiv_y r x y
      rw [e1, e2, f1, f2]
      have hmem : x ∈ Metric.closedBall (0 : SDEState d) ρ := mem_closedBall_zero_iff.2 hxρ
      have h1 := hB3 _ hmem
      have h2 := hB4 _ hmem
      rw [Real.norm_eq_abs] at h1 h2
      exact ⟨h1.trans hM3, h2.trans hM4⟩

end M10c3

end ItoLib

-- ===== G =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c4
/-! M10c-4: the Ito formula along `(X, Y, A)` for an arbitrary `C²` test function `F` whose
martingale integrands are bounded (`ito_coupled_F`); applied to `Gf r`. -/

/-- Generator of a `C²` function `F` along `(X, Y, A)` with coefficient values `σx, bx` for `X`
and `σy, by'` for `Y`. -/
noncomputable def driftGen (F : SDEState (d + d + 1) → ℝ) (κ : ℝ) (σx : SDEDiffusion d) (bx : SDEState d) (σy : SDEDiffusion d)
    (by' : SDEState d) (x y : SDEState d) (a : ℝ) : ℝ :=
  fderiv ℝ F (pack x y a) (pack bx by' κ) +
    (1 / 2) * ∑ j, fderiv ℝ (fderiv ℝ F) (pack x y a)
      (pack (scol σx j) (scol σy j) 0) (pack (scol σx j) (scol σy j) 0)

theorem driftGen_coords (F : SDEState (d + d + 1) → ℝ) (κ : ℝ) (σx : SDEDiffusion d) (bx : SDEState d) (σy : SDEDiffusion d)
    (by' : SDEState d) (x y : SDEState d) (a : ℝ) :
    (∑ i, fderiv ℝ F (pack x y a) (EuclideanSpace.single i 1) * pack bx by' κ i) +
      (1 / 2) * ∑ i, ∑ i', ∑ j, fderiv ℝ (fderiv ℝ F) (pack x y a)
        (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1) *
          pack (scol σx j) (scol σy j) 0 i * pack (scol σx j) (scol σy j) 0 i'
      = driftGen F κ σx bx σy by' x y a := by
  unfold driftGen
  rw [clm_coord (fderiv ℝ F (pack x y a)) (pack bx by' κ)]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · congr 1
    rw [Finset.sum_congr rfl fun j _ => clm2_coord (fderiv ℝ (fderiv ℝ F) (pack x y a))
      (pack (scol σx j) (scol σy j) 0) (pack (scol σx j) (scol σy j) 0)]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring

set_option maxHeartbeats 1000000 in
/-- Ito formula for a `C²` function `F` along `(X, Y, A)` for general Ito processes `X`, `Y`. -/
theorem ito_coupled_F [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {X Y : ℝ≥0 → Ω → SDEState d} {HX HY JX JY : ℝ≥0 → Ω → SDEDiffusion d}
    {bX bY : ℝ≥0 → Ω → SDEState d}
    (hXm : ∀ s, Measurable (X s)) (hYm : ∀ s, Measurable (Y s))
    (hXc : ∀ ω, Continuous fun s => X s ω) (hYc : ∀ ω, Continuous fun s => Y s ω)
    (hXa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (X s))
    (hYa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (Y s))
    (hHXa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (HX s))
    (hHYa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (HY s))
    (hHXc : ∀ ω, Continuous fun s => HX s ω) (hHYc : ∀ ω, Continuous fun s => HY s ω)
    (hbXa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (bX s))
    (hbYa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (bY s))
    (hbXc : ∀ ω, Continuous fun s => bX s ω) (hbYc : ∀ ω, Continuous fun s => bY s ω)
    (hJX : ∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) (fun s ω => HX s ω (i, j)) (fun s ω => JX s ω (i, j)))
    (hJY : ∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) (fun s ω => HY s ω (i, j)) (fun s ω => JY s ω (i, j)))
    (hXeq : ∀ᵐ ω ∂P, ∀ (s : ℝ≥0) i, X s ω i = X 0 ω i + (∑ j, JX s ω (i, j)) +
      ∫ u in (0 : ℝ)..s.val, bX u.toNNReal ω i)
    (hYeq : ∀ᵐ ω ∂P, ∀ (s : ℝ≥0) i, Y s ω i = Y 0 ω i + (∑ j, JY s ω (i, j)) +
      ∫ u in (0 : ℝ)..s.val, bY u.toNNReal ω i)
    {x0 y0 : SDEState d} (hX0 : ∀ᵐ ω ∂P, X 0 ω = x0) (hY0 : ∀ᵐ ω ∂P, Y 0 ω = y0)
    {κ : SDEState d → SDEState d → ℝ}
    (hκ : Continuous fun p : SDEState d × SDEState d => κ p.1 p.2)
    (hκ0 : ∀ x y, 0 ≤ κ x y) {F : SDEState (d + d + 1) → ℝ} (hF : ContDiff ℝ 2 F)
    (hFb : ∀ i j, ∃ C, ∀ s ω (a : ℝ), 0 ≤ a →
      |fderiv ℝ F (pack (X s ω) (Y s ω) a) (EuclideanSpace.single i 1) *
        pack (scol (HX s ω) j) (scol (HY s ω) j) 0 i| ≤ C)
    (t : ℝ≥0) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧ ∫ ω, Z ω ∂P = 0 ∧
      ∀ᵐ ω ∂P, F (pack (X t ω) (Y t ω)
          (∫ u in (0 : ℝ)..t.val, κ (X u.toNNReal ω) (Y u.toNNReal ω))) =
        F (pack x0 y0 0) + Z ω + ∫ u in (0 : ℝ)..t.val,
          driftGen F (κ (X u.toNNReal ω) (Y u.toNNReal ω)) (HX u.toNNReal ω) (bX u.toNNReal ω)
            (HY u.toNNReal ω) (bY u.toNNReal ω) (X u.toNNReal ω) (Y u.toNNReal ω)
            (∫ v in (0 : ℝ)..((u.toNNReal : ℝ≥0) : ℝ), κ (X v.toNNReal ω) (Y v.toNNReal ω)) := by
  have hXYc : ∀ ω, Continuous fun s => (X s ω, Y s ω) := fun ω => (hXc ω).prodMk (hYc ω)
  have hXYa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s]
      fun ω => (X s ω, Y s ω) := fun s => (hXa s).prodMk (hYa s)
  have hXYm : ∀ s, Measurable fun ω => (X s ω, Y s ω) := fun s => (hXm s).prodMk (hYm s)
  have hκc : ∀ ω, Continuous fun s => κ (X s ω) (Y s ω) := fun ω => hκ.comp (hXYc ω)
  -- the clock `A`
  let A : ℝ≥0 → Ω → ℝ := fun s ω => ∫ u in (0 : ℝ)..s.val, κ (X u.toNNReal ω) (Y u.toNNReal ω)
  have hAa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (A s) := fun s =>
    measurable_intervalIntegral_of_continuous _ s
      (fun u hu => hκ.measurable.comp ((hXYa u).mono (completedBrownianPast_mono P W _ hu) le_rfl))
      hκc
  have hAm : ∀ s, Measurable (A s) := fun s =>
    measurable_intervalIntegral_of_continuous _ s (fun u _ => hκ.measurable.comp (hXYm u)) hκc
  have hA0 : ∀ s ω, 0 ≤ A s ω := fun s ω =>
    intervalIntegral.integral_nonneg s.2 fun u _ => hκ0 _ _
  have hAc : ∀ ω, Continuous fun s => A s ω := fun ω => by
    have hgc : Continuous fun u : ℝ => κ (X u.toNNReal ω) (Y u.toNNReal ω) :=
      (hκc ω).comp continuous_real_toNNReal
    have hp : Continuous fun b : ℝ => ∫ u in (0 : ℝ)..b, κ (X u.toNNReal ω) (Y u.toNNReal ω) :=
      continuous_iff_continuousAt.2 fun b =>
        (hgc.integral_hasStrictDerivAt 0 b).hasDerivAt.continuousAt
    exact hp.comp NNReal.continuous_coe
  -- the coupled process `U`
  let U : ℝ≥0 → Ω → SDEState (d + d + 1) := fun s ω => pack (X s ω) (Y s ω) (A s ω)
  have hpk : Continuous fun q : SDEState d × SDEState d × ℝ => pack q.1 q.2.1 q.2.2 :=
    pack_continuous continuous_fst (continuous_fst.comp continuous_snd)
      (continuous_snd.comp continuous_snd)
  have hUm : ∀ s, Measurable (U s) := fun s =>
    hpk.measurable.comp ((hXm s).prodMk ((hYm s).prodMk (hAm s)))
  have hUa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (U s) := fun s =>
    hpk.measurable.comp ((hXa s).prodMk ((hYa s).prodMk (hAa s)))
  have hUc : ∀ ω, Continuous fun s => U s ω := fun ω =>
    hpk.comp ((hXc ω).prodMk ((hYc ω).prodMk (hAc ω)))
  have hcol : ∀ (i : Fin (d + d + 1)) (j : Fin d),
      Continuous fun p : SDEDiffusion d × SDEDiffusion d =>
        pack (scol p.1 j) (scol p.2 j) 0 i := fun i j =>
    ((coord_contDiff i (n := 0)).continuous).comp
      (pack_continuous (scol_continuous continuous_fst j)
        (scol_continuous continuous_snd j) continuous_const)
  have hbf : ∀ i : Fin (d + d + 1), Continuous fun q : SDEState d × SDEState d × ℝ =>
      pack q.1 q.2.1 q.2.2 i := fun i =>
    ((coord_contDiff i (n := 0)).continuous).comp hpk
  have hHH : ∀ ω, Continuous fun s => (HX s ω, HY s ω) := fun ω => (hHXc ω).prodMk (hHYc ω)
  have hHHa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s]
      fun ω => (HX s ω, HY s ω) := fun s => (hHXa s).prodMk (hHYa s)
  have hBB : ∀ ω, Continuous fun s => (bX s ω, bY s ω, κ (X s ω) (Y s ω)) := fun ω =>
    (hbXc ω).prodMk ((hbYc ω).prodMk (hκc ω))
  have hBBa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s]
      fun ω => (bX s ω, bY s ω, κ (X s ω) (Y s ω)) := fun s =>
    (hbXa s).prodMk ((hbYa s).prodMk (hκ.measurable.comp (hXYa s)))
  let HU : Fin (d + d + 1) → Fin d → ℝ≥0 → Ω → ℝ := fun i j s ω =>
    pack (scol (HX s ω) j) (scol (HY s ω) j) 0 i
  let JU : Fin (d + d + 1) → Fin d → ℝ≥0 → Ω → ℝ := fun i j s ω =>
    pack (WithLp.toLp 2 fun k => JX s ω (k, j)) (WithLp.toLp 2 fun k => JY s ω (k, j)) 0 i
  let bU : Fin (d + d + 1) → ℝ≥0 → Ω → ℝ := fun i s ω =>
    pack (bX s ω) (bY s ω) (κ (X s ω) (Y s ω)) i
  have hHm : ∀ i j s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (HU i j s) :=
    fun i j s => (hcol i j).measurable.comp (hHHa s)
  have hHc : ∀ i j ω, Continuous fun s => HU i j s ω := fun i j ω => (hcol i j).comp (hHH ω)
  have hbm : ∀ i s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (bU i s) :=
    fun i s => (hbf i).measurable.comp (hBBa s)
  have hbc : ∀ i ω, Continuous fun s => bU i s ω := fun i ω => (hbf i).comp (hBB ω)
  have hJ : ∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) (HU i j) (JU i j) := by
    intro i j
    induction i using Fin.lastCases with
    | last =>
      have e1 : HU (Fin.last _) j = fun _ _ => 0 := by
        funext s ω; exact pack_iac _ _ _
      have e2 : JU (Fin.last _) j = fun _ _ => 0 := by
        funext s ω; exact pack_iac _ _ _
      rw [e1, e2]; exact hasBrownianItoIntegral_zero _ _ _
    | cast i' =>
      induction i' using Fin.addCases with
      | left k =>
        have e1 : HU (Fin.castSucc (Fin.castAdd d k)) j = fun s ω => HX s ω (k, j) := by
          funext s ω; exact pack_ixc _ _ _ k
        have e2 : JU (Fin.castSucc (Fin.castAdd d k)) j = fun s ω => JX s ω (k, j) := by
          funext s ω; exact pack_ixc _ _ _ k
        rw [e1, e2]; exact hJX k j
      | right k =>
        have e1 : HU (Fin.castSucc (Fin.natAdd d k)) j = fun s ω => HY s ω (k, j) := by
          funext s ω; exact pack_iyc _ _ _ k
        have e2 : JU (Fin.castSucc (Fin.natAdd d k)) j = fun s ω => JY s ω (k, j) := by
          funext s ω; exact pack_iyc _ _ _ k
        rw [e1, e2]; exact hJY k j
  have hUeq : ∀ᵐ ω ∂P, ∀ (s : ℝ≥0) (i : Fin (d + d + 1)), U s ω i = U 0 ω i +
      (∑ j, JU i j s ω) + ∫ u in (0 : ℝ)..s.val, bU i u.toNNReal ω := by
    filter_upwards [hXeq, hYeq] with ω hx hy s i
    induction i using Fin.lastCases with
    | last =>
      show U s ω iac = U 0 ω iac + (∑ j, JU iac j s ω) + ∫ u in (0 : ℝ)..s.val, bU iac u.toNNReal ω
      simp [U, JU, bU, A]
    | cast i' =>
      induction i' using Fin.addCases with
      | left k =>
        show U s ω (ixc k) = U 0 ω (ixc k) + (∑ j, JU (ixc k) j s ω) +
          ∫ u in (0 : ℝ)..s.val, bU (ixc k) u.toNNReal ω
        simp only [U, JU, bU, pack_ixc]
        exact hx s k
      | right k =>
        show U s ω (iyc k) = U 0 ω (iyc k) + (∑ j, JU (iyc k) j s ω) +
          ∫ u in (0 : ℝ)..s.val, bU (iyc k) u.toNNReal ω
        simp only [U, JU, bU, pack_iyc]
        exact hy s k
  -- the martingale integrals
  have hD1c : Continuous (fderiv ℝ F) :=
    hF.continuous_fderiv two_ne_zero
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ F)) :=
    (hF.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hKf : ∀ (i : Fin (d + d + 1)) (j : Fin d),
      Continuous fun q : (SDEState d × SDEState d × ℝ) × (SDEDiffusion d × SDEDiffusion d) =>
        fderiv ℝ F (pack q.1.1 q.1.2.1 q.1.2.2) (EuclideanSpace.single i 1) *
          pack (scol q.2.1 j) (scol q.2.2 j) 0 i := fun i j =>
    ((hD1c.comp (hpk.comp continuous_fst)).clm_apply continuous_const).mul
      ((hcol i j).comp continuous_snd)
  have hKm : ∀ i j s, Measurable[completedBrownianPast P W (fun _ => x₀) s]
      (fun ω => fderiv ℝ F (U s ω) (EuclideanSpace.single i 1) * HU i j s ω) :=
    fun i j s => (hKf i j).measurable.comp
      (((hXa s).prodMk ((hYa s).prodMk (hAa s))).prodMk (hHHa s))
  have hKc : ∀ i j ω, Continuous
      (fun s => fderiv ℝ F (U s ω) (EuclideanSpace.single i 1) * HU i j s ω) :=
    fun i j ω => (hKf i j).comp (((hXc ω).prodMk ((hYc ω).prodMk (hAc ω))).prodMk (hHH ω))
  choose K hK using fun (i : Fin (d + d + 1)) (j : Fin d) =>
    exists_hasBrownianItoIntegral hW x₀ j (hKm i j) (hKc i j)
  have hito := ito_formula hW x₀ hUm hUc hUa hHm hHc hJ hbm hbc hUeq hF hK t
  have hKb : ∀ i j, ∃ C, ∀ s ω,
      |fderiv ℝ F (U s ω) (EuclideanSpace.single i 1) * HU i j s ω| ≤ C := fun i j => by
    obtain ⟨C, hC⟩ := hFb i j
    exact ⟨C, fun s ω => hC s ω (A s ω) (hA0 s ω)⟩
  have hKi : ∀ i j, Integrable (K i j t) P ∧ ∫ ω, K i j t ω ∂P = 0 := fun i j => by
    obtain ⟨C, hC⟩ := hKb i j
    obtain ⟨h1, -, h3⟩ := ito_integral_memLp_meanZero hW x₀ j (hKm i j) (hKc i j) hC (hK i j) t
    exact ⟨h1.integrable one_le_two, h3⟩
  refine ⟨fun ω => ∑ i, ∑ j, K i j t ω, ?_, ?_, ?_⟩
  · exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hKi i j).1
  · rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hKi i j).1]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hKi i j).1]
    exact Finset.sum_eq_zero fun j _ => (hKi i j).2
  · filter_upwards [hito, hX0, hY0] with ω h hx0 hy0
    have hU0 : F (U 0 ω) = F (pack x0 y0 0) := by
      show F (pack (X 0 ω) (Y 0 ω) (A 0 ω)) = _
      rw [hx0, hy0]
      simp [A]
    show F (U t ω) = F (pack x0 y0 0) + (∑ i, ∑ j, K i j t ω) + _
    rw [h, hU0, add_assoc]
    congr 1
    have hφ : Continuous fun u : ℝ => U u.toNNReal ω := (hUc ω).comp continuous_real_toNNReal
    have hF1c : ∀ i, Continuous fun u : ℝ =>
        fderiv ℝ F (U u.toNNReal ω) (EuclideanSpace.single i 1) * bU i u.toNNReal ω :=
      fun i => ((hD1c.comp hφ).clm_apply continuous_const).mul
        ((hbc i ω).comp continuous_real_toNNReal)
    have hF2c : ∀ i i' j, Continuous fun u : ℝ =>
        fderiv ℝ (fderiv ℝ F) (U u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * HU i j u.toNNReal ω * HU i' j u.toNNReal ω :=
      fun i i' j => ((((hD2c.comp hφ).clm_apply continuous_const).clm_apply
        continuous_const).mul ((hHc i j ω).comp continuous_real_toNNReal)).mul
        ((hHc i' j ω).comp continuous_real_toNNReal)
    have E1 : (∑ i, ∫ u in (0 : ℝ)..t.val,
        fderiv ℝ F (U u.toNNReal ω) (EuclideanSpace.single i 1) * bU i u.toNNReal ω) =
        ∫ u in (0 : ℝ)..t.val, ∑ i,
          fderiv ℝ F (U u.toNNReal ω) (EuclideanSpace.single i 1) * bU i u.toNNReal ω :=
      (intervalIntegral.integral_finsetSum fun i _ => (hF1c i).intervalIntegrable _ _).symm
    have E2 : (∑ i, ∑ i', ∑ j, ∫ u in (0 : ℝ)..t.val,
        fderiv ℝ (fderiv ℝ F) (U u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * HU i j u.toNNReal ω * HU i' j u.toNNReal ω) =
        ∫ u in (0 : ℝ)..t.val, ∑ i, ∑ i', ∑ j,
        fderiv ℝ (fderiv ℝ F) (U u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * HU i j u.toNNReal ω * HU i' j u.toNNReal ω := by
      rw [intervalIntegral.integral_finsetSum fun i _ =>
        (continuous_finsetSum _ fun i' _ => continuous_finsetSum _ fun j _ =>
          hF2c i i' j).intervalIntegrable _ _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [intervalIntegral.integral_finsetSum fun i' _ =>
        (continuous_finsetSum _ fun j _ => hF2c i i' j).intervalIntegrable _ _]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [intervalIntegral.integral_finsetSum fun j _ => (hF2c i i' j).intervalIntegrable _ _]
    have hI1 := (continuous_finsetSum Finset.univ fun i _ => hF1c i).intervalIntegrable
      (μ := volume) 0 t.val
    have hI2 : IntervalIntegrable (fun u : ℝ => (1 / 2 : ℝ) * ∑ i, ∑ i', ∑ j,
        fderiv ℝ (fderiv ℝ F) (U u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * HU i j u.toNNReal ω * HU i' j u.toNNReal ω)
        volume 0 t.val :=
      (continuous_const.mul (continuous_finsetSum Finset.univ fun i _ =>
        continuous_finsetSum Finset.univ fun i' _ => continuous_finsetSum Finset.univ
          fun j _ => hF2c i i' j)).intervalIntegrable _ _
    rw [E1, E2, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hI1 hI2]
    refine intervalIntegral.integral_congr fun u _ => ?_
    exact driftGen_coords F _ _ _ _ _ _ _ _

theorem Gf_integrand_ok (r : ℝ) {X Y : ℝ≥0 → Ω → SDEState d} {HX HY : ℝ≥0 → Ω → SDEDiffusion d}
    (hHb : ∃ C, ∀ s ω, ‖X s ω‖ ^ 2 ≤ r + 1 → ‖HX s ω‖ ≤ C ∧ ‖HY s ω‖ ≤ C) :
    ∀ (i : Fin (d + d + 1)) (j : Fin d), ∃ C, ∀ s ω (a : ℝ), 0 ≤ a →
      |fderiv ℝ (Gf r) (pack (X s ω) (Y s ω) a) (EuclideanSpace.single i 1) *
        pack (scol (HX s ω) j) (scol (HY s ω) j) 0 i| ≤ C := by
  intro i j
  obtain ⟨B, hB0, hB⟩ := Gf_deriv_bound (d := d) r (EuclideanSpace.single i 1)
    (EuclideanSpace.single i 1)
  obtain ⟨C₀, hC₀⟩ := hHb
  refine ⟨B * (2 * |C₀|), fun s ω a ha => ?_⟩
  by_cases hN : r + 1 < ‖X s ω‖ ^ 2
  · have h0 := (Gf_fderiv_zero (r := r) (u := pack (X s ω) (Y s ω) a)
      (by rw [Nxf_pack]; exact hN)).1
    rw [h0]
    simp only [zero_apply, zero_mul, abs_zero]
    exact mul_nonneg hB0 (by positivity)
  · obtain ⟨h1, h2⟩ := hC₀ s ω (not_lt.1 hN)
    have hea := Real.exp_pos (-a)
    have he := Real.exp_le_one_iff.2 (neg_nonpos.2 ha)
    have hd' : |fderiv ℝ (Gf r) (pack (X s ω) (Y s ω) a) (EuclideanSpace.single i 1)| ≤ B := by
      rw [(Gf_fderiv_pack r (X s ω) (Y s ω) a).1]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hea]
      exact (mul_le_of_le_one_left (abs_nonneg _) he).trans ((hB _ _).1)
    have hc := abs_packcol_le (HX s ω) (HY s ω) j i
    have hc' : |pack (scol (HX s ω) j) (scol (HY s ω) j) 0 i| ≤ 2 * |C₀| := by
      have := le_abs_self C₀
      linarith
    rw [abs_mul]
    exact mul_le_mul hd' hc' (abs_nonneg _) hB0

theorem driftH_eq_gen (r κ : ℝ) (σx : SDEDiffusion d) (bx : SDEState d) (σy : SDEDiffusion d)
    (by' : SDEState d) (x y : SDEState d) (a : ℝ) :
    driftH r κ σx bx σy by' x y a = driftGen (Gf r) κ σx bx σy by' x y a := rfl

theorem driftH_kappa (r κ : ℝ) (σx : SDEDiffusion d) (bx : SDEState d) (σy : SDEDiffusion d)
    (by' : SDEState d) (x y : SDEState d) (a : ℝ) :
    driftH r κ σx bx σy by' x y a = driftH r 0 σx bx σy by' x y a - κ * Gf r (pack x y a) := by
  have hs : ∀ c : ℝ, fderiv ℝ (Gf r) (pack x y a) (pack bx by' c) =
      fderiv ℝ (Gf r) (pack x y a) (pack bx by' 0) - c * Gf r (pack x y a) := fun c => by
    have := pack_add_eac bx by' 0 c
    rw [zero_add] at this
    rw [← this, map_add, map_smul, Gf_fderiv_eac, smul_eq_mul]
    ring
  unfold driftH
  rw [hs κ, hs 0]
  ring

/-- Global generator bound for `Gf r` when the coefficients are bounded by `S` on `|x|² ≤ r + 1`. -/
theorem driftH_bound (r S : ℝ) (hS : 0 ≤ S) :
    ∃ B, 0 ≤ B ∧ ∀ κ, 0 ≤ κ → ∀ (σx : SDEDiffusion d) (bx : SDEState d) (σy : SDEDiffusion d)
      (by' : SDEState d) (x y : SDEState d) (a : ℝ),
      (‖x‖ ^ 2 ≤ r + 1 → ‖σx‖ ≤ S ∧ ‖bx‖ ≤ S ∧ ‖σy‖ ≤ S ∧ ‖by'‖ ≤ S) →
      driftH r κ σx bx σy by' x y a ≤ Real.exp (-a) * B := by
  choose B1 hB1 using fun i : Fin (d + d + 1) => Gf_deriv_bound (d := d) r
    (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
  choose B2 hB2 using fun i i' : Fin (d + d + 1) => Gf_deriv_bound (d := d) r
    (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1)
  set T1 : ℝ := ∑ i, B1 i * (2 * S)
  set T2 : ℝ := ∑ i, ∑ i', ∑ _j : Fin d, B2 i i' * (2 * S) * (2 * S)
  have hT1 : 0 ≤ T1 := Finset.sum_nonneg fun i _ => mul_nonneg (hB1 i).1 (by linarith)
  have hT2 : 0 ≤ T2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i' _ =>
    Finset.sum_nonneg fun _ _ => mul_nonneg (mul_nonneg (hB2 i i').1 (by linarith)) (by linarith)
  refine ⟨T1 + 1 / 2 * T2, by positivity, ?_⟩
  intro κ hκ σx bx σy by' x y a hS'
  have hea := Real.exp_pos (-a)
  by_cases hN : r + 1 < ‖x‖ ^ 2
  · obtain ⟨h1, h2⟩ := Gf_fderiv_zero (r := r) (u := pack x y a) (by rw [Nxf_pack]; exact hN)
    unfold driftH
    rw [h1, h2]
    simp only [zero_apply, Finset.sum_const_zero, mul_zero, add_zero]
    exact mul_nonneg hea.le (by linarith)
  · obtain ⟨s1, s2, s3, s4⟩ := hS' (not_lt.1 hN)
    rw [driftH_kappa]
    have hk := mul_nonneg hκ (Gf_nonneg r (pack x y a))
    suffices hsuf : driftH r 0 σx bx σy by' x y a ≤ Real.exp (-a) * (T1 + 1 / 2 * T2) by linarith
    rw [driftH_eq_gen, ← driftGen_coords]
    have hF1 : ∑ i, fderiv ℝ (Gf r) (pack x y a) (EuclideanSpace.single i 1) * pack bx by' 0 i ≤
        Real.exp (-a) * T1 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h : |fderiv ℝ (Gf r) (pack x y a) (EuclideanSpace.single i 1)| ≤
          Real.exp (-a) * B1 i := by
        rw [(Gf_fderiv_pack r x y a).1]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hea]
        exact mul_le_mul_of_nonneg_left ((hB1 i).2 x y).1 hea.le
      have hp := abs_pack0_le bx by' i
      calc _ ≤ |fderiv ℝ (Gf r) (pack x y a) (EuclideanSpace.single i 1) * pack bx by' 0 i| :=
            le_abs_self _
        _ = |fderiv ℝ (Gf r) (pack x y a) (EuclideanSpace.single i 1)| * |pack bx by' 0 i| :=
            abs_mul _ _
        _ ≤ Real.exp (-a) * B1 i * (2 * S) :=
            mul_le_mul h (by linarith) (abs_nonneg _) (mul_nonneg hea.le (hB1 i).1)
        _ = Real.exp (-a) * (B1 i * (2 * S)) := by ring
    have hF2 : ∑ i, ∑ i', ∑ j, fderiv ℝ (fderiv ℝ (Gf r)) (pack x y a)
        (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1) *
          pack (scol σx j) (scol σy j) 0 i * pack (scol σx j) (scol σy j) 0 i' ≤
        Real.exp (-a) * T2 := by
      have e : Real.exp (-a) * T2 = ∑ i, ∑ i', ∑ _j : Fin d,
          Real.exp (-a) * (B2 i i' * (2 * S) * (2 * S)) := by
        simp only [T2, Finset.mul_sum]
      rw [e]
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i' _ =>
        Finset.sum_le_sum fun j _ => ?_
      have hD : |fderiv ℝ (fderiv ℝ (Gf r)) (pack x y a) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1)| ≤ Real.exp (-a) * B2 i i' := by
        rw [(Gf_fderiv_pack r x y a).2]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul,
          abs_of_pos hea]
        exact mul_le_mul_of_nonneg_left ((hB2 i i').2 x y).2 hea.le
      have hc1 := abs_packcol_le σx σy j i
      have hc2 := abs_packcol_le σx σy j i'
      have hc1' : |pack (scol σx j) (scol σy j) 0 i| ≤ 2 * S := by linarith
      have hc2' : |pack (scol σx j) (scol σy j) 0 i'| ≤ 2 * S := by linarith
      calc _ ≤ |fderiv ℝ (fderiv ℝ (Gf r)) (pack x y a) (EuclideanSpace.single i 1)
            (EuclideanSpace.single i' 1) * pack (scol σx j) (scol σy j) 0 i *
              pack (scol σx j) (scol σy j) 0 i'| := le_abs_self _
        _ = |fderiv ℝ (fderiv ℝ (Gf r)) (pack x y a) (EuclideanSpace.single i 1)
            (EuclideanSpace.single i' 1)| * |pack (scol σx j) (scol σy j) 0 i| *
              |pack (scol σx j) (scol σy j) 0 i'| := by rw [abs_mul, abs_mul]
        _ ≤ Real.exp (-a) * B2 i i' * (2 * S) * (2 * S) := by
            have hB20 := (hB2 i i').1
            gcongr
        _ = Real.exp (-a) * (B2 i i' * (2 * S) * (2 * S)) := by ring
    calc _ ≤ Real.exp (-a) * T1 + 1 / 2 * (Real.exp (-a) * T2) :=
          add_le_add hF1 (mul_le_mul_of_nonneg_left hF2 (by norm_num))
      _ = Real.exp (-a) * (T1 + 1 / 2 * T2) := by ring

/-- Clock rate penalising only `X` outside `B_R`. -/
noncomputable def kapX (c M R : ℝ) (x : SDEState d) : ℝ := c + M * distB R x

theorem kapX_nonneg {c M R : ℝ} (hc : 0 ≤ c) (hM : 0 ≤ M) (x : SDEState d) :
    0 ≤ kapX c M R x :=
  add_nonneg hc (mul_nonneg hM (distB_nonneg R x))

theorem kapX_comp_continuous (c M R : ℝ) {α : Type*} [TopologicalSpace α] {x : α → SDEState d}
    (hx : Continuous x) : Continuous fun v => kapX c M R (x v) :=
  continuous_const.add (continuous_const.mul ((distB_continuous R).comp hx))

theorem driftH_le_kap {r c R L B M C : ℝ} {σ₀ : SDEState d → SDEDiffusion d}
    {b₀ : SDEState d → SDEState d} (hC : 0 ≤ C) (hCin : DrHin d C) (hL : 0 ≤ L)
    (hc : C * (1 + L) ^ 2 ≤ c) (hM : 0 < M) (hB : 0 ≤ B) (hr : r = (R + 1) ^ 2 + 1)
    (hLip : ∀ x y : SDEState d, ‖x‖ ≤ R + 3 → ‖y‖ ≤ R + 3 →
      ‖b₀ x - b₀ y‖ ≤ L * ‖x - y‖ ∧ ‖σ₀ x - σ₀ y‖ ≤ L * ‖x - y‖)
    {x y : SDEState d} {σy : SDEDiffusion d} {by' : SDEState d} (a : ℝ) (ha : 0 ≤ a)
    (hBd : ∀ κ, 0 ≤ κ → driftH r κ (σ₀ x) (b₀ x) σy by' x y a ≤ Real.exp (-a) * B)
    {e : ℝ} (he0 : 0 ≤ e)
    (he : ‖y‖ ≤ R + 3 → C * (‖b₀ y - by'‖ ^ 2 + ‖σ₀ y - σy‖ ^ 2) ≤ e) :
    driftH r (kapX c M R x) (σ₀ x) (b₀ x) σy by' x y a ≤
      B * (1 / M) * (Real.exp (-a) * kapX c M R x) + e := by
  have hc0 : 0 ≤ c := le_trans (mul_nonneg hC (sq_nonneg _)) hc
  have hk0 : 0 ≤ kapX c M R x := kapX_nonneg hc0 hM.le x
  have hea := Real.exp_pos (-a)
  have hfirst : 0 ≤ B * (1 / M) * (Real.exp (-a) * kapX c M R x) :=
    mul_nonneg (mul_nonneg hB (one_div_nonneg.2 hM.le)) (mul_nonneg hea.le hk0)
  have herr : 0 ≤ C * (‖b₀ y - by'‖ ^ 2 + ‖σ₀ y - σy‖ ^ 2) := by positivity
  have hkc : C * (1 + L) ^ 2 ≤ kapX c M R x := by
    unfold kapX
    have := mul_nonneg hM.le (distB_nonneg R x)
    linarith
  by_cases hin : ‖x‖ ≤ R + 1
  · have hx2 : ‖x‖ ^ 2 < r := by
      have := pow_le_pow_left₀ (norm_nonneg x) hin 2
      rw [hr]
      linarith
    by_cases hy : ‖y‖ ≤ R + 3
    · have h1 := hCin r (kapX c M R x) L (σ₀ x) (b₀ x) σy by' (σ₀ y) (b₀ y) x y a hx2 hL hk0
        (fun _ => hLip x y (by linarith) hy) hkc
      have he1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 ha)
      have h2 := mul_le_of_le_one_left herr he1
      linarith [he hy]
    · have h4 : 4 < ‖x - y‖ ^ 2 := by
        have := norm_sub_norm_le y x
        rw [norm_sub_rev] at this
        have h2 : 2 < ‖x - y‖ := by linarith
        linarith only [mul_lt_mul'' h2 h2 (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 2)]
      have := driftH_far (σ₀ x) (b₀ x) σy by' a hx2 h4 hk0
      linarith
  · have hd : 1 ≤ distB R x := le_max_of_le_right (by linarith)
    have hkM : M ≤ kapX c M R x := by
      unfold kapX
      have := mul_le_mul_of_nonneg_left hd hM.le
      linarith
    have h1 : 1 ≤ kapX c M R x / M := (one_le_div hM).2 hkM
    have h2 : driftH r (kapX c M R x) (σ₀ x) (b₀ x) σy by' x y a ≤
        B * (1 / M) * (Real.exp (-a) * kapX c M R x) :=
      calc driftH r (kapX c M R x) (σ₀ x) (b₀ x) σy by' x y a ≤ Real.exp (-a) * B := hBd _ hk0
        _ ≤ Real.exp (-a) * B * (kapX c M R x / M) :=
            le_mul_of_one_le_right (mul_nonneg hea.le hB) h1
        _ = B * (1 / M) * (Real.exp (-a) * kapX c M R x) := by ring
    linarith

theorem driftH_continuous' (r : ℝ) {α : Type*} [TopologicalSpace α] {κ a : α → ℝ}
    {σx σy : α → SDEDiffusion d} {bx by' x y : α → SDEState d}
    (hκ : Continuous κ) (hσx : Continuous σx) (hbx : Continuous bx) (hσy : Continuous σy)
    (hby : Continuous by') (hx : Continuous x) (hy : Continuous y) (ha : Continuous a) :
    Continuous fun p => driftH r (κ p) (σx p) (bx p) (σy p) (by' p) (x p) (y p) (a p) := by
  have hD1 : Continuous (fderiv ℝ (Gf (d := d) r)) :=
    (Gf_contDiff r (n := 2)).continuous_fderiv two_ne_zero
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ (Gf (d := d) r))) :=
    ((Gf_contDiff r (n := 2)).fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hpk := pack_continuous hx hy ha
  unfold driftH
  refine ((hD1.comp hpk).clm_apply (pack_continuous hbx hby hκ)).add
    (continuous_const.mul (continuous_finsetSum _ fun j _ => ?_))
  have hv := pack_continuous (scol_continuous hσx j) (scol_continuous hσy j)
    (continuous_const (y := (0 : ℝ)))
  exact ((hD2.comp hpk).clm_apply hv).clm_apply hv

/-- Pathwise: the `Gf`-generator integral is at most `B / M` plus the integrated error. -/
theorem driftH_integral_le {r c R L B M C : ℝ} {σ₀ : SDEState d → SDEDiffusion d}
    {b₀ : SDEState d → SDEState d} (hσ : Continuous σ₀) (hb : Continuous b₀)
    (hC : 0 ≤ C) (hCin : DrHin d C) (hL : 0 ≤ L) (hc : C * (1 + L) ^ 2 ≤ c) (hM : 0 < M)
    (hB : 0 ≤ B) (hr : r = (R + 1) ^ 2 + 1)
    (hLip : ∀ x y : SDEState d, ‖x‖ ≤ R + 3 → ‖y‖ ≤ R + 3 →
      ‖b₀ x - b₀ y‖ ≤ L * ‖x - y‖ ∧ ‖σ₀ x - σ₀ y‖ ≤ L * ‖x - y‖)
    {x y : ℝ → SDEState d} {σy : ℝ → SDEDiffusion d} {by' : ℝ → SDEState d}
    (hx : Continuous x) (hy : Continuous y) (hσy : Continuous σy) (hby : Continuous by')
    (hBd : ∀ u κ, 0 ≤ κ → ∀ a, driftH r κ (σ₀ (x u)) (b₀ (x u)) (σy u) (by' u) (x u) (y u) a ≤
      Real.exp (-a) * B)
    {e : ℝ → ℝ} (hec : Continuous e) (he0 : ∀ u, 0 ≤ e u)
    (he : ∀ u, ‖y u‖ ≤ R + 3 → C * (‖b₀ (y u) - by' u‖ ^ 2 + ‖σ₀ (y u) - σy u‖ ^ 2) ≤ e u)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ u in (0 : ℝ)..t, driftH r (kapX c M R (x u)) (σ₀ (x u)) (b₀ (x u)) (σy u) (by' u)
        (x u) (y u) (∫ v in (0 : ℝ)..((u.toNNReal : ℝ≥0) : ℝ), kapX c M R (x v)) ≤
      B * (1 / M) + ∫ u in (0 : ℝ)..t, e u := by
  have hgc : Continuous fun v => kapX c M R (x v) := kapX_comp_continuous c M R hx
  have hc0 : 0 ≤ c := le_trans (mul_nonneg hC (sq_nonneg _)) hc
  have hpc : Continuous fun u => ∫ v in (0 : ℝ)..u, kapX c M R (x v) :=
    continuous_iff_continuousAt.2 fun u => (hgc.integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt
  have hcongr : ∫ u in (0 : ℝ)..t, driftH r (kapX c M R (x u)) (σ₀ (x u)) (b₀ (x u))
        (σy u) (by' u) (x u) (y u)
        (∫ v in (0 : ℝ)..((u.toNNReal : ℝ≥0) : ℝ), kapX c M R (x v)) =
      ∫ u in (0 : ℝ)..t, driftH r (kapX c M R (x u)) (σ₀ (x u)) (b₀ (x u))
        (σy u) (by' u) (x u) (y u) (∫ v in (0 : ℝ)..u, kapX c M R (x v)) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu0 : 0 ≤ u := by rw [Set.uIcc_of_le ht] at hu; exact hu.1
    simp only [Real.coe_toNNReal _ hu0]
  rw [hcongr]
  have hLc : Continuous fun u => driftH r (kapX c M R (x u)) (σ₀ (x u)) (b₀ (x u))
      (σy u) (by' u) (x u) (y u) (∫ v in (0 : ℝ)..u, kapX c M R (x v)) :=
    driftH_continuous' r hgc (hσ.comp hx) (hb.comp hx) hσy hby hx hy hpc
  have hRc : Continuous fun u => B * (1 / M) *
      (Real.exp (-(∫ v in (0 : ℝ)..u, kapX c M R (x v))) * kapX c M R (x u)) :=
    continuous_const.mul ((Real.continuous_exp.comp hpc.neg).mul hgc)
  calc _ ≤ ∫ u in (0 : ℝ)..t, (B * (1 / M) *
        (Real.exp (-(∫ v in (0 : ℝ)..u, kapX c M R (x v))) * kapX c M R (x u)) + e u) :=
        intervalIntegral.integral_mono_on ht (hLc.intervalIntegrable _ _)
          ((hRc.add hec).intervalIntegrable _ _) fun u hu =>
          driftH_le_kap hC hCin hL hc hM hB hr hLip _
            (intervalIntegral.integral_nonneg hu.1 fun v _ => kapX_nonneg hc0 hM.le _)
            (fun κ hκ => hBd u κ hκ _) (he0 u) (he u)
    _ = B * (1 / M) * (1 - Real.exp (-(∫ v in (0 : ℝ)..t, kapX c M R (x v)))) +
          ∫ u in (0 : ℝ)..t, e u := by
        rw [intervalIntegral.integral_add (hRc.intervalIntegrable _ _) (hec.intervalIntegrable _ _),
          intervalIntegral.integral_const_mul, integral_exp_neg_primitive hgc]
    _ ≤ B * (1 / M) + ∫ u in (0 : ℝ)..t, e u := by
        have h1 := Real.exp_pos (-(∫ v in (0 : ℝ)..t, kapX c M R (x v)))
        have h2 : 0 ≤ B * (1 / M) := mul_nonneg hB (one_div_nonneg.2 hM.le)
        nlinarith

end M10c4

section M10c5
/-! M10c-5: expectation bound for `Gf r` along `(X, Y, A)`, `X` the SDE solution, `Y` a general
Ito process with globally bounded coefficients, clock rate `kapX` (penalising only `X`). -/

set_option maxHeartbeats 1000000 in
theorem lintegral_Gf_le [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    {Y : ℝ≥0 → Ω → SDEState d} {HY JY : ℝ≥0 → Ω → SDEDiffusion d} {bY : ℝ≥0 → Ω → SDEState d}
    (hYm : ∀ s, Measurable (Y s)) (hYc : ∀ ω, Continuous fun s => Y s ω)
    (hYa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (Y s))
    (hHYa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (HY s))
    (hHYc : ∀ ω, Continuous fun s => HY s ω)
    (hbYa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (bY s))
    (hbYc : ∀ ω, Continuous fun s => bY s ω)
    (hJY : ∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) (fun s ω => HY s ω (i, j)) (fun s ω => JY s ω (i, j)))
    (hYeq : ∀ᵐ ω ∂P, ∀ (s : ℝ≥0) i, Y s ω i = Y 0 ω i + (∑ j, JY s ω (i, j)) +
      ∫ u in (0 : ℝ)..s.val, bY u.toNNReal ω i)
    {y0 : SDEState d} (hY0 : ∀ᵐ ω ∂P, Y 0 ω = y0)
    {r c R L B M C S : ℝ} (hC : 0 ≤ C) (hCin : DrHin d C) (hL : 0 ≤ L)
    (hc : C * (1 + L) ^ 2 ≤ c) (hM : 0 < M) (hr : r = (R + 1) ^ 2 + 1)
    (hLip : ∀ x y : SDEState d, ‖x‖ ≤ R + 3 → ‖y‖ ≤ R + 3 →
      ‖b₀ x - b₀ y‖ ≤ L * ‖x - y‖ ∧ ‖σ₀ x - σ₀ y‖ ≤ L * ‖x - y‖)
    (hS0 : ∀ x : SDEState d, ‖x‖ ^ 2 ≤ r + 1 → ‖σ₀ x‖ ≤ S ∧ ‖b₀ x‖ ≤ S)
    (hHY : ∀ s ω, ‖HY s ω‖ ≤ S) (hbY : ∀ s ω, ‖bY s ω‖ ≤ S)
    (hB : 0 ≤ B) (hBd : ∀ κ, 0 ≤ κ → ∀ (σx : SDEDiffusion d) (bx : SDEState d)
      (σy : SDEDiffusion d) (by' : SDEState d) (x y : SDEState d) (a : ℝ),
      (‖x‖ ^ 2 ≤ r + 1 → ‖σx‖ ≤ S ∧ ‖bx‖ ≤ S ∧ ‖σy‖ ≤ S ∧ ‖by'‖ ≤ S) →
      driftH r κ σx bx σy by' x y a ≤ Real.exp (-a) * B)
    {e : ℝ → Ω → ℝ} (hec : ∀ ω, Continuous fun u => e u ω) (he0 : ∀ u ω, 0 ≤ e u ω)
    (he : ∀ u ω, ‖Y u.toNNReal ω‖ ≤ R + 3 →
      C * (‖b₀ (Y u.toNNReal ω) - bY u.toNNReal ω‖ ^ 2 +
        ‖σ₀ (Y u.toNNReal ω) - HY u.toNNReal ω‖ ^ 2) ≤ e u ω)
    (t : ℝ≥0) (hEi : Integrable (fun ω => ∫ u in (0 : ℝ)..t.val, e u ω) P) :
    ∫⁻ ω, ENNReal.ofReal (Gf r (pack (X t ω) (Y t ω)
      (∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω)))) ∂P ≤
      ENNReal.ofReal (Gf r (pack x₀ y0 0) + B * (1 / M) +
        ∫ ω, (∫ u in (0 : ℝ)..t.val, e u ω) ∂P) := by
  obtain ⟨hXm, hXc, hXa, hX0, JX, -, -, hJX, -, hXeq⟩ := hX
  have hc0 : 0 ≤ c := le_trans (mul_nonneg hC (sq_nonneg _)) hc
  have hFb := Gf_integrand_ok (Ω := Ω) r (X := X) (Y := Y) (HX := fun s ω => σ₀ (X s ω)) (HY := HY)
    ⟨S, fun s ω h => ⟨(hS0 _ h).1, hHY s ω⟩⟩
  have hX0' : ∀ᵐ ω ∂P, X 0 ω = x₀ := by filter_upwards [hX0] with ω h using h
  obtain ⟨Z, hZi, hZ0, hZeq⟩ := ito_coupled_F hW x₀ (X := X) (Y := Y)
    (HX := fun s ω => σ₀ (X s ω)) (HY := HY) (JX := JX) (JY := JY)
    (bX := fun s ω => b₀ (X s ω)) (bY := bY) hXm hYm hXc hYc hXa hYa
    (fun s => hσ.measurable.comp (hXa s)) hHYa (fun ω => hσ.comp (hXc ω)) hHYc
    (fun s => hb.measurable.comp (hXa s)) hbYa (fun ω => hb.comp (hXc ω)) hbYc hJX hJY hXeq hYeq
    hX0' hY0 (κ := fun x _ => kapX c M R x) (kapX_comp_continuous c M R continuous_fst)
    (fun x _ => kapX_nonneg hc0 hM.le x) (Gf_contDiff r) hFb t
  refine lintegral_le_of_ito (ae_of_all _ fun ω => Gf_nonneg _ _) hZi hZ0 hZeq
    (ae_of_all _ fun ω => ?_) hEi
  exact driftH_integral_le hσ hb hC hCin hL hc hM hB hr hLip
    (x := fun u => X u.toNNReal ω) (y := fun u => Y u.toNNReal ω)
    (σy := fun u => HY u.toNNReal ω) (by' := fun u => bY u.toNNReal ω)
    ((hXc ω).comp continuous_real_toNNReal) ((hYc ω).comp continuous_real_toNNReal)
    ((hHYc ω).comp continuous_real_toNNReal) ((hbYc ω).comp continuous_real_toNNReal)
    (fun u κ hκ a => hBd κ hκ _ _ _ _ _ _ a
      (fun h => ⟨(hS0 _ h).1, (hS0 _ h).2, hHY _ _, hbY _ _⟩))
    (hec ω) (fun u => he0 u ω) (fun u => he u ω) t.val t.2

theorem measurable_Gf_coupled [MeasurableSpace Ω] {X Y : ℝ≥0 → Ω → SDEState d}
    (hXm : ∀ s, Measurable (X s)) (hYm : ∀ s, Measurable (Y s))
    (hXc : ∀ ω, Continuous fun s => X s ω) (r c M R : ℝ) (t : ℝ≥0) :
    Measurable fun ω => Gf r (pack (X t ω) (Y t ω)
      (∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω))) := by
  have hA : Measurable fun ω => ∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω) :=
    measurable_intervalIntegral_of_continuous _ t
      (fun s _ => (kapX_comp_continuous c M R continuous_id).measurable.comp (hXm s))
      (fun ω => kapX_comp_continuous c M R (hXc ω))
  exact (Gf_contDiff r (n := 0)).continuous.measurable.comp
    ((pack_continuous continuous_fst (continuous_fst.comp continuous_snd)
      (continuous_snd.comp continuous_snd)).measurable.comp
      ((hXm t).prodMk ((hYm t).prodMk hA)))

/-- Markov step: on the event that `X` stays in `B̄_R` up to `t` and `|X_t - Y_t|² > ε`,
`Gf ≥ e^{-ct}(1 - e^{-ε})`. -/
theorem prob_close_le [MeasurableSpace Ω] {P : Measure Ω} {X Y : ℝ≥0 → Ω → SDEState d}
    (hXm : ∀ s, Measurable (X s)) (hYm : ∀ s, Measurable (Y s))
    (hXc : ∀ ω, Continuous fun s => X s ω) {r c M R K ε : ℝ} (hr : r = (R + 1) ^ 2 + 1)
    (hR : 0 ≤ R) (hε : 0 < ε) (t : ℝ≥0)
    (hI : ∫⁻ ω, ENNReal.ofReal (Gf r (pack (X t ω) (Y t ω)
      (∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω)))) ∂P ≤ ENNReal.ofReal K) :
    P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ‖X t ω - Y t ω‖ ^ 2} ≤
      ENNReal.ofReal (K / (Real.exp (-(c * t.val)) * (1 - Real.exp (-ε)))) := by
  set δ : ℝ := Real.exp (-(c * t.val)) * (1 - Real.exp (-ε)) with hδ
  have hε1 : Real.exp (-ε) < 1 := by
    have := Real.exp_lt_exp.2 (show -ε < 0 by linarith)
    simpa using this
  have hδ0 : 0 < δ := mul_pos (Real.exp_pos _) (by linarith)
  have hsub : {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ‖X t ω - Y t ω‖ ^ 2} ⊆
      {ω | ENNReal.ofReal δ ≤ ENNReal.ofReal (Gf r (pack (X t ω) (Y t ω)
        (∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω))))} := by
    intro ω ⟨hS, hQ⟩
    refine ENNReal.ofReal_le_ofReal ?_
    have hA : ∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω) = t.val * c := by
      have : ∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω) =
          ∫ _u in (0 : ℝ)..t.val, c := by
        refine intervalIntegral.integral_congr fun u hu => ?_
        rw [Set.uIcc_of_le t.2] at hu
        have hut : u.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hu.2
        simp only [kapX, distB_eq_zero (hS _ hut), mul_zero, add_zero]
      rw [this, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    rw [hA]
    have hXt : ‖X t ω‖ ^ 2 ≤ r := by
      have := pow_le_pow_left₀ (norm_nonneg _) (hS t le_rfl) 2
      rw [hr]; nlinarith
    simp only [Gf, Nxf_pack, Qf_pack, pack_iac, cutoff_eq_one hXt, one_mul]
    have hψ := psiQ_ge (‖X t ω - Y t ω‖ ^ 2)
    have he : Real.exp (-(‖X t ω - Y t ω‖ ^ 2)) ≤ Real.exp (-ε) :=
      Real.exp_le_exp.2 (by linarith)
    rw [hδ, show t.val * c = c * t.val by ring]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (Gf r (pack (X t ω) (Y t ω)
      (∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω))))) P :=
    (ENNReal.measurable_ofReal.comp (measurable_Gf_coupled hXm hYm hXc r c M R t)).aemeasurable
  have h1 : ENNReal.ofReal δ * P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ‖X t ω - Y t ω‖ ^ 2} ≤
      ENNReal.ofReal K :=
    ((mul_le_mul' le_rfl (measure_mono hsub)).trans
      (mul_meas_ge_le_lintegral₀ hmeas _)).trans hI
  have hne : ENNReal.ofReal δ ≠ 0 := by simpa using hδ0
  calc P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ‖X t ω - Y t ω‖ ^ 2}
      = (ENNReal.ofReal δ)⁻¹ * (ENNReal.ofReal δ *
          P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ‖X t ω - Y t ω‖ ^ 2}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal δ)⁻¹ * ENNReal.ofReal K := mul_le_mul' le_rfl h1
    _ = ENNReal.ofReal (K / δ) := by
        rw [ENNReal.ofReal_div_of_pos hδ0, ENNReal.div_eq_inv_mul]

end M10c5

section M10c5s
/-! s33 STAB: stability in probability of an SDE solution against Ito processes whose
coefficients are close (in mean integrated square, inside `B̄_{R+3}`) to the SDE coefficients. -/

set_option maxHeartbeats 1000000 in
theorem ito_stability [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    {R L S : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hLip : ∀ x y : SDEState d, ‖x‖ ≤ R + 3 → ‖y‖ ≤ R + 3 →
      ‖b₀ x - b₀ y‖ ≤ L * ‖x - y‖ ∧ ‖σ₀ x - σ₀ y‖ ≤ L * ‖x - y‖)
    (hS0 : ∀ x : SDEState d, ‖x‖ ≤ R + 3 → ‖σ₀ x‖ ≤ S ∧ ‖b₀ x‖ ≤ S)
    (t : ℝ≥0) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (Y : ℝ≥0 → Ω → SDEState d) (HY JY : ℝ≥0 → Ω → SDEDiffusion d)
      (bY : ℝ≥0 → Ω → SDEState d) (e : ℝ → Ω → ℝ),
      (∀ s, Measurable (Y s)) → (∀ ω, Continuous fun s => Y s ω) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (Y s)) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (HY s)) →
      (∀ ω, Continuous fun s => HY s ω) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (bY s)) →
      (∀ ω, Continuous fun s => bY s ω) →
      (∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) (fun s ω => HY s ω (i, j)) (fun s ω => JY s ω (i, j))) →
      (∀ᵐ ω ∂P, ∀ (s : ℝ≥0) i, Y s ω i = Y 0 ω i + (∑ j, JY s ω (i, j)) +
        ∫ u in (0 : ℝ)..s.val, bY u.toNNReal ω i) →
      (∀ᵐ ω ∂P, Y 0 ω = x₀) →
      (∀ s ω, ‖HY s ω‖ ≤ S) → (∀ s ω, ‖bY s ω‖ ≤ S) →
      (∀ ω, Continuous fun u => e u ω) → (∀ u ω, 0 ≤ e u ω) →
      (∀ u ω, ‖Y u.toNNReal ω‖ ≤ R + 3 →
        ‖b₀ (Y u.toNNReal ω) - bY u.toNNReal ω‖ ^ 2 +
          ‖σ₀ (Y u.toNNReal ω) - HY u.toNNReal ω‖ ^ 2 ≤ e u ω) →
      Integrable (fun ω => ∫ u in (0 : ℝ)..t.val, e u ω) P →
      ∫ ω, (∫ u in (0 : ℝ)..t.val, e u ω) ∂P ≤ δ →
      P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ‖X t ω - Y t ω‖ ^ 2} ≤ ENNReal.ofReal η := by
  have hS : 0 ≤ S := (norm_nonneg _).trans (hS0 0 (by rw [norm_zero]; linarith)).1
  obtain ⟨C, hC, hCin⟩ := driftH_le_inside (d := d)
  set r : ℝ := (R + 1) ^ 2 + 1 with hr
  set c : ℝ := C * (1 + L) ^ 2 with hc
  obtain ⟨B, hB, hBd⟩ := driftH_bound (d := d) r S hS
  set δ' : ℝ := Real.exp (-(c * t.val)) * (1 - Real.exp (-ε)) with hδ'
  have hδ0 : 0 < δ' := by
    have : Real.exp (-ε) < 1 := by
      have := Real.exp_lt_exp.2 (show -ε < 0 by linarith); simpa using this
    exact mul_pos (Real.exp_pos _) (by linarith)
  set M : ℝ := 2 * B / (η * δ') + 1 with hMdef
  have hM : 0 < M := by positivity
  have hBM : B * (1 / M) ≤ η * δ' / 2 := by
    rw [mul_one_div, div_le_iff₀ hM]
    have : η * δ' / 2 * M = B + η * δ' / 2 := by
      rw [hMdef]; field_simp
    rw [this]; linarith only [mul_pos hη hδ0]
  have hS0' : ∀ x : SDEState d, ‖x‖ ^ 2 ≤ r + 1 → ‖σ₀ x‖ ≤ S ∧ ‖b₀ x‖ ≤ S := fun x hx => by
    refine hS0 x ?_
    by_contra hc'
    have hc'' := not_le.1 hc'
    have h3 : (0 : ℝ) ≤ R + 3 := by linarith only [hR]
    linarith only [mul_lt_mul'' hc'' hc'' h3 h3, hx, hr, hR]
  refine ⟨η * δ' / (2 * (C + 1)), by positivity, ?_⟩
  intro Y HY JY bY e hYm hYc hYa hHYa hHYc hbYa hbYc hJY hYeq hY0 hHY hbY hec he0 he hEi hEδ
  have hEi' : Integrable (fun ω => ∫ u in (0 : ℝ)..t.val, C * e u ω) P := by
    simp_rw [intervalIntegral.integral_const_mul]; exact hEi.const_mul C
  have hI := lintegral_Gf_le hW x₀ hσ hb hX hYm hYc hYa hHYa hHYc hbYa hbYc hJY hYeq hY0 hC hCin hL
    le_rfl hM hr hLip hS0' hHY hbY hB hBd (e := fun u ω => C * e u ω)
    (fun ω => continuous_const.mul (hec ω)) (fun u ω => mul_nonneg hC (he0 u ω))
    (fun u ω hY => mul_le_mul_of_nonneg_left (he u ω hY) hC) t hEi'
  have hP := prob_close_le (P := P) hX.1 hYm hX.2.1 hr hR hε t hI
  refine hP.trans (ENNReal.ofReal_le_ofReal ?_)
  have hG0 : Gf r (pack x₀ x₀ 0) = 0 := by simp [Gf, Qf_pack, psiQ]
  have hCe : ∫ ω, (∫ u in (0 : ℝ)..t.val, C * e u ω) ∂P =
      C * ∫ ω, (∫ u in (0 : ℝ)..t.val, e u ω) ∂P := by
    simp_rw [intervalIntegral.integral_const_mul]; exact integral_const_mul C _
  have hCδ : C * ∫ ω, (∫ u in (0 : ℝ)..t.val, e u ω) ∂P ≤ η * δ' / 2 := by
    calc C * ∫ ω, (∫ u in (0 : ℝ)..t.val, e u ω) ∂P ≤ C * (η * δ' / (2 * (C + 1))) :=
          mul_le_mul_of_nonneg_left hEδ hC
      _ ≤ η * δ' / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith only [mul_pos hη hδ0]
  beta_reduce
  try rw [← hδ']
  rw [div_le_iff₀ hδ0, hG0, hCe]
  linarith

end M10c5s

section M10c6
/-! M10c-6: pathwise error of the truncated Euler scheme: on `[0, T]` the coefficient errors
`s₁(Y_u) - H_u`, `b₁(Y_u) - b_u` are `O(osc_w(h) + h)` (lag start `a = y`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}
  {w : ℝ≥0 → SDEState d}

end M10c6

end ItoLib

-- ===== H =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c7
/-! M10c-7: the Euler scheme's coefficient error `‖s₁(Y_u) - H_u‖`, `‖b₁(Y_u) - b_u‖` is
`≤ 2 L K` with `K = d (3 d S δ + 2 S h)` (`δ` = oscillation of `w` over gaps `≤ h` on `[0, T]`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}
  {w : ℝ≥0 → SDEState d}

end M10c7

section M10c8
/-! M10c-8: the coupled expectation bound `lintegral_Gf_le` with `Y` the truncated Euler scheme
driven by `W` (lag start `a = y = x₀`), `s₁ = σ₀`, `b₁ = b₀` on `B̄_{R+3}`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10c8

section M10c9
/-! M10c-9: `E ∫₀ᵗ eulerErr → 0` along any mesh sequence `hₙ → 0` (globally Lipschitz,
bounded truncated coefficients). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10c9

section M10c10
/-! M10c-10: the truncated Euler scheme converges to the SDE solution in probability on the
event that `X` stays in `B̄_R` (truncation radius `≥ R + 3`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10c10

end ItoLib

-- ===== I =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10d1
/-! M10d-1 (b5 groundwork): the cell noise `ζ_j = (1/h) ∫₀ʰ (W(s+h) - W(s+u)) du`: measurable for
the future-increment σ-algebra (so independent of the completed past), mean zero, `E ζ² ≤ h/2`. -/

end M10d1

section M10d2
/-! M10d-2: one cell of the L² stability estimate: for completed-past-measurable `D` (L²) and
bounded `A, B`, `E‖D + N‖² ≤ E‖D‖² + 2 d h E(‖A‖² + ‖B‖²)` with the cell noise
`N_i = Σⱼ (A_ij ξ_j + B_ij ζ_j)`. -/

end M10d2

end ItoLib

-- ===== J =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10d3
/-! M10d-3 (b5): one full cell of the Euler scheme in cell-noise form, and L² of the grid values. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10d3

end ItoLib

-- ===== K =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10e1
/-! M10e-1 (b6 groundwork): the scheme as a deterministic recursion `zrec` driven by the cell
noises `(ξ_l, ζ_l)`; restart identity `Z_{m+k} = zrec_k(Z_{m-1}, Z_m; noises of cells m, m+1, ...)`;
the noises after cell `m` are measurable for the future-increment σ-algebra. -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)

variable {s₁ b₁ h}

end M10e1

section M10e2
/-! M10e-2 (b6): restart at a grid time. Independence of the past pair `(Z_{m-1}, Z_m)` and the
future noises gives `E f(Z_{m+k}) = E[ E' f(zrec_k(Z_{m-1}, Z_m; noises after m)) ]`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10e2

end ItoLib

-- ===== L =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10e3
/-! M10e-3 (b6): time homogeneity. The restarted Brownian motion is standard; the noises after
cell `m` are the noises of the restarted motion; any two standard Brownian motions have the same
finite-dimensional laws. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10e3

section M10e4
/-! M10e-4 (b6 DONE): restart in law at a grid time: `E f(Z_{m+k}) = E G(Z_{m-1}, Z_m)` with
`G(a, y) = E f(Z_k from (a, y))`. -/

variable [MeasurableSpace Ω] {P : Measure Ω}
variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10e4

end ItoLib

-- ===== M =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10f1
/-! M10f-1 (b7 groundwork): the restart function `G_k(a, y) = E f(Z_k from (a, y))` is Lipschitz
in the initial pair for Lipschitz `f`, uniformly in the mesh (via `euler_stab_exp`). -/

variable [MeasurableSpace Ω] {P : Measure Ω}
variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10f1

end ItoLib

-- ===== N =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10f2
/-! M10f-2 (b7): uniform smallness of Euler cell increments, and the exit probability
`P(path leaves B̄_R before T) → 0`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {w : ℝ≥0 → SDEState d}

variable [MeasurableSpace Ω]

end M10f2

section M10f3
/-! M10f-3 (b7): the Euler scheme approximates `X_T` in law, up to the exit probability. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10f3

section M10f4
/-! M10f-4 (b7): the real-analysis wrap-up of the Chapman-Kolmogorov limit
(reverse Fatou in `n`, dominated convergence in `R`). -/

variable [MeasurableSpace Ω]

end M10f4

section M10f5
/-! M10f-5 (b7): the restart function `eulerG`, its bound and uniform Lipschitz property, and the
approximation `eulerG(y, y) ≈ E f(X^y_t)` up to the exit probability. -/

variable [MeasurableSpace Ω]

variable {P : Measure Ω} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10f5

section M10f6
/-! M10f-6 (b7 DONE): Chapman-Kolmogorov in integrated form for bounded Lipschitz test functions,
with a measurable version `g` of `y ↦ E f(X^y_t)`. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10f6

end ItoLib

-- ===== O =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10g
/-! M10g: from integrated Chapman-Kolmogorov identities for thickened indicators (bounded
Lipschitz test functions) to a Markov kernel and set-wise Chapman-Kolmogorov. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10g

end ItoLib

-- ===== P =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10h
/-! M10h (b9/b11): local Lipschitz on compact sets, coordinate clamps, truncation families,
and the Kolmogorov coefficients. -/

variable {d : ℕ}

end M10h

section M10i
open StochKolmogorov.Persist
variable {n : ℕ}

end M10i

section M10j
open StochKolmogorov.Persist
variable {n : ℕ}

end M10j

end ItoLib

-- ===== Q =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10k
/-! M10k (b10 calculus): the cubic negative part `φ(v) = (v⁻)³` (C², `v φ' = 3φ`, `v² φ'' = 6φ`)
and the orthant test function `Hf r u = e^{-a} χ_r(|x|²) Σ_k φ(x_k)`. -/

variable {d : ℕ}

end M10k

section M10l
/-! M10l (b10 drift): generator of `Hf r` inside the ball and its global bound. -/
variable {d : ℕ}

end M10l

section M10m
/-! M10m (b10 expectation): `E Hf_r(X_t) ≤ Hf_r(x₀) + B/M` along `(X, X, A)`. -/
variable {Ω : Type*} {d : ℕ}

end M10m

end ItoLib

-- ===== R =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10n
/-! M10n (b10 expectation and Markov step): `E Hf_r(X_t, A_t) ≤ Hf_r(x₀) + B/M`, and
`P{X stays in B̄_R on [0,t], ε < Φ(X_t)} ≤ (Hf_r(x₀) + B/M) / (e^{-ct} ε)`. -/
variable {Ω : Type*} {d : ℕ}

end M10n

end ItoLib

-- ===== S =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10o
/-! M10o (b10 done): orthant invariance of the Kolmogorov solutions, and the Markov statement. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M10o

end ItoLib

-- ===== V =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M11c
/-! M11c: the orthant test-function machinery of Q.lean/R.lean with a general family of C²
nonnegative coordinate functions `φ k` in place of `(v⁻)³`. -/

variable {Ω : Type*} {d : ℕ}

variable {φ : Fin d → ℝ → ℝ} [hφ : Fact (∀ k, ContDiff ℝ 2 (φ k))]
  [hφ0 : Fact (∀ k v, 0 ≤ φ k v)]

end M11c

end ItoLib

-- ===== W =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M11d
/-! M11d (lemma_3_1 clause 3, interior part): a solution started with `x_k > 0` has `X_t k ≠ 0`
almost surely at every fixed time. Test function `φ_δ(v) = 1/(v² + δ)`, with
`|φ_δ'(v) v| ≤ 2 φ_δ(v)` and `φ_δ''(v) v² ≤ 8 φ_δ(v)`. -/
open StochKolmogorov.Persist

variable {δ : ℝ}

variable {n : ℕ}

end M11d

end ItoLib

-- ===== TA =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section TA
/-! TA (s31): universe-polymorphic Markov statement (Ω : Type*), for the theorem_1_1 glue. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end TA

end ItoLib

-- ===== TC =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section TC
/-! TC (s31): the new child `StochKolmogorov.Persist.markov_property` of the theorem_1_1 reduction. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end TC

end ItoLib

open MeasureTheory ProbabilityTheory Filter in
open scoped ENNReal NNReal Topology BigOperators in
open EthierKurtz in
set_option maxHeartbeats 1000000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    {R L S : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hLip : ∀ x y : SDEState d, ‖x‖ ≤ R + 3 → ‖y‖ ≤ R + 3 →
      ‖b₀ x - b₀ y‖ ≤ L * ‖x - y‖ ∧ ‖σ₀ x - σ₀ y‖ ≤ L * ‖x - y‖)
    (hS0 : ∀ x : SDEState d, ‖x‖ ≤ R + 3 → ‖σ₀ x‖ ≤ S ∧ ‖b₀ x‖ ≤ S)
    (t : ℝ≥0) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (Y : ℝ≥0 → Ω → SDEState d) (HY JY : ℝ≥0 → Ω → SDEDiffusion d)
      (bY : ℝ≥0 → Ω → SDEState d) (e : ℝ → Ω → ℝ),
      (∀ s, Measurable (Y s)) → (∀ ω, Continuous fun s => Y s ω) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (Y s)) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (HY s)) →
      (∀ ω, Continuous fun s => HY s ω) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (bY s)) →
      (∀ ω, Continuous fun s => bY s ω) →
      (∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) (fun s ω => HY s ω (i, j)) (fun s ω => JY s ω (i, j))) →
      (∀ᵐ ω ∂P, ∀ (s : ℝ≥0) i, Y s ω i = Y 0 ω i + (∑ j, JY s ω (i, j)) +
        ∫ u in (0 : ℝ)..s.val, bY u.toNNReal ω i) →
      (∀ᵐ ω ∂P, Y 0 ω = x₀) →
      (∀ s ω, ‖HY s ω‖ ≤ S) → (∀ s ω, ‖bY s ω‖ ≤ S) →
      (∀ ω, Continuous fun u => e u ω) → (∀ u ω, 0 ≤ e u ω) →
      (∀ u ω, ‖Y u.toNNReal ω‖ ≤ R + 3 →
        ‖b₀ (Y u.toNNReal ω) - bY u.toNNReal ω‖ ^ 2 +
          ‖σ₀ (Y u.toNNReal ω) - HY u.toNNReal ω‖ ^ 2 ≤ e u ω) →
      Integrable (fun ω => ∫ u in (0 : ℝ)..t.val, e u ω) P →
      ∫ ω, (∫ u in (0 : ℝ)..t.val, e u ω) ∂P ≤ δ →
      P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ‖X t ω - Y t ω‖ ^ 2} ≤ ENNReal.ofReal η := by
  exact ItoLib.ito_stability hW x₀ hσ hb hX hR hL hLip hS0 t hε hη
