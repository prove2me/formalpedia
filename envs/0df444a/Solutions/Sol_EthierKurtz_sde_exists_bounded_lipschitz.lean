-- Prove2me | solution 1 for EthierKurtz.sde_exists_bounded_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T05:06:21.773225+00:00
-- url     : https://prove2.me/submissions/e76eb4eb-a418-4e37-b935-d323695376f1

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Theorems.Thm_EthierKurtz_brownian_ito_integral_and_formula
import Theorems.Thm_EthierKurtz_brownian_ito_integral_locality_and_continuity

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators


-- ===== ItoM1 =====
section FlatM_ItoM1

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
    nlinarith
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ := Set.mem_iUnion.1 (hall n)
  have := hδuc (dyTime t p.1.1 p.1.2) ⟨zero_le, dyTime_le t hp1⟩
    (dyTime t p.2.1 p.2.2) ⟨zero_le, dyTime_le t hp2⟩
    (by rw [NNReal.dist_eq]; exact lt_of_le_of_lt hp3 htn)
  rw [Real.dist_eq] at this
  linarith

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
    rw [div_le_iff₀ ht]; nlinarith [hu.2]
  have hc1 : 0 < ⌈u * 2 ^ n / t.val⌉₊ := Nat.ceil_pos.2 hx0
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = ⌈u * 2 ^ n / t.val⌉₊ := ⟨⌈u * 2 ^ n / t.val⌉₊ - 1, by omega⟩
  have hkR : (k : ℝ) + 1 = ⌈u * 2 ^ n / t.val⌉₊ := by exact_mod_cast hk
  have hlt : (k : ℝ) < u * 2 ^ n / t.val := by
    have := Nat.ceil_lt_add_one hx0.le; linarith
  have hge : u * 2 ^ n / t.val ≤ (k : ℝ) + 1 := by rw [hkR]; exact Nat.le_ceil _
  have hk2 : k < 2 ^ n := by
    have : ⌈u * 2 ^ n / t.val⌉₊ ≤ 2 ^ n := Nat.ceil_le.2 (by exact_mod_cast hxle)
    omega
  have hlo : (k : ℝ) * t.val / 2 ^ n < u := by
    rw [div_lt_iff₀ h2]; rw [lt_div_iff₀ ht] at hlt; linarith
  have hhi : u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n := by
    rw [le_div_iff₀ h2]; rw [div_le_iff₀ ht] at hge; linarith
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
      linarith
    · have hl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hl
      have : ((k : ℝ) + 1) * t.val / 2 ^ n ≤ (l : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      linarith
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
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) ht)
      (by positivity)
  have hs_ge : ∀ m, (dyTime t n k : ℝ) ≤ (s m : ℝ) := fun m => by
    have hkm : ((k * 2 ^ m : ℕ) : ℝ) ≤ y m := by
      push_cast
      simp only [hy]
      rw [le_div_iff₀ hpos, pow_add]
      rw [div_le_iff₀ (by positivity)] at hlo
      nlinarith [pow_pos (two_pos (α := ℝ)) m]
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
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hs_ge m])]
      have : ((k : ℝ) + 1) * t.val / 2 ^ n - (k : ℝ) * t.val / 2 ^ n = t.val / 2 ^ n := by ring
      have := hs_le m
      rw [hdk]
      show (s m : ℝ) - (k : ℝ) * t.val / 2 ^ n ≤ t.val / 2 ^ n
      linarith
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
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hT) h2.le
  have hbT : ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n ≤ t.val := by
    rw [div_le_iff₀ h2]
    have := mul_le_mul_of_nonneg_right hk' hT
    linarith
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
  nlinarith [mul_nonneg hε.le ht]

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

end M8g4

section M8g5
variable [MeasurableSpace Ω]

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end M9c

section M9cF
/-! The concrete test function on `SDEState (d + d + 1)` = (x, y, a). -/

end M9cF


section M9c2
/-! Packing `(x, y, a)` into `SDEState (d + d + 1)` and the structure of `Ff`. -/

end M9c2


section M9d
/-! The generator of `Ff` along the coupled pair (x, y, a) and its sign inside the ball. -/

end M9d


section M9d2
/-! Global bounds for the generator and the integrands (compact support of `Ff` in (x, y)). -/

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

end M9e1


section M9e2
/-! Ito formula for `Ff r (X, Y, A)` and pathwise uniqueness for time-homogeneous, locally
Lipschitz coefficients (no stopping times: localization through the rate `kap`). -/

end M9e2


end ItoLib

end FlatM_ItoM1
-- ===== E =====
section FlatM_E
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

end M10b4a


section M10b4b
/-! M10b-4 (b): pathwise bounds for the generator `driftG` when `X` has coefficients
`σ₀(X), b₀(X)` and `Y` has arbitrary coefficients `σy, by'`. -/

end M10b4b

end ItoLib

end FlatM_E
-- ===== F =====
section FlatM_F
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

end M10c1

section M10c2
/-! M10c-2: the generator of `Gf r` along `(X, Y, A)` and its form inside the `x`-ball. -/

end M10c2

section M10c3
/-! M10c-3: pointwise bounds for the generator `driftH` of `Gf r`. -/

end M10c3

end ItoLib

end FlatM_F
-- ===== G =====
section FlatM_G
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c4
/-! M10c-4: the Ito formula along `(X, Y, A)` for an arbitrary `C²` test function `F` whose
martingale integrands are bounded (`ito_coupled_F`); applied to `Gf r`. -/

end M10c4


section M10c5
/-! M10c-5: expectation bound for `Gf r` along `(X, Y, A)`, `X` the SDE solution, `Y` a general
Ito process with globally bounded coefficients, clock rate `kapX` (penalising only `X`). -/

end M10c5


section M10c6
/-! M10c-6: pathwise error of the truncated Euler scheme: on `[0, T]` the coefficient errors
`s₁(Y_u) - H_u`, `b₁(Y_u) - b_u` are `O(osc_w(h) + h)` (lag start `a = y`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}
  {w : ℝ≥0 → SDEState d}

end M10c6

end ItoLib

end FlatM_G
-- ===== H =====
section FlatM_H
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

end FlatM_H
-- ===== I =====
section FlatM_I
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

end FlatM_I
-- ===== J =====
section FlatM_J
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

end FlatM_J
-- ===== K =====
section FlatM_K
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

end FlatM_K
-- ===== L =====
section FlatM_L
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

end FlatM_L
-- ===== CB =====
section FlatM_CB
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CB (CORE route C2, s22): Cameron-Martin shift formula for centered Gaussians, one-dimensional
and for finite independent families (`Measure.pi`). -/

end ItoLib

end FlatM_CB
-- ===== CC =====
section FlatM_CC
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C2b
/-! CORE route C2b (s23): one-cell Cameron-Martin for the cell noise `(ξ, ζ)` with a constant shift:
weighting by `cmwPi h u ξ` and shifting `(ξ, ζ) ↦ (ξ + u, ζ + u/2)` preserves the law.
Route: dyadic increments are i.i.d. `N(0, h/2^n)` (`dInc_law`), the dyadic approximation of the
noise is a linear function `psiN` of them (`apx_eq_psiN`), finite-dimensional Cameron-Martin
(`gauss_pi_shift`) at each level, then the limit `n → ∞`. -/

end C2b

end ItoLib

end FlatM_CC
-- ===== CD =====
section FlatM_CD
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C3
/-! CORE route C3 (s23): adapted discrete Girsanov over the cells. The first `k` cell noises have
law `ν_k = ν_{k-1} ⊗ ν_1` (independence of the past and time homogeneity); shifting cell `l` by
`(u_l, u_l/2)` with `u_l` a measurable function of the earlier noises and weighting by
`∏ cmwPi h u_l ξ_l` preserves `ν_k` (`girsanov_cells`). -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end C3

end ItoLib

end FlatM_CD
-- ===== CE =====
section FlatM_CE
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {d : ℕ}

section C4a
/-! CORE route C4a (s23): the steered coupling, deterministic part. Two copies of the scheme are run
on one noise sequence; the second copy uses the shifted noise `n + (u, u/2)` with the adapted
steering `u_l = J(Ŷ pair)((X_l - Ŷ_l)/(m - l))`. The shift adds `avgApply p u` to a step
(`zstep_shift`), so with a right inverse `J` of `avgApply` the step adds `(X_l - Ŷ_l)/(m - l)`
(`cstep_steer`). The steered copy is the plain scheme driven by `shV (steerN ..)` (`shV_crec`). -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)

variable (J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)) (m : ℕ)

variable {s₁ b₁ h J m}

end C4a

end ItoLib

end FlatM_CE
-- ===== CF =====
section FlatM_CF
open Filter Set
open scoped BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CORE route C4b (s23): the steered second-moment recursion. If
`e_{k+1} ≤ (1 - 1/(m-k))² e_k + c h (e_k + e_{k-1})` (with `e_{-1}` given by `e' 0`), then
`e_k ≤ G ((m-k)/m)² (1 + 13 c h)^k` for `k < m`. Key fact: `(j+1)² + (j+2)² ≤ 13 j²` for `j ≥ 1`. -/

end ItoLib

end FlatM_CF
-- ===== CG =====
section FlatM_CG
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C4c
/-! CORE route C4c (s24): the steered coupling driven by a Brownian motion. Past-measurability of
the coupled chain, the one-step identity `D_{k+1} = (1 - 1/(m-k)) D_k + h/2 Δb + cellNoise`,
and the second-moment step feeding `steer_rec` (CF.lean). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C4c

end ItoLib

end FlatM_CG
-- ===== CH =====
section FlatM_CH
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
variable {Ω : Type*}

section C4d
/-! CORE route C4d (s24): lower bound of a weighted event by the relative entropy, with no second
moment of the Girsanov martingale. If `f > 0`, `E f ≤ 1` and `E[-log f] ≤ K`, then
`E[1_E f] ≥ e^{-a} (P E - (K+1)/a)` (Markov on `-log f + f ≥ (-log f)⁺`). -/

end C4d

section C4d2
/-! C4d (s25): the relative entropy of the steering weight. -/
open EthierKurtz

variable {d : ℕ} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C4d2

end ItoLib

end FlatM_CH
-- ===== CI =====
section FlatM_CI
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace
set_option autoImplicit false

namespace ItoLib

section C5a
/-! CORE route C5a (s25): Kolmogorov's maximal inequality in the abstract form needed for the
exit estimate of the Euler chain. The only probabilistic input is the orthogonality of the
"stopped" value `1_{F_k} M_k` to the remaining increment `M_m - M_k`. -/

variable {Ω : Type*} {d : ℕ}

end C5a

end ItoLib

end FlatM_CI
-- ===== CK =====
section FlatM_CK
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5c
/-! CORE route C5c (s26): exit estimate for the Euler chain with bounded coefficients.
`Z_k = Z_0 + M_k + D_k` with `M` the martingale part (orthogonal cell increments) and `D` the
drift part (`‖D_k‖ ≤ k h S`); Kolmogorov's maximal inequality on `M` gives
`(δ/2)^2 P(∃ k ≤ m, ‖Z_k - Z_0‖ ≥ δ) ≤ 16 d S^2 m h` once `m h S ≤ δ/2`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end C5c
end ItoLib

end FlatM_CK
-- ===== CL =====
section FlatM_CL
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5d
/-! CORE route C5d (s26): a global, measurable, bounded right inverse of `avgApply` for diffusions
of the form `s x (i, j) = a i x * Γ j i` (the Kolmogorov diffusion read through a projection),
when `Γ` is invertible and `|a i x + a i y| ≥ κ > 0`. -/

variable {d : ℕ}

end C5d
end ItoLib

end FlatM_CL
-- ===== M =====
section FlatM_M
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

end FlatM_M
-- ===== N =====
section FlatM_N
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

end FlatM_N
-- ===== O =====
section FlatM_O
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

end FlatM_O
-- ===== P =====
section FlatM_P
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

end FlatM_P
-- ===== CM =====
section FlatM_CM
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5dK
/-! CORE route C5d, Kolmogorov instance (s26): the coefficients read through the box clamp
`boxP α β` (box `[α, β]^n` inside the open orthant) are globally Lipschitz and bounded, have the
form `s x (i, j) = aK i x * Γ j i`, and `|aK i x + aK i y| ≥ κ > 0` (Assumption 1.1 part 1). -/

variable {n : ℕ}

open StochKolmogorov.Persist

end C5dK
end ItoLib

end FlatM_CM
-- ===== CN =====
section FlatM_CN
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5g
/-! CORE route, s27: (1) `Γ` is invertible under Assumption 1.1 part 1; (2) a generic discrete
martingale `gmart` built from bounded past-measurable cell coefficients: measurability, second
moment, orthogonality and the Kolmogorov maximal inequality (used for the tracking estimate of
the steered chain). -/

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d} {h : ℝ≥0} {A B : ℕ → Ω → SDEDiffusion d}

end C5g
end ItoLib

end FlatM_CN
-- ===== QA =====
section FlatM_QA
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QA
/-! lemma_3_1 (aaf23e78) toolkit, part QA: continuous versions of Ito integrals.
Dyadic grid `gpt m l = l / 2^m`, the horizon-free step integral `stepM` (mesh `2^{-q}` on
`[0,q]`), its values at finer grid points, and a continuous-time maximal inequality for
differences of step integrals (via `gmart_max`). -/

end QA
end ItoLib

end FlatM_QA
-- ===== QB =====
section FlatM_QB
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QB
/-! lemma_3_1 toolkit, part QB: uniform `L²`-continuity of a bounded continuous integrand, and
the pathwise identification of `stepM q t` as the limit of `t`-grid Riemann sums whose
coefficients are the level-`q` left values (grid comparison, step 1). -/

end QB
end ItoLib

end FlatM_QB
-- ===== QC =====
section FlatM_QC
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QC
/-! lemma_3_1 toolkit, part QC: grid comparison in `L²` and `stepM q t → J t` in probability
for every fixed `t` (bounded continuous adapted integrand). -/

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d}

end QC
end ItoLib

end FlatM_QC
-- ===== QD =====
section FlatM_QD
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QDan
/-! Pure analysis: a sequence of continuous functions with geometrically small successive
differences on growing intervals converges pointwise to a continuous limit. -/

theorem geom_cauchy_limit {F : ℕ → ℝ≥0 → ℝ} (hF : ∀ k, Continuous (F k)) {K : ℕ}
    (hK : ∀ k, K ≤ k → ∀ t : ℝ≥0, t ≤ k → |F (k + 1) t - F k t| ≤ (1 / 2 : ℝ) ^ k) :
    (∀ t, CauchySeq fun k => F k t) ∧
    (∀ (t : ℝ≥0) (m : ℕ), K ≤ m → t ≤ m →
      |F m t - limUnder atTop (fun k => F k t)| ≤ 2 * (1 / 2 : ℝ) ^ m) ∧
    Continuous (fun t => limUnder atTop fun k => F k t) := by
  have hstep : ∀ (t : ℝ≥0) (m : ℕ), K ≤ m → t ≤ m → ∀ n : ℕ,
      dist (F (n + m) t) (F (n + 1 + m) t) ≤ 2 * (1 / 2 : ℝ) ^ m / 2 / 2 ^ n := by
    intro t m hKm htm n
    rw [dist_comm, Real.dist_eq, show n + 1 + m = n + m + 1 by omega]
    have h1 := hK (n + m) (by omega) t (htm.trans (by exact_mod_cast Nat.le_add_left m n))
    have h2 : (1 / 2 : ℝ) ^ (n + m) = 2 * (1 / 2 : ℝ) ^ m / 2 / 2 ^ n := by
      rw [pow_add, div_pow, one_pow]; field_simp
    linarith
  have hcau : ∀ t, CauchySeq fun k => F k t := by
    intro t
    set m := max K ⌈t⌉₊
    have htm : t ≤ (m : ℝ≥0) := (Nat.le_ceil t).trans (by exact_mod_cast le_max_right K ⌈t⌉₊)
    exact (cauchySeq_shift m).1 (cauchySeq_of_le_geometric_two (C := 2 * (1 / 2 : ℝ) ^ m)
      (hstep t m (le_max_left _ _) htm))
  have hbd : ∀ (t : ℝ≥0) (m : ℕ), K ≤ m → t ≤ m →
      |F m t - limUnder atTop (fun k => F k t)| ≤ 2 * (1 / 2 : ℝ) ^ m := by
    intro t m hKm htm
    have hlim : Tendsto (fun n => F (n + m) t) atTop (𝓝 (limUnder atTop fun k => F k t)) :=
      (hcau t).tendsto_limUnder.comp (tendsto_add_atTop_nat m)
    have := dist_le_of_le_geometric_two_of_tendsto (C := 2 * (1 / 2 : ℝ) ^ m)
      (hstep t m hKm htm) hlim 0
    simpa [Real.dist_eq] using this
  refine ⟨hcau, hbd, ?_⟩
  refine continuous_iff_continuousAt.2 fun t0 => ?_
  refine continuousAt_of_locally_uniform_approx_of_continuousAt fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨n0, hn0⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1 / 2 : ℝ) < 1)
  set m := max (max K (⌈t0⌉₊ + 1)) n0
  refine ⟨{t | t < ((⌈t0⌉₊ + 1 : ℕ) : ℝ≥0)}, ?_, F m, (hF m).continuousAt, fun y hy => ?_⟩
  · refine (isOpen_lt continuous_id continuous_const).mem_nhds ?_
    show t0 < ((⌈t0⌉₊ + 1 : ℕ) : ℝ≥0)
    exact (Nat.le_ceil t0).trans_lt (by exact_mod_cast Nat.lt_succ_self _)
  · apply hεu
    have hym : y ≤ (m : ℝ≥0) := (le_of_lt hy).trans (by
      exact_mod_cast (le_max_right K (⌈t0⌉₊ + 1)).trans (le_max_left _ n0))
    have h1 := hbd y m ((le_max_left _ _).trans (le_max_left _ _)) hym
    have h2 : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ n0 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right _ _)
    rw [dist_comm, Real.dist_eq]
    linarith

end QDan

section QD

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d}

/-- **Continuous version of the Ito integral** of a bounded continuous adapted integrand. -/
theorem contIto_bdd (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ}
    (hC : ∀ s ω, |H s ω| ≤ C) :
    ∃ Jc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Jc t ω) ∧
      (∀ t, Measurable[completedBrownianPast P W (fun _ => x₀) t] (Jc t)) ∧
      (∀ t, Measurable (Jc t)) ∧ (∀ ω, Jc 0 ω = 0) ∧
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H Jc := by
  exact (EthierKurtz.brownian_ito_integral_locality_and_continuity hW x₀).2.2.1 j H hHm hHa hHc C hC
end QD

end ItoLib

end FlatM_QD
-- ===== Q =====
section FlatM_Q
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

end FlatM_Q
-- ===== R =====
section FlatM_R
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

end FlatM_R
-- ===== S =====
section FlatM_S
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

end FlatM_S
-- ===== U =====
section FlatM_U
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M11a
/-! M11a (lemma_3_1 clause 2): pathwise uniqueness for all times at once, and for the Kolmogorov
system. -/

theorem denseRange_rat_toNNReal : DenseRange fun q : ℚ => (q : ℝ).toNNReal := by
  have hs : DenseRange Real.toNNReal := Function.Surjective.denseRange fun x =>
    ⟨(x : ℝ), Real.toNNReal_coe⟩
  exact hs.comp Rat.denseRange_cast continuous_real_toNNReal

open StochKolmogorov.Persist

end M11a

section M11b
/-! M11b (lemma_3_1 clause 4a): `H < ∞`, i.e. `bracket35` is bounded above on the orthant. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M11b

end ItoLib

end FlatM_U
-- ===== QE =====
section FlatM_QE
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QEneg
variable {Ω : Type*} [MeasurableSpace Ω]

end QEneg

section QEF

end QEF

section QEface
open StochKolmogorov.Persist
variable {n : ℕ}

end QEface

end ItoLib

end FlatM_QE
-- ===== QF =====
section FlatM_QF
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QFgen
/-! Generic test function `F(x,y,a) = e^{-a} G(y)` along `(X, Y, A)`. -/
variable {d : ℕ}

end QFgen

section QFsat
/-! The concave saturation `h_m(u) = ∫₀ᵘ (1 - st(s - m)) ds`. -/

end QFsat

section QFell
/-! The logarithm `ℓ = log(1 + cᵀy) - Σ pᵢ log yᵢ` of `V`, its line derivatives, and bounds. -/
variable {n : ℕ}
open StochKolmogorov.Persist

end QFell

section QFalg
variable {n : ℕ}
open StochKolmogorov.Persist

end QFalg

section QFgenL
variable {n : ℕ}
open StochKolmogorov.Persist

end QFgenL

end ItoLib

end FlatM_QF
-- ===== QG =====
section FlatM_QG
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
open StochKolmogorov.Persist

section QG
/-! Clause 4b (3.6) of Lemma 3.1: `E V^δ₀(X_t) ≤ e^{δ₀ H t} V^δ₀(x)`. -/
variable {n : ℕ}

end QG

end ItoLib

end FlatM_QG
-- ===== QH =====
section FlatM_QH
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QH
/-! Clause 1 toolkit (E1): the Ito isometry as an upper bound, `E J_t² ≤ E ∫₀ᵗ H²`. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

set_option maxHeartbeats 1000000 in
/-- Ito isometry (upper bound) for the difference of two Ito integrals. -/
theorem ito_sq_le2 {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H J H₁ J₁ : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ} (hC : ∀ s ω, |H s ω| ≤ C)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J)
    (hHm₁ : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H₁ s))
    (hHc₁ : ∀ ω, Continuous fun s => H₁ s ω) (hC₁ : ∀ s ω, |H₁ s ω| ≤ C)
    (hJ₁ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H₁ J₁) (t : ℝ≥0) :
    ∫ ω, (J t ω - J₁ t ω) ^ 2 ∂P ≤
      ∫ ω, (∫ u in (0 : ℝ)..t.val, (H u.toNNReal ω - H₁ u.toNNReal ω) ^ 2) ∂P := by
  exact (EthierKurtz.brownian_ito_integral_locality_and_continuity hW x₀).2.1 j H J H₁ J₁ hHm hHc C hC hJ hHm₁ hHc₁ hC₁ hJ₁ t
end QH

end ItoLib

end FlatM_QH
-- ===== QI =====
section FlatM_QI
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QI
/-! Clause 1 toolkit (E3): weak maximal inequality for continuous versions of Ito integrals. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

set_option maxHeartbeats 1000000 in
/-- **Weak maximal inequality** for the difference of continuous versions of two Ito integrals
of bounded continuous adapted integrands, with a uniform `L²` bound `β` on the difference of
the integrands over `[0, N]`. -/
theorem contIto_max {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H H₁ J J₁ : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ}
    (hC : ∀ s ω, |H s ω| ≤ C)
    (hHm₁ : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H₁ s))
    (hHa₁ : ∀ s, Measurable (H₁ s)) (hHc₁ : ∀ ω, Continuous fun s => H₁ s ω) {C₁ : ℝ}
    (hC₁ : ∀ s ω, |H₁ s ω| ≤ C₁)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J)
    (hJ₁ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H₁ J₁)
    (hJc : ∀ ω, Continuous fun t => J t ω) (hJc₁ : ∀ ω, Continuous fun t => J₁ t ω)
    {N : ℕ} {β : ℝ} (hβ : ∀ s : ℝ≥0, s ≤ N → ∫ ω, (H s ω - H₁ s ω) ^ 2 ∂P ≤ β)
    {lam : ℝ} (hlam : 0 < lam) :
    lam ^ 2 * P.real {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |J t ω - J₁ t ω|} ≤ 2 * d * N * β := by
  exact (EthierKurtz.brownian_ito_integral_locality_and_continuity hW x₀).2.2.2 j H H₁ J J₁ hHm hHa hHc C hC hHm₁ hHa₁ hHc₁ C₁ hC₁ hJ hJ₁ hJc hJc₁ N β hβ lam hlam
end QI
end ItoLib

end FlatM_QI
-- ===== QJ =====
section FlatM_QJ
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QJan
/-! Clause 1 toolkit (E4, part 1): analysis helpers. -/

/-- Cauchy–Schwarz for an interval integral of a continuous function. -/
theorem sq_intervalIntegral_le0 {g : ℝ → ℝ} (hg : Continuous g) {t : ℝ} (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t, g u) ^ 2 ≤ t * ∫ u in (0 : ℝ)..t, g u ^ 2 := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0; simp
  set I := ∫ u in (0 : ℝ)..t, g u with hI
  set I2 := ∫ u in (0 : ℝ)..t, g u ^ 2 with hI2
  set m := I / t with hm
  have h0 : 0 ≤ ∫ u in (0 : ℝ)..t, (g u - m) ^ 2 :=
    intervalIntegral.integral_nonneg ht (fun u _ => sq_nonneg _)
  have hexp : ∫ u in (0 : ℝ)..t, (g u - m) ^ 2 = I2 - 2 * m * I + m ^ 2 * t := by
    have e : (fun u => (g u - m) ^ 2) = fun u => (g u ^ 2 - 2 * m * g u) + m ^ 2 := by
      funext u; ring
    rw [e, intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    · simp [hI, hI2]; ring
    · exact (hg.pow 2).intervalIntegrable _ _
    · exact (continuous_const.mul hg).intervalIntegrable _ _
    · exact ((hg.pow 2).sub (continuous_const.mul hg)).intervalIntegrable _ _
    · exact intervalIntegrable_const
  rw [hexp, hm] at h0
  have : I2 - 2 * (I / t) * I + (I / t) ^ 2 * t = (t * I2 - I ^ 2) / t := by
    field_simp; ring
  rw [this] at h0
  have := (div_nonneg_iff.1 h0)
  rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
  · linarith
  · linarith

/-- Uniform-on-compacts geometric Cauchy criterion, with a horizon-dependent start index. -/
theorem geom_cauchy_limit' {F : ℕ → ℝ≥0 → ℝ} (hF : ∀ k, Continuous (F k))
    (hK : ∀ N : ℕ, ∃ K : ℕ, ∀ k, K ≤ k → ∀ t : ℝ≥0, t ≤ N →
      |F (k + 1) t - F k t| ≤ (1 / 2 : ℝ) ^ k) :
    (∀ t, CauchySeq fun k => F k t) ∧ Continuous (fun t => limUnder atTop fun k => F k t) := by
  -- truncate at horizon `N`
  have hN : ∀ N : ℕ, (∀ t, CauchySeq fun k => F k (min t N)) ∧
      Continuous (fun t => limUnder atTop fun k => F k (min t N)) := by
    intro N
    obtain ⟨K, hKN⟩ := hK N
    have h := geom_cauchy_limit (F := fun k t => F k (min t N))
      (fun k => (hF k).comp (continuous_id.min continuous_const)) (K := K)
      (fun k hk t _ => hKN k hk _ (min_le_right _ _))
    exact ⟨h.1, h.2.2⟩
  have hcau : ∀ t, CauchySeq fun k => F k t := by
    intro t
    have h := (hN ⌈t⌉₊).1 t
    have he : min t (⌈t⌉₊ : ℝ≥0) = t := min_eq_left (Nat.le_ceil t)
    simpa [he] using h
  refine ⟨hcau, continuous_iff_continuousAt.2 fun t0 => ?_⟩
  set N := ⌈t0⌉₊ + 1
  have hev : (fun t => limUnder atTop fun k => F k (min t N)) =ᶠ[𝓝 t0]
      (fun t => limUnder atTop fun k => F k t) := by
    have hopen : {t : ℝ≥0 | t < (N : ℝ≥0)} ∈ 𝓝 t0 := by
      refine (isOpen_lt continuous_id continuous_const).mem_nhds ?_
      show t0 < ((⌈t0⌉₊ + 1 : ℕ) : ℝ≥0)
      exact (Nat.le_ceil t0).trans_lt (by exact_mod_cast Nat.lt_succ_self _)
    filter_upwards [hopen] with t ht
    rw [min_eq_left (le_of_lt ht)]
  exact ((hN N).2.continuousAt).congr hev

theorem measurable_toLp_coords {Ω' : Type*} {m : MeasurableSpace Ω'} {n : ℕ} {f : Ω' → Fin n → ℝ}
    (h : ∀ i, Measurable[m] fun ω => f ω i) :
    Measurable[m] fun ω => (WithLp.toLp 2 (f ω) : SDEState n) :=
  (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 h)

end QJan

section QJ
/-! Clause 1 toolkit (E4, part 1): the continuous Ito integral as a function, and the Picard map. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- A fixed continuous adapted version of the Ito integral of a bounded continuous adapted
integrand (zero when the hypotheses fail). -/
noncomputable def cIto (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → SDEState d)
    (x₀ : SDEState d) (j : Fin d) (H : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := by
  classical
  exact if h : IsStandardBrownian P W ∧
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s)) ∧
      (∀ s, Measurable (H s)) ∧ (∀ ω, Continuous fun s => H s ω) ∧
      (∃ C : ℝ, ∀ s ω, |H s ω| ≤ C) then
    Classical.choose (contIto_bdd h.1 x₀ j h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.choose_spec)
  else fun _ _ => 0

theorem cIto_spec {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ}
    (hC : ∀ s ω, |H s ω| ≤ C) :
    (∀ ω, Continuous fun t => cIto P W x₀ j H t ω) ∧
      (∀ t, Measurable[completedBrownianPast P W (fun _ => x₀) t] (cIto P W x₀ j H t)) ∧
      (∀ t, Measurable (cIto P W x₀ j H t)) ∧ (∀ ω, cIto P W x₀ j H 0 ω = 0) ∧
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H (cIto P W x₀ j H) := by
  classical
  have h : IsStandardBrownian P W ∧
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s)) ∧
      (∀ s, Measurable (H s)) ∧ (∀ ω, Continuous fun s => H s ω) ∧
      (∃ C : ℝ, ∀ s ω, |H s ω| ≤ C) := ⟨hW, hHm, hHa, hHc, C, hC⟩
  unfold cIto
  rw [dif_pos h]
  exact Classical.choose_spec (contIto_bdd h.1 x₀ j h.2.1 h.2.2.1 h.2.2.2.1
    h.2.2.2.2.choose_spec)

/-- Continuous, measurable and adapted (to the completed Brownian past from `x₀`) paths. -/
def GoodProc (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d) (x₀ : SDEState d)
    (Y : ℝ≥0 → Ω → SDEState d) : Prop :=
  (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous fun t => Y t ω) ∧
    (∀ t, Measurable[completedBrownianPast P W (fun _ => x₀) t] (Y t))

/-- One Picard step for time-homogeneous coefficients `s`, `b`. -/
noncomputable def picStep (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → SDEState d)
    (x₀ : SDEState d) (s : SDEState d → SDEDiffusion d) (b : SDEState d → SDEState d)
    (Y : ℝ≥0 → Ω → SDEState d) : ℝ≥0 → Ω → SDEState d := fun t ω =>
  WithLp.toLp 2 (fun i => x₀ i + ∑ j, cIto P W x₀ j (fun u ω => s (Y u ω) (i, j)) t ω +
    ∫ u in (0 : ℝ)..t.val, b (Y u.toNNReal ω) i)

theorem coordS_continuous {s : SDEState d → SDEDiffusion d} (hs : Continuous s)
    (p : Fin d × Fin d) : Continuous fun x => s x p :=
  ((continuous_apply p).comp (PiLp.continuous_ofLp 2 _)).comp hs

theorem coordB_continuous {b : SDEState d → SDEState d} (hb : Continuous b) (i : Fin d) :
    Continuous fun x => b x i :=
  ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).comp hb

theorem goodProc_coef {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d} {x₀ : SDEState d}
    {Y : ℝ≥0 → Ω → SDEState d} (hY : GoodProc P W x₀ Y) {f : SDEState d → ℝ}
    (hf : Continuous f) :
    (∀ u, Measurable[completedBrownianPast P W (fun _ => x₀) u] fun ω => f (Y u ω)) ∧
      (∀ u, Measurable fun ω => f (Y u ω)) ∧ (∀ ω, Continuous fun u => f (Y u ω)) :=
  ⟨fun u => hf.measurable.comp (hY.2.2 u), fun u => hf.measurable.comp (hY.1 u),
    fun ω => hf.comp (hY.2.1 ω)⟩

theorem picStep_apply (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → SDEState d)
    (x₀ : SDEState d) (s : SDEState d → SDEDiffusion d) (b : SDEState d → SDEState d)
    (Y : ℝ≥0 → Ω → SDEState d) (t : ℝ≥0) (ω : Ω) (i : Fin d) :
    picStep P W x₀ s b Y t ω i = x₀ i + ∑ j, cIto P W x₀ j (fun u ω => s (Y u ω) (i, j)) t ω +
      ∫ u in (0 : ℝ)..t.val, b (Y u.toNNReal ω) i := by
  simp [picStep]

theorem goodProc_picStep {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) {s : SDEState d → SDEDiffusion d}
    {b : SDEState d → SDEState d} (hs : Continuous s) (hb : Continuous b) {S : ℝ}
    (hsS : ∀ x p, |s x p| ≤ S) {Y : ℝ≥0 → Ω → SDEState d} (hY : GoodProc P W x₀ Y) :
    GoodProc P W x₀ (picStep P W x₀ s b Y) := by
  have hJ : ∀ i j, _ := fun (i j : Fin d) =>
    let h := goodProc_coef hY (coordS_continuous hs (i, j))
    cIto_spec hW x₀ j h.1 h.2.1 h.2.2 (fun u ω => hsS _ _)
  have hbc : ∀ i ω, Continuous fun u : ℝ => b (Y u.toNNReal ω) i := fun i ω =>
    (coordB_continuous hb i).comp ((hY.2.1 ω).comp continuous_real_toNNReal)
  have hbcN : ∀ i ω, Continuous fun u : ℝ≥0 => b (Y u ω) i := fun i ω =>
    (coordB_continuous hb i).comp (hY.2.1 ω)
  refine ⟨fun t => ?_, fun ω => ?_, fun t => ?_⟩
  · refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun i => ?_)
    refine (measurable_const.add (Finset.measurable_sum _ fun j _ => (hJ i j).2.2.1 t)).add ?_
    exact measurable_intervalIntegral_of_continuous _ t
      (fun u _ => (coordB_continuous hb i).measurable.comp (hY.1 u)) (hbcN i)
  · refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    refine (continuous_const.add (continuous_finsetSum _ fun j _ => (hJ i j).1 ω)).add ?_
    exact (intervalIntegral.continuous_primitive (fun a b' => (hbc i ω).intervalIntegrable a b')
      0).comp NNReal.continuous_coe
  · refine measurable_toLp_coords fun i => ?_
    have h1 : Measurable[completedBrownianPast P W (fun _ => x₀) t]
        (fun ω => ∑ j, cIto P W x₀ j (fun u ω => s (Y u ω) (i, j)) t ω) :=
      Finset.measurable_sum _ fun j _ => (hJ i j).2.1 t
    have h2 : Measurable[completedBrownianPast P W (fun _ => x₀) t]
        (fun ω => ∫ u in (0 : ℝ)..t.val, b (Y u.toNNReal ω) i) :=
      measurable_intervalIntegral_of_continuous _ t
        (fun u hu => (coordB_continuous hb i).measurable.comp
          ((hY.2.2 u).mono (completedBrownianPast_mono P W _ hu) le_rfl)) (hbcN i)
    have h0 : Measurable[completedBrownianPast P W (fun _ => x₀) t] (fun _ : Ω => x₀ i) :=
      measurable_const
    exact (h0.add h1).add h2

/-- The Picard iterates, started from the constant `x₀`. -/
noncomputable def picIter (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → SDEState d)
    (x₀ : SDEState d) (s : SDEState d → SDEDiffusion d) (b : SDEState d → SDEState d) :
    ℕ → ℝ≥0 → Ω → SDEState d
  | 0 => fun _ _ => x₀
  | k + 1 => picStep P W x₀ s b (picIter P W x₀ s b k)

theorem goodProc_const (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d) (x₀ : SDEState d) :
    GoodProc P W x₀ (fun _ _ => x₀) :=
  ⟨fun _ => measurable_const, fun _ => continuous_const, fun _ => measurable_const⟩

theorem goodProc_picIter {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) {s : SDEState d → SDEDiffusion d}
    {b : SDEState d → SDEState d} (hs : Continuous s) (hb : Continuous b) {S : ℝ}
    (hsS : ∀ x p, |s x p| ≤ S) (k : ℕ) : GoodProc P W x₀ (picIter P W x₀ s b k) := by
  induction k with
  | zero => exact goodProc_const P W x₀
  | succ k ih => exact goodProc_picStep hW x₀ hs hb hsS ih

end QJ
end ItoLib

end FlatM_QJ
-- ===== QK =====
section FlatM_QK
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QKan

theorem ofReal_intervalIntegral_eq {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ u, 0 ≤ g u) {t : ℝ}
    (ht : 0 ≤ t) :
    ENNReal.ofReal (∫ u in (0 : ℝ)..t, g u) = ∫⁻ u in Ioc 0 t, ENNReal.ofReal (g u) := by
  rw [intervalIntegral.integral_of_le ht, ofReal_integral_eq_lintegral_ofReal]
  · exact hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact ae_of_all _ fun u => hg0 u

/-- `‖v‖² ≤ 2d Σ a² + 2 Σ c²` when `v i = Σ_j a i j + c i`. -/
theorem vec_sq_bound {d : ℕ} (v : SDEState d) (a : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hv : ∀ i, v i = ∑ j, a i j + c i) :
    ‖v‖ ^ 2 ≤ 2 * d * ∑ p : Fin d × Fin d, a p.1 p.2 ^ 2 + 2 * ∑ i, c i ^ 2 := by
  have hper : ∀ i, (∑ j, a i j + c i) ^ 2 ≤ 2 * d * ∑ j, a i j ^ 2 + 2 * c i ^ 2 := by
    intro i
    have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => a i j)
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    have h2 : (∑ j, a i j + c i) ^ 2 ≤ 2 * (∑ j, a i j) ^ 2 + 2 * c i ^ 2 := by
      nlinarith [sq_nonneg (∑ j, a i j - c i)]
    nlinarith
  calc ‖v‖ ^ 2 = ∑ i, (∑ j, a i j + c i) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]; simp only [hv]
    _ ≤ ∑ i, (2 * d * ∑ j, a i j ^ 2 + 2 * c i ^ 2) := Finset.sum_le_sum fun i _ => hper i
    _ = 2 * d * ∑ p : Fin d × Fin d, a p.1 p.2 ^ 2 + 2 * ∑ i, c i ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Fintype.sum_prod_type]

theorem ofReal_intervalIntegral_eq' {g : ℝ → ℝ} (hg : Continuous g) {t : ℝ} (ht : 0 ≤ t)
    (hg0 : ∀ u ∈ Ioc 0 t, 0 ≤ g u) :
    ENNReal.ofReal (∫ u in (0 : ℝ)..t, g u) = ∫⁻ u in Ioc 0 t, ENNReal.ofReal (g u) := by
  rw [intervalIntegral.integral_of_le ht, ofReal_integral_eq_lintegral_ofReal]
  · exact hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ hg0)

/-- Picard factorial bound from the integral recursion. -/
theorem picard_factorial {φ : ℕ → ℝ → ℝ≥0∞} {T M K : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M)
    (h0 : ∀ u ∈ Icc 0 T, φ 0 u ≤ ENNReal.ofReal M)
    (hrec : ∀ k, ∀ t ∈ Icc 0 T, φ (k + 1) t ≤ ENNReal.ofReal K * ∫⁻ u in Ioc 0 t, φ k u) :
    ∀ k, ∀ t ∈ Icc 0 T, φ k t ≤ ENNReal.ofReal (M * (K * t) ^ k / k.factorial) := by
  intro k
  induction k with
  | zero => intro t ht; simpa using h0 t ht
  | succ k ih =>
    intro t ht
    have hcont : Continuous fun u : ℝ => M * (K * u) ^ k / k.factorial := by fun_prop
    calc φ (k + 1) t ≤ ENNReal.ofReal K * ∫⁻ u in Ioc 0 t, φ k u := hrec k t ht
      _ ≤ ENNReal.ofReal K * ∫⁻ u in Ioc 0 t,
            ENNReal.ofReal (M * (K * u) ^ k / k.factorial) := by
          exact mul_le_mul' le_rfl (setLIntegral_mono hcont.measurable.ennreal_ofReal
            fun u hu => ih u ⟨hu.1.le, hu.2.trans ht.2⟩)
      _ = ENNReal.ofReal K * ENNReal.ofReal (∫ u in (0 : ℝ)..t,
            M * (K * u) ^ k / k.factorial) := by
          rw [ofReal_intervalIntegral_eq' hcont ht.1 fun u hu => by
            have := hu.1.le; positivity]
      _ = ENNReal.ofReal (M * (K * t) ^ (k + 1) / (k + 1).factorial) := by
          rw [← ENNReal.ofReal_mul hK]
          congr 1
          have e : (fun u : ℝ => M * (K * u) ^ k / k.factorial) =
              fun u => (M * K ^ k / k.factorial) * u ^ k := by
            funext u; rw [mul_pow]; ring
          rw [e, intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
          push_cast
          field_simp
          ring

end QKan

section QK
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

set_option maxHeartbeats 1000000 in
/-- Ito isometry bound in `lintegral` form. -/
theorem ito_sq_lint {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H J H₁ J₁ : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ}
    (hC : ∀ s ω, |H s ω| ≤ C)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J)
    (hHm₁ : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H₁ s))
    (hHa₁ : ∀ s, Measurable (H₁ s)) (hHc₁ : ∀ ω, Continuous fun s => H₁ s ω)
    (hC₁ : ∀ s ω, |H₁ s ω| ≤ C)
    (hJ₁ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H₁ J₁) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal ((J t ω - J₁ t ω) ^ 2) ∂P ≤
      ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..t.val,
        (H u.toNNReal ω - H₁ u.toNNReal ω) ^ 2) ∂P := by
  have h := ito_sq_le2 hW x₀ j hHm hHc hC hJ hHm₁ hHc₁ hC₁ hJ₁ t
  have hm1 := (ito_integral_memLp_meanZero hW x₀ j hHm hHc hC hJ t).1
  have hm2 := (ito_integral_memLp_meanZero hW x₀ j hHm₁ hHc₁ hC₁ hJ₁ t).1
  have hint1 : Integrable (fun ω => (J t ω - J₁ t ω) ^ 2) P := (hm1.sub hm2).integrable_sq
  have hmeas : Measurable fun ω => ∫ u in (0 : ℝ)..t.val,
      (H u.toNNReal ω - H₁ u.toNNReal ω) ^ 2 :=
    measurable_intervalIntegral_of_continuous _ t (H := fun u ω => (H u ω - H₁ u ω) ^ 2)
      (fun u _ => ((hHa u).sub (hHa₁ u)).pow_const 2) (fun ω => ((hHc ω).sub (hHc₁ ω)).pow 2)
  have hbd : ∀ ω, ‖∫ u in (0 : ℝ)..t.val, (H u.toNNReal ω - H₁ u.toNNReal ω) ^ 2‖ ≤
      (2 * C) ^ 2 * |t.val - 0| := fun ω =>
    intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 := hC u.toNNReal ω
      have h2 := hC₁ u.toNNReal ω
      have h3 : |H u.toNNReal ω - H₁ u.toNNReal ω| ≤ 2 * C := (abs_sub _ _).trans (by linarith)
      calc (H u.toNNReal ω - H₁ u.toNNReal ω) ^ 2 = |H u.toNNReal ω - H₁ u.toNNReal ω| ^ 2 :=
            (sq_abs _).symm
        _ ≤ (2 * C) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
  have hint2 : Integrable (fun ω => ∫ u in (0 : ℝ)..t.val,
      (H u.toNNReal ω - H₁ u.toNNReal ω) ^ 2) P :=
    Integrable.mono' (integrable_const ((2 * C) ^ 2 * |t.val - 0|))
      hmeas.aestronglyMeasurable (ae_of_all _ hbd)
  rw [← ofReal_integral_eq_lintegral_ofReal hint1 (ae_of_all _ fun ω => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all _ fun ω =>
      intervalIntegral.integral_nonneg t.2 fun u _ => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h

/-- Tonelli for a nonnegative continuous-in-time measurable process. -/
theorem lint_swap {P : Measure Ω} [IsProbabilityMeasure P] {F : ℝ≥0 → Ω → ℝ}
    (hFc : ∀ ω, Continuous fun u => F u ω) (hFm : ∀ u, Measurable (F u))
    (hF0 : ∀ u ω, 0 ≤ F u ω) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..t.val, F u.toNNReal ω) ∂P =
      ∫⁻ u in Ioc 0 t.val, ∫⁻ ω, ENNReal.ofReal (F u.toNNReal ω) ∂P := by
  have h1 : ∀ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..t.val, F u.toNNReal ω) =
      ∫⁻ u in Ioc 0 t.val, ENNReal.ofReal (F u.toNNReal ω) := fun ω =>
    ofReal_intervalIntegral_eq ((hFc ω).comp continuous_real_toNNReal) (fun u => hF0 _ _) t.2
  simp_rw [h1]
  have hm : Measurable (Function.uncurry fun (u : ℝ) (ω : Ω) => F u.toNNReal ω) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => (hFc ω).comp continuous_real_toNNReal) (fun u => hFm _)
  have hm' : Measurable (Function.uncurry fun (ω : Ω) (u : ℝ) =>
      ENNReal.ofReal (F u.toNNReal ω)) :=
    (hm.comp measurable_swap).ennreal_ofReal
  exact lintegral_lintegral_swap hm'.aemeasurable

set_option maxHeartbeats 2000000 in
/-- One Picard step is Lipschitz in mean square. -/
theorem picStep_sq_le {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) {s : SDEState d → SDEDiffusion d}
    {b : SDEState d → SDEState d} (hs : Continuous s) (hb : Continuous b) {S : ℝ}
    (hsS : ∀ x p, |s x p| ≤ S) {L : ℝ}
    (hL : ∀ x y, ‖s x - s y‖ ≤ L * ‖x - y‖ ∧ ‖b x - b y‖ ≤ L * ‖x - y‖)
    {Y Y' : ℝ≥0 → Ω → SDEState d} (hY : GoodProc P W x₀ Y) (hY' : GoodProc P W x₀ Y')
    (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (‖picStep P W x₀ s b Y t ω - picStep P W x₀ s b Y' t ω‖ ^ 2) ∂P ≤
      ENNReal.ofReal (2 * (d + t) * L ^ 2) * ∫⁻ ω, ENNReal.ofReal
        (∫ u in (0 : ℝ)..t.val, ‖Y u.toNNReal ω - Y' u.toNNReal ω‖ ^ 2) ∂P := by
  set JY : Fin d → Fin d → ℝ≥0 → Ω → ℝ := fun i j =>
    cIto P W x₀ j (fun u ω => s (Y u ω) (i, j)) with hJY
  set JY' : Fin d → Fin d → ℝ≥0 → Ω → ℝ := fun i j =>
    cIto P W x₀ j (fun u ω => s (Y' u ω) (i, j)) with hJY'
  have cfY := fun (i j : Fin d) => goodProc_coef hY (coordS_continuous hs (i, j))
  have cfY' := fun (i j : Fin d) => goodProc_coef hY' (coordS_continuous hs (i, j))
  have specY := fun (i j : Fin d) =>
    cIto_spec hW x₀ j (cfY i j).1 (cfY i j).2.1 (cfY i j).2.2 (fun u ω => hsS _ _)
  have specY' := fun (i j : Fin d) =>
    cIto_spec hW x₀ j (cfY' i j).1 (cfY' i j).2.1 (cfY' i j).2.2 (fun u ω => hsS _ _)
  set Q : Ω → ℝ := fun ω => ∫ u in (0 : ℝ)..t.val, ‖Y u.toNNReal ω - Y' u.toNNReal ω‖ ^ 2
    with hQ
  have hQ0 : ∀ ω, 0 ≤ Q ω := fun ω =>
    intervalIntegral.integral_nonneg t.2 fun u _ => sq_nonneg _
  have hYc : ∀ ω, Continuous fun u : ℝ => Y u.toNNReal ω := fun ω =>
    (hY.2.1 ω).comp continuous_real_toNNReal
  have hY'c : ∀ ω, Continuous fun u : ℝ => Y' u.toNNReal ω := fun ω =>
    (hY'.2.1 ω).comp continuous_real_toNNReal
  have hdc : ∀ ω, Continuous fun u : ℝ => ‖Y u.toNNReal ω - Y' u.toNNReal ω‖ ^ 2 := fun ω =>
    ((hYc ω).sub (hY'c ω)).norm.pow 2
  -- a generic pathwise estimate `Σ ∫ (Δf)² ≤ L² Q` for a Lipschitz vector field
  have hlipint : ∀ {ι : Type} [Fintype ι] (f : SDEState d → EuclideanSpace ℝ ι),
      Continuous f → (∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) → ∀ ω,
      ∑ p, ∫ u in (0 : ℝ)..t.val, (f (Y u.toNNReal ω) p - f (Y' u.toNNReal ω) p) ^ 2 ≤
        L ^ 2 * Q ω := by
    intro ι _ f hf hfL ω
    have hfc : ∀ p, Continuous fun u : ℝ => (f (Y u.toNNReal ω) p - f (Y' u.toNNReal ω) p) ^ 2 :=
      fun p => ((((continuous_apply p).comp (PiLp.continuous_ofLp 2 _)).comp
        (hf.comp (hYc ω))).sub (((continuous_apply p).comp (PiLp.continuous_ofLp 2 _)).comp
        (hf.comp (hY'c ω)))).pow 2
    rw [← intervalIntegral.integral_finsetSum fun p _ => (hfc p).intervalIntegrable _ _,
      hQ, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on t.2
      ((continuous_finsetSum _ fun p _ => hfc p).intervalIntegrable _ _)
      ((continuous_const.mul (hdc ω)).intervalIntegrable _ _) fun u _ => ?_
    have h1 : ∑ p, (f (Y u.toNNReal ω) p - f (Y' u.toNNReal ω) p) ^ 2 =
        ‖f (Y u.toNNReal ω) - f (Y' u.toNNReal ω)‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]; simp
    rw [h1]
    calc ‖f (Y u.toNNReal ω) - f (Y' u.toNNReal ω)‖ ^ 2
        ≤ (L * ‖Y u.toNNReal ω - Y' u.toNNReal ω‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hfL _ _) 2
      _ = L ^ 2 * ‖Y u.toNNReal ω - Y' u.toNNReal ω‖ ^ 2 := by ring
  -- pathwise bound
  have hpath : ∀ ω, ‖picStep P W x₀ s b Y t ω - picStep P W x₀ s b Y' t ω‖ ^ 2 ≤
      2 * d * ∑ p : Fin d × Fin d, (JY p.1 p.2 t ω - JY' p.1 p.2 t ω) ^ 2 +
        2 * t * L ^ 2 * Q ω := by
    intro ω
    have hbi : ∀ (Z : ℝ≥0 → Ω → SDEState d), (∀ ω, Continuous fun u : ℝ => Z u.toNNReal ω) →
        ∀ i, IntervalIntegrable (fun u : ℝ => b (Z u.toNNReal ω) i) volume 0 t.val :=
      fun Z hZ i => ((coordB_continuous hb i).comp (hZ ω)).intervalIntegrable _ _
    set c : Fin d → ℝ := fun i =>
      ∫ u in (0 : ℝ)..t.val, (b (Y u.toNNReal ω) i - b (Y' u.toNNReal ω) i) with hc
    have hv : ∀ i, (picStep P W x₀ s b Y t ω - picStep P W x₀ s b Y' t ω) i =
        ∑ j, (JY i j t ω - JY' i j t ω) + c i := by
      intro i
      rw [PiLp.sub_apply, picStep_apply, picStep_apply]
      have e := intervalIntegral.integral_sub (hbi Y hYc i) (hbi Y' hY'c i)
      have e2 : ∑ j, (JY i j t ω - JY' i j t ω) = ∑ j, JY i j t ω - ∑ j, JY' i j t ω := by
        rw [Finset.sum_sub_distrib]
      simp only [hc, hJY, hJY'] at e e2 ⊢
      linarith
    have h1 := vec_sq_bound _ (fun i j => JY i j t ω - JY' i j t ω) c hv
    have hc2 : ∑ i, c i ^ 2 ≤ t * (L ^ 2 * Q ω) := by
      have hci : ∀ i, c i ^ 2 ≤ t * ∫ u in (0 : ℝ)..t.val,
          (b (Y u.toNNReal ω) i - b (Y' u.toNNReal ω) i) ^ 2 := fun i =>
        sq_intervalIntegral_le0 (((coordB_continuous hb i).comp (hYc ω)).sub
          ((coordB_continuous hb i).comp (hY'c ω))) t.2
      calc ∑ i, c i ^ 2 ≤ ∑ i, t * ∫ u in (0 : ℝ)..t.val,
            (b (Y u.toNNReal ω) i - b (Y' u.toNNReal ω) i) ^ 2 :=
            Finset.sum_le_sum fun i _ => hci i
        _ = t * ∑ i, ∫ u in (0 : ℝ)..t.val,
            (b (Y u.toNNReal ω) i - b (Y' u.toNNReal ω) i) ^ 2 := by rw [Finset.mul_sum]
        _ ≤ t * (L ^ 2 * Q ω) := mul_le_mul_of_nonneg_left
            (hlipint b hb (fun x y => (hL x y).2) ω) t.2
    nlinarith [h1, hc2]
  -- expectation of the stochastic part
  have hJm : ∀ p : Fin d × Fin d, Measurable fun ω => (JY p.1 p.2 t ω - JY' p.1 p.2 t ω) ^ 2 :=
    fun p => (((specY p.1 p.2).2.2.1 t).sub ((specY' p.1 p.2).2.2.1 t)).pow_const 2
  have hJpart : ∫⁻ ω, ENNReal.ofReal
      (∑ p : Fin d × Fin d, (JY p.1 p.2 t ω - JY' p.1 p.2 t ω) ^ 2) ∂P ≤
      ENNReal.ofReal (L ^ 2) * ∫⁻ ω, ENNReal.ofReal (Q ω) ∂P := by
    have hIm : ∀ p : Fin d × Fin d, Measurable fun ω => ENNReal.ofReal (∫ u in (0 : ℝ)..t.val,
        (s (Y u.toNNReal ω) (p.1, p.2) - s (Y' u.toNNReal ω) (p.1, p.2)) ^ 2) := fun p =>
      (measurable_intervalIntegral_of_continuous _ t
        (H := fun u ω => (s (Y u ω) (p.1, p.2) - s (Y' u ω) (p.1, p.2)) ^ 2)
        (fun u _ => (((cfY p.1 p.2).2.1 u).sub ((cfY' p.1 p.2).2.1 u)).pow_const 2)
        (fun ω => (((cfY p.1 p.2).2.2 ω).sub ((cfY' p.1 p.2).2.2 ω)).pow 2)).ennreal_ofReal
    calc ∫⁻ ω, ENNReal.ofReal
          (∑ p : Fin d × Fin d, (JY p.1 p.2 t ω - JY' p.1 p.2 t ω) ^ 2) ∂P
        = ∑ p : Fin d × Fin d, ∫⁻ ω, ENNReal.ofReal
            ((JY p.1 p.2 t ω - JY' p.1 p.2 t ω) ^ 2) ∂P := by
          rw [← lintegral_finsetSum _ fun p _ => (hJm p).ennreal_ofReal]
          refine lintegral_congr fun ω => ?_
          rw [ENNReal.ofReal_sum_of_nonneg fun p _ => sq_nonneg _]
      _ ≤ ∑ p : Fin d × Fin d, ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..t.val,
            (s (Y u.toNNReal ω) (p.1, p.2) - s (Y' u.toNNReal ω) (p.1, p.2)) ^ 2) ∂P := by
          refine Finset.sum_le_sum fun p _ => ?_
          exact ito_sq_lint hW x₀ p.2 (cfY p.1 p.2).1 (cfY p.1 p.2).2.1 (cfY p.1 p.2).2.2
            (fun u ω => hsS _ _) (specY p.1 p.2).2.2.2.2 (cfY' p.1 p.2).1 (cfY' p.1 p.2).2.1
            (cfY' p.1 p.2).2.2 (fun u ω => hsS _ _) (specY' p.1 p.2).2.2.2.2 t
      _ = ∫⁻ ω, ENNReal.ofReal (∑ p : Fin d × Fin d, ∫ u in (0 : ℝ)..t.val,
            (s (Y u.toNNReal ω) p - s (Y' u.toNNReal ω) p) ^ 2) ∂P := by
          rw [← lintegral_finsetSum _ fun p _ => hIm p]
          refine lintegral_congr fun ω => ?_
          rw [ENNReal.ofReal_sum_of_nonneg fun p _ =>
            intervalIntegral.integral_nonneg t.2 fun u _ => sq_nonneg _]
      _ ≤ ∫⁻ ω, ENNReal.ofReal (L ^ 2) * ENNReal.ofReal (Q ω) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_mul (sq_nonneg L)]
          exact ENNReal.ofReal_le_ofReal (hlipint s hs (fun x y => (hL x y).1) ω)
      _ = ENNReal.ofReal (L ^ 2) * ∫⁻ ω, ENNReal.ofReal (Q ω) ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hS0 : ∀ ω, 0 ≤ ∑ p : Fin d × Fin d, (JY p.1 p.2 t ω - JY' p.1 p.2 t ω) ^ 2 :=
    fun ω => Finset.sum_nonneg fun p _ => sq_nonneg _
  have hd0 : (0 : ℝ) ≤ 2 * d := by positivity
  have ht0 : (0 : ℝ) ≤ 2 * t * L ^ 2 := by positivity
  calc ∫⁻ ω, ENNReal.ofReal (‖picStep P W x₀ s b Y t ω - picStep P W x₀ s b Y' t ω‖ ^ 2) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (2 * d) * ENNReal.ofReal
          (∑ p : Fin d × Fin d, (JY p.1 p.2 t ω - JY' p.1 p.2 t ω) ^ 2) +
          ENNReal.ofReal (2 * t * L ^ 2) * ENNReal.ofReal (Q ω)) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_mul hd0, ← ENNReal.ofReal_mul ht0,
          ← ENNReal.ofReal_add (mul_nonneg hd0 (hS0 ω)) (mul_nonneg ht0 (hQ0 ω))]
        exact ENNReal.ofReal_le_ofReal (hpath ω)
    _ = ENNReal.ofReal (2 * d) * ∫⁻ ω, ENNReal.ofReal
          (∑ p : Fin d × Fin d, (JY p.1 p.2 t ω - JY' p.1 p.2 t ω) ^ 2) ∂P +
          ENNReal.ofReal (2 * t * L ^ 2) * ∫⁻ ω, ENNReal.ofReal (Q ω) ∂P := by
        have hm1 : Measurable fun ω => ENNReal.ofReal (2 * d) * ENNReal.ofReal
            (∑ p : Fin d × Fin d, (JY p.1 p.2 t ω - JY' p.1 p.2 t ω) ^ 2) :=
          measurable_const.mul (Finset.measurable_sum _ fun p _ => hJm p).ennreal_ofReal
        rw [lintegral_add_left hm1,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2 * d) * (ENNReal.ofReal (L ^ 2) * ∫⁻ ω, ENNReal.ofReal (Q ω) ∂P) +
          ENNReal.ofReal (2 * t * L ^ 2) * ∫⁻ ω, ENNReal.ofReal (Q ω) ∂P := by
        gcongr
    _ = ENNReal.ofReal (2 * (d + t) * L ^ 2) * ∫⁻ ω, ENNReal.ofReal (Q ω) ∂P := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hd0, ← add_mul,
          ← ENNReal.ofReal_add (mul_nonneg hd0 (sq_nonneg L)) ht0]
        congr 2
        ring

end QK
end ItoLib

end FlatM_QK
-- ===== QL =====
section FlatM_QL
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QL
/-! Clause 1 toolkit (E4, part 3): initial bound and the Picard moment bound. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem sq_le_of_abs_le' {a S : ℝ} (h : |a| ≤ S) : a ^ 2 ≤ S ^ 2 := by
  have := abs_le.mp h
  exact sq_le_sq' this.1 this.2

set_option maxHeartbeats 1000000 in
/-- Mean-square size of one Picard step around the starting point. -/
theorem picStep_sub_x0_sq_le {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {s : SDEState d → SDEDiffusion d} {b : SDEState d → SDEState d} (hs : Continuous s)
    (hb : Continuous b) {S : ℝ} (hsS : ∀ x p, |s x p| ≤ S) (hbS : ∀ x i, |b x i| ≤ S)
    {Y : ℝ≥0 → Ω → SDEState d} (hY : GoodProc P W x₀ Y) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (‖picStep P W x₀ s b Y t ω - x₀‖ ^ 2) ∂P ≤
      ENNReal.ofReal (2 * d * (d * d * (t * S ^ 2)) + 2 * (d * (t ^ 2 * S ^ 2))) := by
  set JY : Fin d → Fin d → ℝ≥0 → Ω → ℝ := fun i j =>
    cIto P W x₀ j (fun u ω => s (Y u ω) (i, j)) with hJY
  have cfY := fun (i j : Fin d) => goodProc_coef hY (coordS_continuous hs (i, j))
  have specY := fun (i j : Fin d) =>
    cIto_spec hW x₀ j (cfY i j).1 (cfY i j).2.1 (cfY i j).2.2 (fun u ω => hsS _ _)
  have hYc : ∀ ω, Continuous fun u : ℝ => Y u.toNNReal ω := fun ω =>
    (hY.2.1 ω).comp continuous_real_toNNReal
  -- pathwise bound
  have hpath : ∀ ω, ‖picStep P W x₀ s b Y t ω - x₀‖ ^ 2 ≤
      2 * d * ∑ p : Fin d × Fin d, (JY p.1 p.2 t ω) ^ 2 + 2 * (d * (t ^ 2 * S ^ 2)) := by
    intro ω
    set c : Fin d → ℝ := fun i => ∫ u in (0 : ℝ)..t.val, b (Y u.toNNReal ω) i with hc
    have hv : ∀ i, (picStep P W x₀ s b Y t ω - x₀) i = ∑ j, JY i j t ω + c i := by
      intro i
      rw [PiLp.sub_apply, picStep_apply]
      simp only [hc, hJY]
      ring
    have h1 := vec_sq_bound _ (fun i j => JY i j t ω) c hv
    have hci : ∀ i, c i ^ 2 ≤ t ^ 2 * S ^ 2 := by
      intro i
      have hb1 : ∀ u ∈ Set.uIoc (0 : ℝ) t.val, ‖b (Y u.toNNReal ω) i‖ ≤ S := fun u _ => by
        rw [Real.norm_eq_abs]; exact hbS _ _
      have h2 := intervalIntegral.norm_integral_le_of_norm_le_const hb1
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg t.2] at h2
      have h3 : |c i| ≤ S * t := h2
      have := sq_le_of_abs_le' h3
      nlinarith
    have hc2 : ∑ i, c i ^ 2 ≤ d * (t ^ 2 * S ^ 2) := by
      calc ∑ i, c i ^ 2 ≤ ∑ _i : Fin d, t ^ 2 * S ^ 2 := Finset.sum_le_sum fun i _ => hci i
        _ = d * (t ^ 2 * S ^ 2) := by simp
    nlinarith [h1, hc2]
  have hJm : ∀ p : Fin d × Fin d, Measurable fun ω => (JY p.1 p.2 t ω) ^ 2 :=
    fun p => ((specY p.1 p.2).2.2.1 t).pow_const 2
  have hJpart : ∫⁻ ω, ENNReal.ofReal (∑ p : Fin d × Fin d, (JY p.1 p.2 t ω) ^ 2) ∂P ≤
      ENNReal.ofReal (d * d * (t * S ^ 2)) := by
    have hone : ∀ p : Fin d × Fin d,
        ∫⁻ ω, ENNReal.ofReal ((JY p.1 p.2 t ω) ^ 2) ∂P ≤ ENNReal.ofReal (t * S ^ 2) := by
      intro p
      have hS0 : 0 ≤ S := (abs_nonneg _).trans (hsS x₀ p)
      have h := ito_sq_lint hW x₀ p.2 (cfY p.1 p.2).1 (cfY p.1 p.2).2.1 (cfY p.1 p.2).2.2
        (fun u ω => hsS _ _) (specY p.1 p.2).2.2.2.2 (H₁ := fun _ _ => 0)
        (fun _ => measurable_const) (fun _ => measurable_const) (fun _ => continuous_const)
        (fun _ _ => by simpa using hS0)
        (hasBrownianItoIntegral_zero P _ (fun s ω => W s ω p.2)) t
      simp only [sub_zero] at h
      refine h.trans ?_
      calc ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..t.val, (s (Y u.toNNReal ω) (p.1, p.2)) ^ 2) ∂P
          ≤ ∫⁻ _ω, ENNReal.ofReal (t * S ^ 2) ∂P := by
            refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
            have hc : Continuous fun u : ℝ => (s (Y u.toNNReal ω) (p.1, p.2)) ^ 2 :=
              ((coordS_continuous hs (p.1, p.2)).comp (hYc ω)).pow 2
            calc ∫ u in (0 : ℝ)..t.val, (s (Y u.toNNReal ω) (p.1, p.2)) ^ 2
                ≤ ∫ _u in (0 : ℝ)..t.val, S ^ 2 :=
                  intervalIntegral.integral_mono_on t.2 (hc.intervalIntegrable _ _)
                    intervalIntegrable_const fun u _ => sq_le_of_abs_le' (hsS _ _)
              _ = t * S ^ 2 := by simp
        _ = ENNReal.ofReal (t * S ^ 2) := by simp
    have hts : 0 ≤ t * S ^ 2 := by positivity
    calc ∫⁻ ω, ENNReal.ofReal (∑ p : Fin d × Fin d, (JY p.1 p.2 t ω) ^ 2) ∂P
        = ∑ p : Fin d × Fin d, ∫⁻ ω, ENNReal.ofReal ((JY p.1 p.2 t ω) ^ 2) ∂P := by
          rw [← lintegral_finsetSum _ fun p _ => (hJm p).ennreal_ofReal]
          refine lintegral_congr fun ω => ?_
          rw [ENNReal.ofReal_sum_of_nonneg fun p _ => sq_nonneg _]
      _ ≤ ∑ _p : Fin d × Fin d, ENNReal.ofReal (t * S ^ 2) := Finset.sum_le_sum fun p _ => hone p
      _ = ENNReal.ofReal (d * d * (t * S ^ 2)) := by
          rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => hts]
          congr 1
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  have hS0 : ∀ ω, 0 ≤ ∑ p : Fin d × Fin d, (JY p.1 p.2 t ω) ^ 2 :=
    fun ω => Finset.sum_nonneg fun p _ => sq_nonneg _
  have hd0 : (0 : ℝ) ≤ 2 * d := by positivity
  have hc0 : (0 : ℝ) ≤ 2 * (d * (t ^ 2 * S ^ 2)) := by positivity
  calc ∫⁻ ω, ENNReal.ofReal (‖picStep P W x₀ s b Y t ω - x₀‖ ^ 2) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (2 * d) * ENNReal.ofReal
          (∑ p : Fin d × Fin d, (JY p.1 p.2 t ω) ^ 2) +
          ENNReal.ofReal (2 * (d * (t ^ 2 * S ^ 2)))) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_mul hd0, ← ENNReal.ofReal_add (mul_nonneg hd0 (hS0 ω)) hc0]
        exact ENNReal.ofReal_le_ofReal (hpath ω)
    _ = ENNReal.ofReal (2 * d) * ∫⁻ ω, ENNReal.ofReal
          (∑ p : Fin d × Fin d, (JY p.1 p.2 t ω) ^ 2) ∂P +
          ENNReal.ofReal (2 * (d * (t ^ 2 * S ^ 2))) := by
        have hm1 : Measurable fun ω => ENNReal.ofReal (2 * d) * ENNReal.ofReal
            (∑ p : Fin d × Fin d, (JY p.1 p.2 t ω) ^ 2) :=
          measurable_const.mul (Finset.measurable_sum _ fun p _ => hJm p).ennreal_ofReal
        rw [lintegral_add_left hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (2 * d) * ENNReal.ofReal (d * d * (t * S ^ 2)) +
          ENNReal.ofReal (2 * (d * (t ^ 2 * S ^ 2))) := by gcongr
    _ = ENNReal.ofReal (2 * d * (d * d * (t * S ^ 2)) + 2 * (d * (t ^ 2 * S ^ 2))) := by
        rw [← ENNReal.ofReal_mul hd0, ← ENNReal.ofReal_add (by positivity) hc0]

theorem picIter_succ (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → SDEState d)
    (x₀ : SDEState d) (s : SDEState d → SDEDiffusion d) (b : SDEState d → SDEState d) (k : ℕ) :
    picIter P W x₀ s b (k + 1) = picStep P W x₀ s b (picIter P W x₀ s b k) := rfl

/-- The Picard factorial moment bound on a horizon `T`. -/
theorem picard_moment {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {s : SDEState d → SDEDiffusion d} {b : SDEState d → SDEState d} (hs : Continuous s)
    (hb : Continuous b) {S : ℝ} (hsS : ∀ x p, |s x p| ≤ S) (hbS : ∀ x i, |b x i| ≤ S)
    {L : ℝ} (hL : ∀ x y, ‖s x - s y‖ ≤ L * ‖x - y‖ ∧ ‖b x - b y‖ ≤ L * ‖x - y‖)
    (T : ℝ≥0) (k : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
    ∫⁻ ω, ENNReal.ofReal
        (‖picIter P W x₀ s b (k + 1) t ω - picIter P W x₀ s b k t ω‖ ^ 2) ∂P ≤
      ENNReal.ofReal ((2 * d * (d * d * (T * S ^ 2)) + 2 * (d * (T ^ 2 * S ^ 2))) *
        (2 * (d + T) * L ^ 2 * t) ^ k / k.factorial) := by
  set φ : ℕ → ℝ → ℝ≥0∞ := fun k u => ∫⁻ ω, ENNReal.ofReal
    (‖picIter P W x₀ s b (k + 1) u.toNNReal ω - picIter P W x₀ s b k u.toNNReal ω‖ ^ 2) ∂P
    with hφ
  have hG := goodProc_picIter hW x₀ hs hb hsS
  have hM : (0 : ℝ) ≤ 2 * d * (d * d * (T * S ^ 2)) + 2 * (d * (T ^ 2 * S ^ 2)) := by positivity
  have hK : (0 : ℝ) ≤ 2 * (d + T) * L ^ 2 := by positivity
  have h0 : ∀ u ∈ Icc (0 : ℝ) T, φ 0 u ≤
      ENNReal.ofReal (2 * d * (d * d * (T * S ^ 2)) + 2 * (d * (T ^ 2 * S ^ 2))) := by
    intro u hu
    have hut : (u.toNNReal : ℝ) ≤ T := by
      rw [Real.coe_toNNReal _ hu.1]; exact hu.2
    have h := picStep_sub_x0_sq_le hW x₀ hs hb hsS hbS (hG 0) u.toNNReal
    refine le_trans (le_of_eq ?_) (h.trans (ENNReal.ofReal_le_ofReal ?_))
    · rfl
    · have h1 : (u.toNNReal : ℝ) * S ^ 2 ≤ T * S ^ 2 :=
        mul_le_mul_of_nonneg_right hut (sq_nonneg _)
      have h2 : (u.toNNReal : ℝ) ^ 2 * S ^ 2 ≤ T ^ 2 * S ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (NNReal.coe_nonneg _) hut 2) (sq_nonneg _)
      have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      have hdd : (0 : ℝ) ≤ 2 * d * (d * d) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h1 hdd, mul_le_mul_of_nonneg_left h2 hd]
  have hrec : ∀ k, ∀ t ∈ Icc (0 : ℝ) T, φ (k + 1) t ≤
      ENNReal.ofReal (2 * (d + T) * L ^ 2) * ∫⁻ u in Ioc 0 t, φ k u := by
    intro k t ht
    have htt : (t.toNNReal : ℝ) = t := Real.coe_toNNReal _ ht.1
    have h := picStep_sq_le hW x₀ hs hb hsS hL (hG (k + 1)) (hG k) t.toNNReal
    have hsw := lint_swap (P := P)
      (F := fun u ω => ‖picIter P W x₀ s b (k + 1) u ω - picIter P W x₀ s b k u ω‖ ^ 2)
      (fun ω => (((hG (k + 1)).2.1 ω).sub ((hG k).2.1 ω)).norm.pow 2)
      (fun u => (((hG (k + 1)).1 u).sub ((hG k).1 u)).norm.pow_const 2)
      (fun _ _ => sq_nonneg _) t.toNNReal
    rw [hsw] at h
    simp only [NNReal.val_eq_coe, htt] at h
    refine h.trans ?_
    gcongr
    exact ht.2
  have hmain := picard_factorial hK hM h0 hrec k t ⟨t.2, ht⟩
  simpa [hφ, Real.toNNReal_coe] using hmain

end QL
end ItoLib

end FlatM_QL
-- ===== QM =====
section FlatM_QM
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QM
/-! Clause 1 toolkit (E4, part 4): Borel–Cantelli for the Picard iterates. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem coord_sq_le_norm_sq {ι : Type} [Fintype ι] (v : EuclideanSpace ℝ ι) (p : ι) :
    v p ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Finset.single_le_sum (f := fun q => v q ^ 2) (fun q _ => sq_nonneg _)
    (Finset.mem_univ p)

/-- Pathwise: a coordinate of the difference of two Picard steps. -/
theorem picStep_diff_abs_le {P : Measure Ω} [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → SDEState d) (x₀ : SDEState d) {s : SDEState d → SDEDiffusion d}
    {b : SDEState d → SDEState d} (hb : Continuous b) {Y Y' : ℝ≥0 → Ω → SDEState d}
    (hYc : ∀ ω, Continuous fun t => Y t ω) (hY'c : ∀ ω, Continuous fun t => Y' t ω)
    (N t : ℝ≥0) (ht : t ≤ N) (ω : Ω) (i : Fin d) :
    |picStep P W x₀ s b Y t ω i - picStep P W x₀ s b Y' t ω i| ≤
      ∑ j, |cIto P W x₀ j (fun u ω => s (Y u ω) (i, j)) t ω -
        cIto P W x₀ j (fun u ω => s (Y' u ω) (i, j)) t ω| +
      ∫ u in (0 : ℝ)..N.val, |b (Y u.toNNReal ω) i - b (Y' u.toNNReal ω) i| := by
  have hc : Continuous fun u : ℝ => b (Y u.toNNReal ω) i - b (Y' u.toNNReal ω) i :=
    ((coordB_continuous hb i).comp ((hYc ω).comp continuous_real_toNNReal)).sub
      ((coordB_continuous hb i).comp ((hY'c ω).comp continuous_real_toNNReal))
  have hi1 : IntervalIntegrable (fun u : ℝ => b (Y u.toNNReal ω) i) volume 0 t.val :=
    ((coordB_continuous hb i).comp ((hYc ω).comp continuous_real_toNNReal)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun u : ℝ => b (Y' u.toNNReal ω) i) volume 0 t.val :=
    ((coordB_continuous hb i).comp ((hY'c ω).comp continuous_real_toNNReal)).intervalIntegrable _ _
  have hv : picStep P W x₀ s b Y t ω i - picStep P W x₀ s b Y' t ω i =
      ∑ j, (cIto P W x₀ j (fun u ω => s (Y u ω) (i, j)) t ω -
        cIto P W x₀ j (fun u ω => s (Y' u ω) (i, j)) t ω) +
      ∫ u in (0 : ℝ)..t.val, (b (Y u.toNNReal ω) i - b (Y' u.toNNReal ω) i) := by
    rw [picStep_apply, picStep_apply, intervalIntegral.integral_sub hi1 hi2,
      Finset.sum_sub_distrib]
    ring
  rw [hv]
  refine (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) ?_)
  refine (intervalIntegral.abs_integral_le_integral_abs t.2).trans ?_
  exact intervalIntegral.integral_mono_interval le_rfl t.2 ht
    (ae_of_all _ fun u => abs_nonneg _) (hc.abs.intervalIntegrable _ _)

set_option maxHeartbeats 2000000 in
/-- One Borel–Cantelli term: the probability that the next Picard increment exceeds
`(d+1) lam` somewhere on `[0, N]`, from a mean-square bound `B` on the current increment. -/
theorem picStep_dev_prob {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {s : SDEState d → SDEDiffusion d} {b : SDEState d → SDEState d} (hs : Continuous s)
    (hb : Continuous b) {S : ℝ} (hsS : ∀ x p, |s x p| ≤ S)
    {L : ℝ} (hL : ∀ x y, ‖s x - s y‖ ≤ L * ‖x - y‖ ∧ ‖b x - b y‖ ≤ L * ‖x - y‖)
    {Y Y' : ℝ≥0 → Ω → SDEState d} (hY : GoodProc P W x₀ Y) (hY' : GoodProc P W x₀ Y')
    (N : ℕ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ≥0, t ≤ N → ∫⁻ ω, ENNReal.ofReal (‖Y t ω - Y' t ω‖ ^ 2) ∂P ≤ ENNReal.ofReal B)
    {lam : ℝ} (hlam : 0 < lam) :
    P {ω | ∃ t : ℝ≥0, t ≤ N ∧ ∃ i, (d + 1) * lam <
        |picStep P W x₀ s b Y t ω i - picStep P W x₀ s b Y' t ω i|} ≤
      ENNReal.ofReal ((d * d * (2 * d * N * (L ^ 2 * B)) + d * (N * (N * (L ^ 2 * B)))) /
        lam ^ 2) := by
  set JY : Fin d → Fin d → ℝ≥0 → Ω → ℝ := fun i j =>
    cIto P W x₀ j (fun u ω => s (Y u ω) (i, j)) with hJY
  set JY' : Fin d → Fin d → ℝ≥0 → Ω → ℝ := fun i j =>
    cIto P W x₀ j (fun u ω => s (Y' u ω) (i, j)) with hJY'
  have cfY := fun (i j : Fin d) => goodProc_coef hY (coordS_continuous hs (i, j))
  have cfY' := fun (i j : Fin d) => goodProc_coef hY' (coordS_continuous hs (i, j))
  have specY := fun (i j : Fin d) =>
    cIto_spec hW x₀ j (cfY i j).1 (cfY i j).2.1 (cfY i j).2.2 (fun u ω => hsS _ _)
  have specY' := fun (i j : Fin d) =>
    cIto_spec hW x₀ j (cfY' i j).1 (cfY' i j).2.1 (cfY' i j).2.2 (fun u ω => hsS _ _)
  set EJ : Fin d × Fin d → Set Ω := fun p =>
    {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |JY p.1 p.2 t ω - JY' p.1 p.2 t ω|} with hEJ
  set g : Fin d → Ω → ℝ := fun i ω =>
    ∫ u in (0 : ℝ)..(N : ℝ≥0).val, |b (Y u.toNNReal ω) i - b (Y' u.toNNReal ω) i| with hg
  set Eb : Fin d → Set Ω := fun i => {ω | lam < g i ω} with hEb
  -- inclusion
  have hsub : {ω | ∃ t : ℝ≥0, t ≤ N ∧ ∃ i, (d + 1) * lam <
        |picStep P W x₀ s b Y t ω i - picStep P W x₀ s b Y' t ω i|} ⊆
      (⋃ p, EJ p) ∪ ⋃ i, Eb i := by
    intro ω hω
    obtain ⟨t, htN, i, hlt⟩ := hω
    by_contra hno
    simp only [mem_union, mem_iUnion, not_or, not_exists, hEJ, hEb, mem_setOf_eq,
      not_lt] at hno
    have h1 := picStep_diff_abs_le (P := P) W x₀ (s := s) hb hY.2.1 hY'.2.1 N t htN ω i
    have h2 : ∑ j, |JY i j t ω - JY' i j t ω| ≤ ∑ _j : Fin d, lam :=
      Finset.sum_le_sum fun j _ => by
        first
        | exact hno.1 (i, j) t htN
        | exact le_of_not_gt fun h => hno.1 (i, j) t ⟨htN, h⟩
    have h3 : g i ω ≤ lam := by
      first
      | exact hno.2 i
      | exact le_of_not_gt (hno.2 i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    simp only [hJY, hJY', hg] at h2 h3
    linarith
  -- stochastic part
  have hJprob : ∀ p, P (EJ p) ≤ ENNReal.ofReal (2 * d * N * (L ^ 2 * B) / lam ^ 2) := by
    intro p
    have hβ : ∀ u : ℝ≥0, u ≤ N →
        ∫ ω, (s (Y u ω) (p.1, p.2) - s (Y' u ω) (p.1, p.2)) ^ 2 ∂P ≤ L ^ 2 * B := by
      intro u hu
      have hm : Measurable fun ω => (s (Y u ω) (p.1, p.2) - s (Y' u ω) (p.1, p.2)) ^ 2 :=
        (((cfY p.1 p.2).2.1 u).sub ((cfY' p.1 p.2).2.1 u)).pow_const 2
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => sq_nonneg _)
        hm.aestronglyMeasurable]
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
      calc ∫⁻ ω, ENNReal.ofReal ((s (Y u ω) (p.1, p.2) - s (Y' u ω) (p.1, p.2)) ^ 2) ∂P
          ≤ ∫⁻ ω, ENNReal.ofReal (L ^ 2) * ENNReal.ofReal (‖Y u ω - Y' u ω‖ ^ 2) ∂P := by
            refine lintegral_mono fun ω => ?_
            rw [← ENNReal.ofReal_mul (sq_nonneg L)]
            refine ENNReal.ofReal_le_ofReal ?_
            have h1 := coord_sq_le_norm_sq (s (Y u ω) - s (Y' u ω)) (p.1, p.2)
            have h2 : ‖s (Y u ω) - s (Y' u ω)‖ ^ 2 ≤ (L * ‖Y u ω - Y' u ω‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (hL _ _).1 2
            rw [PiLp.sub_apply] at h1
            nlinarith
        _ = ENNReal.ofReal (L ^ 2) * ∫⁻ ω, ENNReal.ofReal (‖Y u ω - Y' u ω‖ ^ 2) ∂P :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (L ^ 2) * ENNReal.ofReal B := by gcongr; exact hB u hu
        _ = ENNReal.ofReal (L ^ 2 * B) := by rw [ENNReal.ofReal_mul (sq_nonneg L)]
    have h := contIto_max hW x₀ p.2 (cfY p.1 p.2).1 (cfY p.1 p.2).2.1 (cfY p.1 p.2).2.2
      (fun u ω => hsS _ _) (cfY' p.1 p.2).1 (cfY' p.1 p.2).2.1 (cfY' p.1 p.2).2.2
      (fun u ω => hsS _ _) (specY p.1 p.2).2.2.2.2 (specY' p.1 p.2).2.2.2.2
      (specY p.1 p.2).1 (specY' p.1 p.2).1 hβ hlam
    rw [← ofReal_measureReal (μ := P) (s := EJ p)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ (by positivity)]
    have : P.real (EJ p) * lam ^ 2 = lam ^ 2 * P.real (EJ p) := mul_comm _ _
    rw [this]
    exact h
  -- drift part (Chebyshev)
  have hbprob : ∀ i, P (Eb i) ≤ ENNReal.ofReal (N * (N * (L ^ 2 * B)) / lam ^ 2) := by
    intro i
    have hYc : ∀ ω, Continuous fun u : ℝ => Y u.toNNReal ω := fun ω =>
      (hY.2.1 ω).comp continuous_real_toNNReal
    have hY'c : ∀ ω, Continuous fun u : ℝ => Y' u.toNNReal ω := fun ω =>
      (hY'.2.1 ω).comp continuous_real_toNNReal
    have hdc : ∀ ω, Continuous fun u : ℝ => b (Y u.toNNReal ω) i - b (Y' u.toNNReal ω) i :=
      fun ω => ((coordB_continuous hb i).comp (hYc ω)).sub
        ((coordB_continuous hb i).comp (hY'c ω))
    have hgm : Measurable (g i) :=
      measurable_intervalIntegral_of_continuous _ (N : ℝ≥0)
        (H := fun u ω => |b (Y u ω) i - b (Y' u ω) i|)
        (fun u _ => (((coordB_continuous hb i).measurable.comp (hY.1 u)).sub
          ((coordB_continuous hb i).measurable.comp (hY'.1 u))).abs)
        (fun ω => (((coordB_continuous hb i).comp (hY.2.1 ω)).sub
          ((coordB_continuous hb i).comp (hY'.2.1 ω))).abs)
    have hgsq : ∀ ω, g i ω ^ 2 ≤ N * (L ^ 2 *
        ∫ u in (0 : ℝ)..(N : ℝ≥0).val, ‖Y u.toNNReal ω - Y' u.toNNReal ω‖ ^ 2) := by
      intro ω
      have h1 := sq_intervalIntegral_le0 (hdc ω).abs (NNReal.coe_nonneg (N : ℝ≥0))
      have h2 : ∫ u in (0 : ℝ)..(N : ℝ≥0).val,
            |b (Y u.toNNReal ω) i - b (Y' u.toNNReal ω) i| ^ 2 ≤
          L ^ 2 * ∫ u in (0 : ℝ)..(N : ℝ≥0).val, ‖Y u.toNNReal ω - Y' u.toNNReal ω‖ ^ 2 := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_mono_on (NNReal.coe_nonneg _)
          (((hdc ω).abs.pow 2).intervalIntegrable _ _)
          ((continuous_const.mul (((hYc ω).sub (hY'c ω)).norm.pow 2)).intervalIntegrable _ _)
          fun u _ => ?_
        have h3 := coord_sq_le_norm_sq (b (Y u.toNNReal ω) - b (Y' u.toNNReal ω)) i
        have h4 : ‖b (Y u.toNNReal ω) - b (Y' u.toNNReal ω)‖ ^ 2 ≤
            (L * ‖Y u.toNNReal ω - Y' u.toNNReal ω‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hL _ _).2 2
        rw [PiLp.sub_apply] at h3
        rw [sq_abs]
        nlinarith
      have hN0 : (0 : ℝ) ≤ ((N : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
      calc g i ω ^ 2 ≤ ((N : ℝ≥0) : ℝ) * ∫ u in (0 : ℝ)..(N : ℝ≥0).val,
            |b (Y u.toNNReal ω) i - b (Y' u.toNNReal ω) i| ^ 2 := h1
        _ ≤ ((N : ℝ≥0) : ℝ) * (L ^ 2 * ∫ u in (0 : ℝ)..(N : ℝ≥0).val,
            ‖Y u.toNNReal ω - Y' u.toNNReal ω‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hN0
        _ = N * (L ^ 2 * ∫ u in (0 : ℝ)..(N : ℝ≥0).val,
            ‖Y u.toNNReal ω - Y' u.toNNReal ω‖ ^ 2) := by simp
    have hsw := lint_swap (P := P) (F := fun u ω => ‖Y u ω - Y' u ω‖ ^ 2)
      (fun ω => ((hY.2.1 ω).sub (hY'.2.1 ω)).norm.pow 2)
      (fun u => ((hY.1 u).sub (hY'.1 u)).norm.pow_const 2) (fun _ _ => sq_nonneg _) (N : ℝ≥0)
    have hE : ∫⁻ ω, ENNReal.ofReal (g i ω ^ 2) ∂P ≤ ENNReal.ofReal (N * (N * (L ^ 2 * B))) := by
      have hNL : (0 : ℝ) ≤ N * L ^ 2 := by positivity
      calc ∫⁻ ω, ENNReal.ofReal (g i ω ^ 2) ∂P
          ≤ ∫⁻ ω, ENNReal.ofReal (N * L ^ 2) * ENNReal.ofReal
              (∫ u in (0 : ℝ)..(N : ℝ≥0).val, ‖Y u.toNNReal ω - Y' u.toNNReal ω‖ ^ 2) ∂P := by
            refine lintegral_mono fun ω => ?_
            rw [← ENNReal.ofReal_mul hNL]
            refine ENNReal.ofReal_le_ofReal ((hgsq ω).trans (le_of_eq ?_))
            ring
        _ = ENNReal.ofReal (N * L ^ 2) * ∫⁻ u in Ioc 0 ((N : ℝ≥0) : ℝ),
              ∫⁻ ω, ENNReal.ofReal (‖Y u.toNNReal ω - Y' u.toNNReal ω‖ ^ 2) ∂P := by
            simp only [NNReal.val_eq_coe] at hsw ⊢
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hsw]
        _ ≤ ENNReal.ofReal (N * L ^ 2) * ∫⁻ _u in Ioc 0 ((N : ℝ≥0) : ℝ), ENNReal.ofReal B := by
            refine mul_le_mul' le_rfl (setLIntegral_mono measurable_const fun u hu => ?_)
            refine hB _ ?_
            have : u ≤ (N : ℝ) := by simpa using hu.2
            exact (Real.toNNReal_le_iff_le_coe).2 (by simpa using this)
        _ = ENNReal.ofReal (N * (N * (L ^ 2 * B))) := by
            rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul hB0,
              ← ENNReal.ofReal_mul hNL]
            congr 1
            simp
            ring
    have hsub2 : Eb i ⊆ {ω | ENNReal.ofReal (lam ^ 2) ≤ ENNReal.ofReal (g i ω ^ 2)} := by
      intro ω hω
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hlam.le (le_of_lt hω) 2)
    have hmk := mul_meas_ge_le_lintegral₀ (μ := P)
      (f := fun ω => ENNReal.ofReal (g i ω ^ 2)) (hgm.pow_const 2).ennreal_ofReal.aemeasurable
      (ENNReal.ofReal (lam ^ 2))
    have hl2 : 0 < lam ^ 2 := by positivity
    calc P (Eb i) ≤ P {ω | ENNReal.ofReal (lam ^ 2) ≤ ENNReal.ofReal (g i ω ^ 2)} :=
          measure_mono hsub2
      _ ≤ ENNReal.ofReal (N * (N * (L ^ 2 * B))) / ENNReal.ofReal (lam ^ 2) := by
          rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hl2).ne')
            (Or.inl ENNReal.ofReal_ne_top), mul_comm]
          exact hmk.trans hE
      _ = ENNReal.ofReal (N * (N * (L ^ 2 * B)) / lam ^ 2) :=
          (ENNReal.ofReal_div_of_pos hl2).symm
  have ha : 0 ≤ 2 * d * N * (L ^ 2 * B) / lam ^ 2 := by positivity
  have hc : 0 ≤ N * (N * (L ^ 2 * B)) / lam ^ 2 := by positivity
  calc _ ≤ P ((⋃ p, EJ p) ∪ ⋃ i, Eb i) := measure_mono hsub
    _ ≤ P (⋃ p, EJ p) + P (⋃ i, Eb i) := measure_union_le _ _
    _ ≤ ∑ p, P (EJ p) + ∑ i, P (Eb i) :=
        add_le_add (measure_iUnion_fintype_le P _) (measure_iUnion_fintype_le P _)
    _ ≤ ∑ _p : Fin d × Fin d, ENNReal.ofReal (2 * d * N * (L ^ 2 * B) / lam ^ 2) +
          ∑ _i : Fin d, ENNReal.ofReal (N * (N * (L ^ 2 * B)) / lam ^ 2) :=
        add_le_add (Finset.sum_le_sum fun p _ => hJprob p) (Finset.sum_le_sum fun i _ => hbprob i)
    _ = ENNReal.ofReal ((d * d * (2 * d * N * (L ^ 2 * B)) + d * (N * (N * (L ^ 2 * B)))) /
          lam ^ 2) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => ha,
          ← ENNReal.ofReal_sum_of_nonneg fun _ _ => hc,
          ← ENNReal.ofReal_add (Finset.sum_nonneg fun _ _ => ha)
            (Finset.sum_nonneg fun _ _ => hc)]
        congr 1
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring

end QM
end ItoLib

end FlatM_QM
-- ===== QN =====
section FlatM_QN
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Nat
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QN
/-! Clause 1 toolkit (E4, part 5): almost-sure geometric convergence of the Picard iterates. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem picard_summable (A Q : ℝ) (D : ℝ) (hD : 0 < D) :
    Summable fun k : ℕ => A * (Q ^ k / k !) / (((1 / 2 : ℝ) ^ (k + 1) / D) ^ 2) := by
  have h := (Real.summable_pow_div_factorial (4 * Q)).mul_left (4 * D ^ 2 * A)
  refine h.congr fun k => ?_
  have h4 : ((1 / 2 : ℝ) ^ (k + 1)) ^ 2 = (1 / 4) ^ (k + 1) := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [div_pow, h4]
  have hf : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have e : (1 / 4 : ℝ) ^ k * 4 ^ k = 1 := by rw [← mul_pow]; norm_num
  field_simp
  linear_combination (A * Q ^ k) * e

set_option maxHeartbeats 1000000 in
/-- Almost surely, on every horizon, the Picard increments are eventually below `2^-k`. -/
theorem picard_ae_geom {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {s : SDEState d → SDEDiffusion d} {b : SDEState d → SDEState d} (hs : Continuous s)
    (hb : Continuous b) {S : ℝ} (hsS : ∀ x p, |s x p| ≤ S) (hbS : ∀ x i, |b x i| ≤ S)
    {L : ℝ} (hL : ∀ x y, ‖s x - s y‖ ≤ L * ‖x - y‖ ∧ ‖b x - b y‖ ≤ L * ‖x - y‖) :
    ∀ᵐ ω ∂P, ∀ N : ℕ, ∃ K : ℕ, ∀ k, K ≤ k → ∀ t : ℝ≥0, t ≤ N → ∀ i,
      |picIter P W x₀ s b (k + 1) t ω i - picIter P W x₀ s b k t ω i| ≤ (1 / 2 : ℝ) ^ k := by
  rw [ae_all_iff]
  intro N
  have hG := goodProc_picIter hW x₀ hs hb hsS
  set M : ℝ := 2 * d * (d * d * (N * S ^ 2)) + 2 * (d * (N ^ 2 * S ^ 2)) with hMdef
  set K : ℝ := 2 * (d + N) * L ^ 2 with hKdef
  have hM : 0 ≤ M := by rw [hMdef]; positivity
  have hK : 0 ≤ K := by rw [hKdef]; positivity
  set B : ℕ → ℝ := fun k => M * (K * N) ^ k / k ! with hBdef
  have hB0 : ∀ k, 0 ≤ B k := fun k =>
    div_nonneg (mul_nonneg hM (pow_nonneg (mul_nonneg hK (Nat.cast_nonneg _)) _)) (Nat.cast_nonneg _)
  set lam : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ (k + 1) / (d + 1) with hlam
  have hlam0 : ∀ k, 0 < lam k := fun k => div_pos (pow_pos (by norm_num) _) (by positivity)
  set E : ℕ → Set Ω := fun k => {ω | ∃ t : ℝ≥0, t ≤ N ∧ ∃ i, (d + 1) * lam k <
      |picStep P W x₀ s b (picIter P W x₀ s b (k + 1)) t ω i -
        picStep P W x₀ s b (picIter P W x₀ s b k) t ω i|} with hE
  set C : ℕ → ℝ := fun k => (d * d * (2 * d * N * (L ^ 2 * B k)) +
      d * (N * (N * (L ^ 2 * B k)))) / lam k ^ 2 with hC
  have hPE : ∀ k, P (E k) ≤ ENNReal.ofReal (C k) := by
    intro k
    refine picStep_dev_prob hW x₀ hs hb hsS hL (hG (k + 1)) (hG k) N (hB0 k) (fun t ht => ?_)
      (hlam0 k)
    have h := picard_moment hW x₀ hs hb hsS hbS hL (N : ℝ≥0) k t ht
    push_cast at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have htN : (t : ℝ) ≤ N := by exact_mod_cast ht
    have : (K * t) ^ k ≤ (K * N) ^ k :=
      pow_le_pow_left₀ (mul_nonneg hK t.2) (mul_le_mul_of_nonneg_left htN hK) k
    show _ ≤ M * (K * N) ^ k / (Nat.factorial k : ℝ)
    rw [hMdef, hKdef] at *
    gcongr
  have hCs : Summable C := by
    have h := picard_summable ((d * d * (2 * d * N * L ^ 2) + d * (N * (N * L ^ 2))) * M)
      (K * N) (d + 1) (by positivity)
    refine h.congr fun k => ?_
    simp only [hC, hBdef, hlam]
    ring
  have hC0 : ∀ k, 0 ≤ C k := fun k => by
    have h2 : 0 ≤ L ^ 2 * B k := mul_nonneg (sq_nonneg L) (hB0 k)
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    exact div_nonneg (add_nonneg (mul_nonneg (mul_nonneg hd hd) (mul_nonneg (by positivity) h2))
      (mul_nonneg hd (mul_nonneg hN (mul_nonneg hN h2)))) (sq_nonneg _)
  have hsum : ∑' k, P (E k) ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∑' k, ENNReal.ofReal (C k)) ?_ (ENNReal.tsum_le_tsum hPE)
    rw [← ENNReal.ofReal_tsum_of_nonneg hC0 hCs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨K0, hK0⟩ := eventually_atTop.1 hω
  refine ⟨K0 + 1, fun k hk t ht i => ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hn := hK0 k' (by omega)
  simp only [hE, mem_setOf_eq, not_exists, not_and, not_lt] at hn
  have h := hn t ht i
  have hd : (d : ℝ) + 1 ≠ 0 := by positivity
  simp only [hlam] at h
  rw [mul_div_cancel₀ _ hd] at h
  exact h

end QN
end ItoLib

end FlatM_QN
-- ===== QO =====
section FlatM_QO
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QO
/-! Clause 1 toolkit (E4, part 6): the Picard limit process. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem picIter_time_zero {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {s : SDEState d → SDEDiffusion d} {b : SDEState d → SDEState d} (hs : Continuous s)
    (hb : Continuous b) {S : ℝ} (hsS : ∀ x p, |s x p| ≤ S) (k : ℕ) (ω : Ω) :
    picIter P W x₀ s b k 0 ω = x₀ := by
  cases k with
  | zero => rfl
  | succ k =>
    have hG := goodProc_picIter hW x₀ hs hb hsS k
    ext i
    rw [picIter_succ, picStep_apply]
    have h0 : ∀ j, cIto P W x₀ j (fun u ω => s (picIter P W x₀ s b k u ω) (i, j)) 0 ω = 0 :=
      fun j =>
        let h := goodProc_coef hG (coordS_continuous hs (i, j))
        (cIto_spec hW x₀ j h.1 h.2.1 h.2.2 (fun u ω => hsS _ _)).2.2.2.1 ω
    simp [h0]

set_option maxHeartbeats 1000000 in
/-- The Picard iterates converge, almost surely and for every time, to a continuous adapted
process started at `x₀`. -/
theorem picard_limit {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {s : SDEState d → SDEDiffusion d} {b : SDEState d → SDEState d} (hs : Continuous s)
    (hb : Continuous b) {S : ℝ} (hsS : ∀ x p, |s x p| ≤ S) (hbS : ∀ x i, |b x i| ≤ S)
    {L : ℝ} (hL : ∀ x y, ‖s x - s y‖ ≤ L * ‖x - y‖ ∧ ‖b x - b y‖ ≤ L * ‖x - y‖) :
    ∃ X : ℝ≥0 → Ω → SDEState d, GoodProc P W x₀ X ∧ (∀ ω, X 0 ω = x₀) ∧
      ∀ᵐ ω ∂P, ∀ t, Tendsto (fun k => picIter P W x₀ s b k t ω) atTop (𝓝 (X t ω)) := by
  classical
  have hae := picard_ae_geom hW x₀ hs hb hsS hbS hL
  have hG := goodProc_picIter hW x₀ hs hb hsS
  set Bad : Set Ω := {ω | ¬ ∀ N : ℕ, ∃ K : ℕ, ∀ k, K ≤ k → ∀ t : ℝ≥0, t ≤ N → ∀ i,
      |picIter P W x₀ s b (k + 1) t ω i - picIter P W x₀ s b k t ω i| ≤ (1 / 2 : ℝ) ^ k}
    with hBad
  have hBad0 : P Bad = 0 := by rw [ae_iff] at hae; exact hae
  set N0 := toMeasurable P Bad with hN0
  have hN0null : P N0 = 0 := by rw [hN0, measure_toMeasurable]; exact hBad0
  set G : Set Ω := N0ᶜ with hGdef
  have hGgood : ∀ ω ∈ G, ∀ N : ℕ, ∃ K : ℕ, ∀ k, K ≤ k → ∀ t : ℝ≥0, t ≤ N → ∀ i,
      |picIter P W x₀ s b (k + 1) t ω i - picIter P W x₀ s b k t ω i| ≤ (1 / 2 : ℝ) ^ k := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable P _ h)
  have hlim : ∀ ω ∈ G, ∀ i, (∀ t, CauchySeq fun k => picIter P W x₀ s b k t ω i) ∧
      Continuous (fun t => limUnder atTop fun k => picIter P W x₀ s b k t ω i) := by
    intro ω hω i
    refine geom_cauchy_limit' (F := fun k t => picIter P W x₀ s b k t ω i)
      (fun k => ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).comp ((hG k).2.1 ω)) ?_
    intro N
    obtain ⟨K, hK⟩ := hGgood ω hω N
    exact ⟨K, fun k hk t ht => hK k hk t ht i⟩
  set X : ℝ≥0 → Ω → SDEState d := fun t ω => if ω ∈ G then
      WithLp.toLp 2 (fun i => limUnder atTop fun k => picIter P W x₀ s b k t ω i) else x₀
    with hX
  have htend : ∀ ω ∈ G, ∀ t,
      Tendsto (fun k => picIter P W x₀ s b k t ω) atTop (𝓝 (X t ω)) := by
    intro ω hω t
    simp only [hX, hω, if_true]
    have h1 : Tendsto (fun k => fun i => picIter P W x₀ s b k t ω i) atTop
        (𝓝 (fun i => limUnder atTop fun k => picIter P W x₀ s b k t ω i)) :=
      tendsto_pi_nhds.2 fun i => ((hlim ω hω i).1 t).tendsto_limUnder
    exact ((PiLp.continuous_toLp 2 _).tendsto _).comp h1
  have hGm : MeasurableSet G := (measurableSet_toMeasurable P _).compl
  have hGmt : ∀ t, MeasurableSet[completedBrownianPast P W (fun _ => x₀) t] G := fun t => by
    refine MeasurableSet.compl ?_
    refine (le_sup_right : MeasurableSpace.generateFrom
      {A | ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ A ⊆ N} ≤ _) _ ?_
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨N0, measurableSet_toMeasurable P _, hN0null, subset_rfl⟩
  have hev : ∀ t ω, Tendsto (fun k => if ω ∈ G then picIter P W x₀ s b k t ω else x₀) atTop
      (𝓝 (X t ω)) := by
    intro t ω
    by_cases hω : ω ∈ G
    · simp only [hω, if_true]; exact htend ω hω t
    · simp only [hX, hω, if_false]; exact tendsto_const_nhds
  refine ⟨X, ⟨fun t => ?_, fun ω => ?_, fun t => ?_⟩, fun ω => ?_, ?_⟩
  · exact measurable_of_tendsto_metrizable
      (fun k => Measurable.ite hGm ((hG k).1 t) measurable_const) (tendsto_pi_nhds.2 (hev t))
  · by_cases hω : ω ∈ G
    · simp only [hX, hω, if_true]
      exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => (hlim ω hω i).2)
    · simp only [hX, hω, if_false]; exact continuous_const
  · have hfm : ∀ k, Measurable[completedBrownianPast P W (fun _ => x₀) t]
        (fun ω => if ω ∈ G then picIter P W x₀ s b k t ω else x₀) := fun k =>
      Measurable.ite (hGmt t) ((hG k).2.2 t) measurable_const
    exact @measurable_of_tendsto_metrizable Ω (SDEState d)
      (completedBrownianPast P W (fun _ => x₀) t) _ _ _ _ _ _ hfm (tendsto_pi_nhds.2 (hev t))
  · by_cases hω : ω ∈ G
    · refine tendsto_nhds_unique (htend ω hω 0) ?_
      simp only [picIter_time_zero hW x₀ hs hb hsS]
      exact tendsto_const_nhds
    · simp only [hX, hω, if_false]
  · have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
      rw [ae_iff]; simpa [hGdef] using hN0null
    filter_upwards [hGae] with ω hω
    exact htend ω hω

end QO
end ItoLib

end FlatM_QO
-- ===== QP =====
section FlatM_QP
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QP
/-! Clause 1 toolkit (E4, part 7): the Picard limit solves the SDE (bounded Lipschitz case). -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem sdiff_sq_le {s : SDEState d → SDEDiffusion d} {S : ℝ} (hsS : ∀ x p, |s x p| ≤ S)
    (x y : SDEState d) : ‖s x - s y‖ ^ 2 ≤ d * d * (2 * S) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc ∑ p, ((s x - s y) p) ^ 2 ≤ ∑ _p : Fin d × Fin d, (2 * S) ^ 2 := by
        refine Finset.sum_le_sum fun p _ => sq_le_of_abs_le' ?_
        rw [PiLp.sub_apply]
        calc |s x p - s y p| ≤ |s x p| + |s y p| := abs_sub _ _
          _ ≤ 2 * S := by linarith [hsS x p, hsS y p]
    _ = d * d * (2 * S) ^ 2 := by simp

set_option maxHeartbeats 2000000 in
/-- Mean-square convergence of the Ito integrals along a.s. convergent integrand paths. -/
theorem ito_lint_tendsto {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {s : SDEState d → SDEDiffusion d} (hs : Continuous s) {S : ℝ} (hsS : ∀ x p, |s x p| ≤ S)
    {Y : ℕ → ℝ≥0 → Ω → SDEState d} (hY : ∀ k, GoodProc P W x₀ (Y k))
    {X : ℝ≥0 → Ω → SDEState d} (hX : GoodProc P W x₀ X)
    (hconv : ∀ᵐ ω ∂P, ∀ t, Tendsto (fun k => Y k t ω) atTop (𝓝 (X t ω))) (t : ℝ≥0) :
    Tendsto (fun k => ∫⁻ ω, ENNReal.ofReal (∑ p : Fin d × Fin d,
      (cIto P W x₀ p.2 (fun u ω => s (Y k u ω) p) t ω -
        cIto P W x₀ p.2 (fun u ω => s (X u ω) p) t ω) ^ 2) ∂P) atTop (𝓝 0) := by
  have cfY := fun (k : ℕ) (p : Fin d × Fin d) => goodProc_coef (hY k) (coordS_continuous hs p)
  have cfX := fun (p : Fin d × Fin d) => goodProc_coef hX (coordS_continuous hs p)
  have specY := fun (k : ℕ) (p : Fin d × Fin d) =>
    cIto_spec hW x₀ p.2 (cfY k p).1 (cfY k p).2.1 (cfY k p).2.2 (fun u ω => hsS _ _)
  have specX := fun (p : Fin d × Fin d) =>
    cIto_spec hW x₀ p.2 (cfX p).1 (cfX p).2.1 (cfX p).2.2 (fun u ω => hsS _ _)
  have hYc : ∀ k ω, Continuous fun u : ℝ => Y k u.toNNReal ω := fun k ω =>
    ((hY k).2.1 ω).comp continuous_real_toNNReal
  have hXc : ∀ ω, Continuous fun u : ℝ => X u.toNNReal ω := fun ω =>
    (hX.2.1 ω).comp continuous_real_toNNReal
  set Q : ℕ → Ω → ℝ := fun k ω =>
    ∫ u in (0 : ℝ)..t.val, ‖s (Y k u.toNNReal ω) - s (X u.toNNReal ω)‖ ^ 2 with hQ
  have hqc : ∀ k ω, Continuous fun u : ℝ => ‖s (Y k u.toNNReal ω) - s (X u.toNNReal ω)‖ ^ 2 :=
    fun k ω => ((hs.comp (hYc k ω)).sub (hs.comp (hXc ω))).norm.pow 2
  -- step 1: Ito isometry bound
  have hle : ∀ k, ∫⁻ ω, ENNReal.ofReal (∑ p : Fin d × Fin d,
      (cIto P W x₀ p.2 (fun u ω => s (Y k u ω) p) t ω -
        cIto P W x₀ p.2 (fun u ω => s (X u ω) p) t ω) ^ 2) ∂P ≤
      ∫⁻ ω, ENNReal.ofReal (Q k ω) ∂P := by
    intro k
    have hJm : ∀ p : Fin d × Fin d, Measurable fun ω =>
        (cIto P W x₀ p.2 (fun u ω => s (Y k u ω) p) t ω -
          cIto P W x₀ p.2 (fun u ω => s (X u ω) p) t ω) ^ 2 :=
      fun p => (((specY k p).2.2.1 t).sub ((specX p).2.2.1 t)).pow_const 2
    have hIm : ∀ p : Fin d × Fin d, Measurable fun ω => ENNReal.ofReal (∫ u in (0 : ℝ)..t.val,
        (s (Y k u.toNNReal ω) p - s (X u.toNNReal ω) p) ^ 2) := fun p =>
      (measurable_intervalIntegral_of_continuous _ t
        (H := fun u ω => (s (Y k u ω) p - s (X u ω) p) ^ 2)
        (fun u _ => (((cfY k p).2.1 u).sub ((cfX p).2.1 u)).pow_const 2)
        (fun ω => (((cfY k p).2.2 ω).sub ((cfX p).2.2 ω)).pow 2)).ennreal_ofReal
    calc _ = ∑ p : Fin d × Fin d, ∫⁻ ω, ENNReal.ofReal
            ((cIto P W x₀ p.2 (fun u ω => s (Y k u ω) p) t ω -
              cIto P W x₀ p.2 (fun u ω => s (X u ω) p) t ω) ^ 2) ∂P := by
          rw [← lintegral_finsetSum _ fun p _ => (hJm p).ennreal_ofReal]
          refine lintegral_congr fun ω => ?_
          rw [ENNReal.ofReal_sum_of_nonneg fun p _ => sq_nonneg _]
      _ ≤ ∑ p : Fin d × Fin d, ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..t.val,
            (s (Y k u.toNNReal ω) p - s (X u.toNNReal ω) p) ^ 2) ∂P := by
          refine Finset.sum_le_sum fun p _ => ?_
          exact ito_sq_lint hW x₀ p.2 (cfY k p).1 (cfY k p).2.1 (cfY k p).2.2
            (fun u ω => hsS _ _) (specY k p).2.2.2.2 (cfX p).1 (cfX p).2.1
            (cfX p).2.2 (fun u ω => hsS _ _) (specX p).2.2.2.2 t
      _ = ∫⁻ ω, ENNReal.ofReal (∑ p : Fin d × Fin d, ∫ u in (0 : ℝ)..t.val,
            (s (Y k u.toNNReal ω) p - s (X u.toNNReal ω) p) ^ 2) ∂P := by
          rw [← lintegral_finsetSum _ fun p _ => hIm p]
          refine lintegral_congr fun ω => ?_
          rw [ENNReal.ofReal_sum_of_nonneg fun p _ =>
            intervalIntegral.integral_nonneg t.2 fun u _ => sq_nonneg _]
      _ = ∫⁻ ω, ENNReal.ofReal (Q k ω) ∂P := by
          refine lintegral_congr fun ω => ?_
          congr 1
          have hpc : ∀ p : Fin d × Fin d, Continuous fun u : ℝ =>
              (s (Y k u.toNNReal ω) p - s (X u.toNNReal ω) p) ^ 2 := fun p =>
            (((coordS_continuous hs p).comp (hYc k ω)).sub
              ((coordS_continuous hs p).comp (hXc ω))).pow 2
          rw [← intervalIntegral.integral_finsetSum fun p _ => (hpc p).intervalIntegrable _ _]
          refine intervalIntegral.integral_congr fun u _ => ?_
          simp only
          rw [EuclideanSpace.real_norm_sq_eq]
          simp
  -- step 2: dominated convergence
  have hQm : ∀ k, Measurable fun ω => ENNReal.ofReal (Q k ω) := fun k =>
    (measurable_intervalIntegral_of_continuous _ t
      (H := fun u ω => ‖s (Y k u ω) - s (X u ω)‖ ^ 2)
      (fun u _ => ((hs.measurable.comp ((hY k).1 u)).sub (hs.measurable.comp (hX.1 u))).norm.pow_const 2)
      (fun ω => ((hs.comp ((hY k).2.1 ω)).sub (hs.comp (hX.2.1 ω))).norm.pow 2)).ennreal_ofReal
  have hC0 : (0 : ℝ) ≤ d * d * (2 * S) ^ 2 := by positivity
  have hbound : ∀ k ω, ENNReal.ofReal (Q k ω) ≤ ENNReal.ofReal (t * (d * d * (2 * S) ^ 2)) := by
    intro k ω
    refine ENNReal.ofReal_le_ofReal ?_
    calc Q k ω ≤ ∫ _u in (0 : ℝ)..t.val, d * d * (2 * S) ^ 2 :=
          intervalIntegral.integral_mono_on t.2 ((hqc k ω).intervalIntegrable _ _)
            intervalIntegrable_const fun u _ => sdiff_sq_le hsS _ _
      _ = t * (d * d * (2 * S) ^ 2) := by simp; ring
  have hlimQ : ∀ᵐ ω ∂P, Tendsto (fun k => ENNReal.ofReal (Q k ω)) atTop (𝓝 0) := by
    filter_upwards [hconv] with ω hω
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := 0) (b := t.val) (l := atTop)
      (F := fun k u => ‖s (Y k u.toNNReal ω) - s (X u.toNNReal ω)‖ ^ 2) (f := fun _ => 0)
      (fun _ => d * d * (2 * S) ^ 2)
      (Eventually.of_forall fun k => ((hqc k ω).aestronglyMeasurable))
      (Eventually.of_forall fun k => ae_of_all _ fun u _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact sdiff_sq_le hsS _ _)
      intervalIntegrable_const
      (ae_of_all _ fun u _ => by
        have h1 := (((hs.tendsto _).comp (hω u.toNNReal)).sub
          (tendsto_const_nhds (x := s (X u.toNNReal ω)))).norm.pow 2
        simpa using h1)
    simpa [hQ] using h
  have hlim := tendsto_lintegral_of_dominated_convergence
    (fun _ => ENNReal.ofReal (t * (d * d * (2 * S) ^ 2))) hQm
    (fun k => ae_of_all _ fun ω => hbound k ω)
    (by rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_ne_top) hlimQ
  rw [lintegral_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hle

end QP
end ItoLib

end FlatM_QP
-- ===== QZ4 =====
section FlatM_QZ4
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QZ4
/-! Clause 1 toolkit (E4, final): strong existence for bounded globally Lipschitz coefficients. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem measurable_toLp_coords' {Ω' : Type*} {m : MeasurableSpace Ω'} {ι : Type} [Fintype ι]
    {f : Ω' → ι → ℝ} (h : ∀ i, Measurable[m] fun ω => f ω i) :
    Measurable[m] fun ω => (WithLp.toLp 2 (f ω) : EuclideanSpace ℝ ι) :=
  (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 h)

set_option maxHeartbeats 2000000 in
/-- E4: the SDE with bounded, globally Lipschitz, time-homogeneous coefficients has a strong
solution from any deterministic starting point. -/
theorem picard_solves {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {s : SDEState d → SDEDiffusion d} {b : SDEState d → SDEState d} (hs : Continuous s)
    (hb : Continuous b) {S : ℝ} (hsS : ∀ x p, |s x p| ≤ S) (hbS : ∀ x i, |b x i| ≤ S)
    {L : ℝ} (hL : ∀ x y, ‖s x - s y‖ ≤ L * ‖x - y‖ ∧ ‖b x - b y‖ ≤ L * ‖x - y‖) :
    ∃ X : ℝ≥0 → Ω → SDEState d,
      SolvesBrownianSDE P (fun p => s p.2) (fun p => b p.2) W (fun _ => x₀) X := by
  obtain ⟨X, hX, hX0, hconv⟩ := picard_limit hW x₀ hs hb hsS hbS hL
  have hG := goodProc_picIter hW x₀ hs hb hsS
  have cfX := fun (p : Fin d × Fin d) => goodProc_coef hX (coordS_continuous hs p)
  have specX := fun (p : Fin d × Fin d) =>
    cIto_spec hW x₀ p.2 (cfX p).1 (cfX p).2.1 (cfX p).2.2 (fun u ω => hsS _ _)
  have cfY := fun (k : ℕ) (p : Fin d × Fin d) => goodProc_coef (hG k) (coordS_continuous hs p)
  have specY := fun (k : ℕ) (p : Fin d × Fin d) =>
    cIto_spec hW x₀ p.2 (cfY k p).1 (cfY k p).2.1 (cfY k p).2.2 (fun u ω => hsS _ _)
  set J : ℝ≥0 → Ω → SDEDiffusion d := fun t ω =>
    WithLp.toLp 2 (fun p => cIto P W x₀ p.2 (fun u ω => s (X u ω) p) t ω) with hJ
  set JY : ℕ → ℝ≥0 → Ω → SDEDiffusion d := fun k t ω =>
    WithLp.toLp 2 (fun p => cIto P W x₀ p.2 (fun u ω => s (picIter P W x₀ s b k u ω) p) t ω)
    with hJY
  have hXc : ∀ ω, Continuous fun u : ℝ => X u.toNNReal ω := fun ω =>
    (hX.2.1 ω).comp continuous_real_toNNReal
  -- the equation at a fixed time
  have hfix : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ∀ i, X t ω i = x₀ i + ∑ j, J t ω (i, j) +
      ∫ u in (0 : ℝ)..t.val, b (X u.toNNReal ω) i := by
    intro t
    have hlt := ito_lint_tendsto hW x₀ hs hsS hG hX hconv t
    set F : ℕ → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (∑ p : Fin d × Fin d,
      (cIto P W x₀ p.2 (fun u ω => s (picIter P W x₀ s b k u ω) p) t ω -
        cIto P W x₀ p.2 (fun u ω => s (X u ω) p) t ω) ^ 2) with hF
    have hFm : ∀ k, Measurable (F k) := fun k =>
      (Finset.measurable_sum _ fun p _ =>
        (((specY k p).2.2.1 t).sub ((specX p).2.2.1 t)).pow_const 2).ennreal_ofReal
    have hTIM : TendstoInMeasure P (fun k => JY k t) atTop (J t) := by
      rw [tendstoInMeasure_iff_dist]
      intro ε hε
      have hε2 : ENNReal.ofReal (ε ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
      have hbd : ∀ k, P {ω | ε ≤ dist (JY k t ω) (J t ω)} ≤
          (∫⁻ ω, F k ω ∂P) / ENNReal.ofReal (ε ^ 2) := by
        intro k
        rw [ENNReal.le_div_iff_mul_le (Or.inl hε2) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        refine le_trans (mul_le_mul' le_rfl (measure_mono ?_))
          (mul_meas_ge_le_lintegral₀ (hFm k).aemeasurable (ENNReal.ofReal (ε ^ 2)))
        intro ω hω
        simp only [mem_setOf_eq] at hω ⊢
        refine ENNReal.ofReal_le_ofReal ?_
        rw [dist_eq_norm] at hω
        have h2 := pow_le_pow_left₀ hε.le hω 2
        rw [EuclideanSpace.real_norm_sq_eq] at h2
        simpa [hJY, hJ] using h2
      have hlim := ENNReal.Tendsto.div_const hlt (Or.inr hε2)
      rw [ENNReal.zero_div] at hlim
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun _ => bot_le) hbd
    obtain ⟨ns, hns, hae⟩ := hTIM.exists_seq_tendsto_ae
    filter_upwards [hae, hconv] with ω h1 h2 i
    have hcoord : ∀ {ι : Type} [Fintype ι] (q : ι),
        Continuous fun v : EuclideanSpace ℝ ι => v q := fun q =>
      (continuous_apply q).comp (PiLp.continuous_ofLp 2 _)
    have hns' : Tendsto (fun m => ns m + 1) atTop atTop :=
      (tendsto_add_atTop_nat 1).comp hns.tendsto_atTop
    have hL1 : Tendsto (fun m => picIter P W x₀ s b (ns m + 1) t ω i) atTop (𝓝 (X t ω i)) :=
      (((hcoord i).tendsto _).comp (h2 t)).comp hns'
    have hJl : ∀ j, Tendsto (fun m => cIto P W x₀ j
        (fun u ω => s (picIter P W x₀ s b (ns m) u ω) (i, j)) t ω) atTop (𝓝 (J t ω (i, j))) :=
      fun j => ((hcoord (i, j)).tendsto _).comp h1
    have hbl : Tendsto (fun m => ∫ u in (0 : ℝ)..t.val,
        b (picIter P W x₀ s b (ns m) u.toNNReal ω) i) atTop
        (𝓝 (∫ u in (0 : ℝ)..t.val, b (X u.toNNReal ω) i)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun _ => S) (Eventually.of_forall fun m => ?_)
        (Eventually.of_forall fun m => ae_of_all _ fun u _ => ?_) intervalIntegrable_const
        (ae_of_all _ fun u _ => ?_)
      · exact ((coordB_continuous hb i).comp
          (((hG (ns m)).2.1 ω).comp continuous_real_toNNReal)).aestronglyMeasurable
      · rw [Real.norm_eq_abs]; exact hbS _ _
      · exact ((coordB_continuous hb i).tendsto _).comp ((h2 u.toNNReal).comp hns.tendsto_atTop)
    have hR := (tendsto_const_nhds (x := x₀ i)).add (tendsto_finset_sum Finset.univ
      fun j _ => hJl j) |>.add hbl
    refine tendsto_nhds_unique (hL1.congr fun m => ?_) hR
    rw [picIter_succ, picStep_apply]
  -- all times at once
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, ∀ i, X (q : ℝ).toNNReal ω i = x₀ i +
      ∑ j, J (q : ℝ).toNNReal ω (i, j) +
      ∫ u in (0 : ℝ)..((q : ℝ).toNNReal).val, b (X u.toNNReal ω) i :=
    ae_all_iff.2 fun q => hfix _
  have hJc : ∀ ω, Continuous fun t => J t ω := fun ω =>
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p => (specX p).1 ω)
  refine ⟨X, hX.1, hX.2.1, hX.2.2, ae_of_all _ hX0, J, hJc, fun t => ?_, fun i j => ?_,
    fun t ω i => ?_, ?_⟩
  · exact measurable_toLp_coords' fun p => (specX p).2.1 t
  · exact (specX (i, j)).2.2.2.2
  · exact ((coordB_continuous hb i).comp (hXc ω)).intervalIntegrable _ _
  · filter_upwards [hq] with ω hω
    intro t i
    have hF : Continuous fun t : ℝ≥0 => X t ω i :=
      ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).comp (hX.2.1 ω)
    have hGc : Continuous fun t : ℝ≥0 => x₀ i + ∑ j, J t ω (i, j) +
        ∫ u in (0 : ℝ)..t.val, b (X u.toNNReal ω) i := by
      refine (continuous_const.add (continuous_finsetSum _ fun j _ =>
        ((continuous_apply (i, j)).comp (PiLp.continuous_ofLp 2 _)).comp (hJc ω))).add ?_
      exact (intervalIntegral.continuous_primitive (fun a b' =>
        ((coordB_continuous hb i).comp (hXc ω)).intervalIntegrable a b') 0).comp
        NNReal.continuous_coe
    have hext := Continuous.ext_on denseRange_rat_toNNReal hF hGc (by
      rintro _ ⟨q, rfl⟩
      exact hω q i)
    have := congrFun hext t
    rw [hX0 ω]
    exact this

end QZ4
end ItoLib

end FlatM_QZ4
-- ===== E5A =====
section FlatM_E5A
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E5A
/-! Clause 1 toolkit (E5, part 1): two solutions from the same point, of SDEs whose bounded
coefficients agree on a ball, coincide as long as the first stays in a smaller ball. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end E5A

end ItoLib

end FlatM_E5A
-- ===== E5B =====
section FlatM_E5B
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E5B
/-! Clause 1 toolkit (E5, part 2): gluing a consistent, non-exploding family of truncated
solutions into a global strong solution. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end E5B

end ItoLib

end FlatM_E5B
-- ===== E6F =====
section FlatM_E6F
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6F
/-! Clause 1 toolkit (E6, part 1): `face_rep` for a solution of an SDE whose coefficients only
agree with the Kolmogorov coefficients on a box (truncated systems). -/
open StochKolmogorov.Persist
variable {n : ℕ}

end E6F

end ItoLib

end FlatM_E6F
-- ===== E6P =====
section FlatM_E6P
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6P
/-! Clause 1 toolkit (E6, part 1): `face_rep` for a solution of an SDE whose coefficients only
agree with the Kolmogorov coefficients on a box (truncated systems). -/
open StochKolmogorov.Persist
variable {n : ℕ}

end E6P

end ItoLib

end FlatM_E6P
-- ===== E6Q =====
section FlatM_E6Q
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6Q
/-! Clause 1 toolkit (E6, part 2): a solution of a Kolmogorov-structured SDE started in the
orthant stays in the orthant for all times, almost surely. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end E6Q

end ItoLib

end FlatM_E6Q
-- ===== E6T =====
section FlatM_E6T
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6T
/-! Clause 1 toolkit (E6, part 3): a Kolmogorov-structured truncation of the coefficients:
evaluate the true coefficients at the box projection `boxP (-R) R y`. It is bounded, globally
Lipschitz, equal to the true coefficients on the box, and of the form `y_k * (bounded)`. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end E6T

end ItoLib

end FlatM_E6T
-- ===== V =====
section FlatM_V
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

end FlatM_V
-- ===== W =====
section FlatM_W
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

end FlatM_W
-- ===== Y =====
section FlatM_Y
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M12a
/-! M12a: the test-function machinery of V.lean for a single C² nonnegative function `ψ` of a
linear form `ℓ(x) = Σ_k cv_k x_k`, `Φ(x) = ψ(ℓ x)` (used with `ψ ≈ log(1+·)`). -/

variable {Ω : Type*} {d : ℕ}

variable {ψ : ℝ → ℝ} {cv : SDEState d} [hψ : Fact (ContDiff ℝ 2 ψ)] [hψ0 : Fact (∀ v, 0 ≤ ψ v)]

end M12a


section M12b
/-! M12b: the Lyapunov function `log(1 + cᵀx)` for (1.1): `E ∫₀ᵗ w(X_u) du ≤ log(1 + cᵀx) + log 2 + K t`
with `w = γb + δ₀ Σᵢ (|fᵢ| + gᵢ²)` and `K = max H 0` (`H` of (3.5)). -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M12b

end ItoLib

end FlatM_Y
-- ===== E6L =====
section FlatM_E6L
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6L
/-! Clause 1 toolkit (E6, part 4): the saturated Lyapunov profile `lyS m = hsat m ∘ psiK`,
derivatives of `y ↦ ψ(cᵀy)`, and the time-slot test function
`F(x,y,a) = e^{-a} (Φ(y) + K (T - x_{i0}) - λ) + λ` with its generator. -/
open StochKolmogorov.Persist

variable {n : ℕ}

end E6L

section E6Lb
variable {d : ℕ}

end E6Lb

end ItoLib

end FlatM_E6L
-- ===== E6M =====
section FlatM_E6M
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6M
/-! Clause 1 toolkit (E6, part 5): a maximal inequality without martingale theory. Along a
solution `Y` that stays in a set `D` on which the generator of `Φ ≥ 0` is at most `K`, the
probability that `Φ(Y_s) > λ` for some `s < t` is at most `(Φ(x) + K t) / (λ (1 - e⁻¹))`.
Proof: the Ito formula for `F = e^{-a}(Φ(y) + K (T - s) - λ) + λ`, where the clock `a` runs at
rate `M (Φ(Y) + K (T - s) - λ)⁺` (the time `s` is carried in the `X` slot), and `M → ∞`. -/
variable {n : ℕ}

end E6M

end ItoLib

end FlatM_E6M
-- ===== X41 =====
section FlatM_X41
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! X41 (eq_4_1, finite-`M` part): the minimax step of [SBA11, Lemma 4] for finitely many
boundary ergodic measures, by strict separation of a polytope from the closed negative orthant. -/

end ItoLib

end FlatM_X41
-- ===== E6A =====
section FlatM_E6A
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6A
/-! Clause 1 (E6, assembly): non-explosion of the truncated Kolmogorov systems via the saturated
Lyapunov function `lyS m (cᵀy)` and `exceed_prob_le`, then `glue_solution`. -/

open StochKolmogorov.Persist

variable {n : ℕ}

end E6A

end ItoLib

end FlatM_E6A
-- ===== L31 =====
section FlatM_L31
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz StochKolmogorov.Persist

end ItoLib


end FlatM_L31

open EthierKurtz in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    (x₀ : SDEState d) {s : SDEState d → SDEDiffusion d} {b : SDEState d → SDEState d}
    (hs : Continuous s) (hb : Continuous b) {S : ℝ} (hsS : ∀ x p, |s x p| ≤ S)
    (hbS : ∀ x i, |b x i| ≤ S) {L : ℝ}
    (hL : ∀ x y, ‖s x - s y‖ ≤ L * ‖x - y‖ ∧ ‖b x - b y‖ ≤ L * ‖x - y‖) :
    ∃ X : ℝ≥0 → Ω → SDEState d,
      SolvesBrownianSDE P (fun p => s p.2) (fun p => b p.2) W (fun _ => x₀) X := by
  exact ItoLib.picard_solves hW x₀ hs hb hsS hbS hL
