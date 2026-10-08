-- Prove2me | solution 1 for BalkemaDeHaan.DiscreteDomain.discrete_mem_Dr
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:47:49.685161+00:00
-- url     : https://prove2.me/submissions/9dda9349-eef2-46d7-afe3-c4742e9058e9

import Mathlib
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_ResidualLife
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_PiPC
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_DiscreteLaw

open MeasureTheory Filter Topology


namespace BalkemaDeHaan.DiscreteDomain

/-- the level function `z` with `Π_{p,c}(x) = 1 - exp(-p ⌊1 + z x⌋)` for `x ≥ 0`. -/
noncomputable def zfun (p c x : ℝ) : ℝ :=
  if c = 0 then x / p else Real.log (1 + c * x) / (c * p)

/-- its inverse: `w r` is the point with level `r`; the jumps of `Π_{p,c}` are the `w k`, `k ∈ ℕ`. -/
noncomputable def wfun (p c r : ℝ) : ℝ :=
  if c = 0 then r * p else (Real.exp (c * p * r) - 1) / c

/-- the scaling constant -/
noncomputable def Cfun (p c : ℝ) : ℝ :=
  if c = 0 then 1 / p else c / (Real.exp (c * p) - 1)

lemma piPC_eq_z (p c x : ℝ) (hx : 0 ≤ x) :
    piPC p c x = 1 - Real.exp (-p * ((⌊1 + zfun p c x⌋ : ℤ) : ℝ)) := by
  unfold piPC zfun
  rw [if_neg (not_lt.2 hx)]
  split_ifs <;> rfl

lemma piPC_of_neg (p c x : ℝ) (hx : x < 0) : piPC p c x = 0 := by
  unfold piPC; rw [if_pos hx]

lemma wfun_le_iff (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c) (x : ℝ) (hx : 0 ≤ x) (r : ℝ) :
    wfun p c r ≤ x ↔ r ≤ zfun p c x := by
  unfold wfun zfun
  split_ifs with h
  · rw [le_div_iff₀ hp]
  · have hc' : 0 < c := lt_of_le_of_ne hc (Ne.symm h)
    have h1 : 0 < 1 + c * x := by positivity
    rw [div_le_iff₀ hc', le_div_iff₀ (by positivity)]
    have key : Real.exp (c * p * r) ≤ 1 + c * x ↔ r * (c * p) ≤ Real.log (1 + c * x) := by
      rw [Real.le_log_iff_exp_le h1, show r * (c * p) = c * p * r by ring]
    constructor
    · intro h'; rw [← key]; linarith
    · intro h'; have := key.2 h'; linarith

lemma lt_wfun_iff (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c) (x : ℝ) (hx : 0 ≤ x) (r : ℝ) :
    x < wfun p c r ↔ zfun p c x < r := by
  rw [← not_le, ← not_le, wfun_le_iff p c hp hc x hx]

lemma wfun_zero (p c : ℝ) : wfun p c 0 = 0 := by
  unfold wfun; split_ifs <;> simp

lemma wfun_strictMono (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c) : StrictMono (wfun p c) := by
  intro r r' hr
  unfold wfun
  split_ifs with h
  · exact mul_lt_mul_of_pos_right hr hp
  · have hc' : 0 < c := lt_of_le_of_ne hc (Ne.symm h)
    apply div_lt_div_of_pos_right _ hc'
    have : c * p * r < c * p * r' := mul_lt_mul_of_pos_left hr (by positivity)
    linarith [Real.exp_lt_exp.2 this]

lemma wfun_nonneg (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c) (r : ℝ) (hr : 0 ≤ r) : 0 ≤ wfun p c r := by
  rw [← wfun_zero p c]; exact (wfun_strictMono p c hp hc).monotone hr

lemma zfun_nonneg (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ zfun p c x := by
  rw [← wfun_le_iff p c hp hc x hx, wfun_zero]; exact hx

/-- on `[w k, w (k+1))` the limit law is constant `1 - e^{-p(k+1)}`. -/
lemma piPC_eq_on (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c) (k : ℕ) (x : ℝ)
    (h1 : wfun p c k ≤ x) (h2 : x < wfun p c (k + 1)) :
    piPC p c x = 1 - Real.exp (-p * (k + 1)) := by
  have hx : 0 ≤ x := le_trans (wfun_nonneg p c hp hc k (Nat.cast_nonneg k)) h1
  rw [wfun_le_iff p c hp hc x hx] at h1
  rw [lt_wfun_iff p c hp hc x hx] at h2
  rw [piPC_eq_z p c x hx]
  have : ⌊1 + zfun p c x⌋ = (k : ℤ) + 1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  rw [this]; push_cast; ring_nf

/-- every `x ≥ 0` lies in some `[w k, w (k+1))`. -/
lemma exists_level (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c) (x : ℝ) (hx : 0 ≤ x) :
    ∃ k : ℕ, wfun p c k ≤ x ∧ x < wfun p c (k + 1) := by
  refine ⟨⌊zfun p c x⌋₊, ?_, ?_⟩
  · rw [wfun_le_iff p c hp hc x hx]; exact Nat.floor_le (zfun_nonneg p c hp hc x hx)
  · rw [lt_wfun_iff p c hp hc x hx]; exact Nat.lt_floor_add_one _

lemma piPC_continuousAt_of_neg (p c x : ℝ) (hx : x < 0) : ContinuousAt (piPC p c) x := by
  have : piPC p c =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact piPC_of_neg p c y hy
  exact continuousAt_const.congr this.symm

lemma piPC_continuousAt_of_mem (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c) (k : ℕ) (x : ℝ)
    (h1 : wfun p c k < x) (h2 : x < wfun p c (k + 1)) : ContinuousAt (piPC p c) x := by
  have : piPC p c =ᶠ[𝓝 x] fun _ => 1 - Real.exp (-p * (k + 1)) := by
    filter_upwards [Ioo_mem_nhds h1 h2] with y hy
    exact piPC_eq_on p c hp hc k y hy.1.le hy.2
  exact continuousAt_const.congr this.symm

/-- the `w k` are discontinuity points of `Π_{p,c}`. -/
lemma piPC_not_continuousAt (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c) (k : ℕ) :
    ¬ ContinuousAt (piPC p c) (wfun p c k) := by
  intro hcont
  have hval : piPC p c (wfun p c k) = 1 - Real.exp (-p * (k + 1)) :=
    piPC_eq_on p c hp hc k _ le_rfl (wfun_strictMono p c hp hc (by linarith))
  have hleft : Tendsto (piPC p c) (𝓝[<] (wfun p c k)) (𝓝 (piPC p c (wfun p c k))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have h0 : Tendsto (piPC p c) (𝓝[<] (wfun p c ((0:ℕ):ℝ))) (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [Nat.cast_zero, wfun_zero] at hy
      exact (piPC_of_neg p c y hy).symm
    have := tendsto_nhds_unique hleft h0
    rw [hval] at this
    have : Real.exp (-p * ((0:ℕ) + 1)) = 1 := by linarith
    simp at this
    linarith
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hlt : wfun p c j < wfun p c (j + 1 : ℕ) := wfun_strictMono p c hp hc (by push_cast; linarith)
    have h0 : Tendsto (piPC p c) (𝓝[<] (wfun p c (j + 1 : ℕ))) (𝓝 (1 - Real.exp (-p * (j + 1)))) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsLT hlt] with y hy
      exact (piPC_eq_on p c hp hc j y hy.1.le (by push_cast at hy ⊢; exact hy.2)).symm
    have := tendsto_nhds_unique hleft h0
    rw [hval] at this
    have h3 : Real.exp (-p * ((j + 1 : ℕ) + 1)) = Real.exp (-p * (j + 1)) := by linarith
    have h4 := Real.exp_injective h3
    push_cast at h4
    nlinarith

/-- at a continuity point `x ≥ 0`, `x` lies strictly inside some `(w k, w (k+1))`. -/
lemma exists_level_of_continuousAt (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c) (x : ℝ) (hx : 0 ≤ x)
    (hcont : ContinuousAt (piPC p c) x) :
    ∃ k : ℕ, wfun p c k < x ∧ x < wfun p c (k + 1) := by
  obtain ⟨k, h1, h2⟩ := exists_level p c hp hc x hx
  refine ⟨k, lt_of_le_of_ne h1 ?_, h2⟩
  intro heq
  rw [← heq] at hcont
  exact piPC_not_continuousAt p c hp hc k hcont

lemma Cfun_pos (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c) : 0 < Cfun p c := by
  unfold Cfun
  split_ifs with h
  · positivity
  · have hc' : 0 < c := lt_of_le_of_ne hc (Ne.symm h)
    apply div_pos hc'
    have : (0:ℝ) < c * p := by positivity
    linarith [Real.add_one_lt_exp this.ne']

lemma Cfun_wfun_zero (p c : ℝ) : Cfun p c * wfun p c 0 = 0 := by
  rw [wfun_zero, mul_zero]

lemma Cfun_wfun_succ (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c) (k : ℕ) :
    Cfun p c * wfun p c (k + 1) = Cfun p c * wfun p c k + Real.exp (c * p) ^ k := by
  unfold Cfun wfun
  split_ifs with h
  · subst h; simp; field_simp
  · have hc' : 0 < c := lt_of_le_of_ne hc (Ne.symm h)
    have hq : Real.exp (c * p) - 1 ≠ 0 := by
      have : (0:ℝ) < c * p := by positivity
      linarith [Real.add_one_lt_exp this.ne']
    rw [← Real.exp_nat_mul]
    field_simp
    rw [show c * p * ((k:ℝ) + 1) = c * p + k * (c * p) by ring, Real.exp_add]
    ring

lemma te_tail_Ioc_eq (μ : Measure ℝ) [IsFiniteMeasure μ] (t y : ℝ) (hy : 0 ≤ y) :
    (μ (Set.Ioc t (t + y))).toReal = (μ (Set.Ioi t)).toReal - (μ (Set.Ioi (t + y))).toReal := by
  have hU : Set.Ioc t (t + y) ∪ Set.Ioi (t + y) = Set.Ioi t :=
    Set.Ioc_union_Ioi_eq_Ioi (by linarith)
  have hD : Disjoint (Set.Ioc t (t + y)) (Set.Ioi (t + y)) := by
    rw [Set.disjoint_left]; intro x hx hx'; exact absurd hx.2 (not_le.2 hx')
  have := measure_union hD measurableSet_Ioi (μ := μ)
  rw [hU] at this
  rw [this, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]; ring

lemma te_residualCDF_of_nonneg (μ : Measure ℝ) [IsFiniteMeasure μ] (t y : ℝ) (hy : 0 ≤ y)
    (ht : 0 < μ (Set.Ioi t)) :
    BalkemaDeHaan.LimitTypes.residualCDF μ t y =
      1 - (μ (Set.Ioi (t + y))).toReal / (μ (Set.Ioi t)).toReal := by
  unfold BalkemaDeHaan.LimitTypes.residualCDF
  have hpos : 0 < (μ (Set.Ioi t)).toReal := ENNReal.toReal_pos ht.ne' (measure_ne_top _ _)
  rw [te_tail_Ioc_eq μ t y hy, sub_div, div_self hpos.ne']

lemma te_residualCDF_of_neg (μ : Measure ℝ) (t y : ℝ) (hy : y < 0) :
    BalkemaDeHaan.LimitTypes.residualCDF μ t y = 0 := by
  unfold BalkemaDeHaan.LimitTypes.residualCDF
  rw [Set.Ioc_eq_empty (by intro h; linarith), measure_empty, ENNReal.toReal_zero, zero_div]

lemma te_tail_antitone (μ : Measure ℝ) [IsFiniteMeasure μ] {s u : ℝ} (h : s ≤ u) :
    (μ (Set.Ioi u)).toReal ≤ (μ (Set.Ioi s)).toReal :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ioi_subset_Ioi h))


/-! ### discrete laws -/

/-- the tail at the `n`-th jump -/
noncomputable def tailR (ν : Measure ℝ) (t : ℕ → ℝ) (n : ℕ) : ℝ := (ν (Set.Ioi (t n))).toReal

/-- the `n`-th gap -/
noncomputable def gap (t : ℕ → ℝ) (n : ℕ) : ℝ := t (n + 1) - t n

lemma gap_pos {t : ℕ → ℝ} (hmono : StrictMono t) (n : ℕ) : 0 < gap t n := by
  unfold gap; linarith [hmono (Nat.lt_succ_self n)]

lemma disc_tail_pos {ν : Measure ℝ} {t : ℕ → ℝ} (hν : IsDiscreteWithJumps ν t) (s : ℝ) :
    0 < ν (Set.Ioi s) := by
  obtain ⟨_, hlim, _, hatom⟩ := hν
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_gt_atTop s)).exists
  exact lt_of_lt_of_le (hatom n) (measure_mono (Set.singleton_subset_iff.2 hn))

lemma disc_tailR_pos {ν : Measure ℝ} {t : ℕ → ℝ} [IsFiniteMeasure ν]
    (hν : IsDiscreteWithJumps ν t) (n : ℕ) : 0 < tailR ν t n :=
  ENNReal.toReal_pos (disc_tail_pos hν _).ne' (measure_ne_top _ _)

lemma disc_Ioc_null {ν : Measure ℝ} {t : ℕ → ℝ} (hν : IsDiscreteWithJumps ν t) (s u : ℝ)
    (h : ∀ n, t n ∉ Set.Ioc s u) : ν (Set.Ioc s u) = 0 := by
  apply measure_mono_null _ hν.2.2.1
  intro x hx hx'
  obtain ⟨n, rfl⟩ := hx'
  exact h n hx

lemma disc_Ioi_eq {ν : Measure ℝ} {t : ℕ → ℝ} (hν : IsDiscreteWithJumps ν t) (s u : ℝ)
    (hsu : s ≤ u) (h : ∀ n, t n ∉ Set.Ioc s u) : ν (Set.Ioi s) = ν (Set.Ioi u) := by
  apply le_antisymm
  · calc ν (Set.Ioi s) = ν (Set.Ioc s u ∪ Set.Ioi u) := by rw [Set.Ioc_union_Ioi_eq_Ioi hsu]
      _ ≤ ν (Set.Ioc s u) + ν (Set.Ioi u) := measure_union_le _ _
      _ = ν (Set.Ioi u) := by rw [disc_Ioc_null hν s u h, zero_add]
  · exact measure_mono (Set.Ioi_subset_Ioi hsu)

/-- on `[t n, t (n+1))` the tail is constant. -/
lemma disc_Ioi_eq_of_mem {ν : Measure ℝ} {t : ℕ → ℝ} (hν : IsDiscreteWithJumps ν t) (n : ℕ)
    (s : ℝ) (h1 : t n ≤ s) (h2 : s < t (n + 1)) : ν (Set.Ioi s) = ν (Set.Ioi (t n)) := by
  symm
  apply disc_Ioi_eq hν _ _ h1
  intro m hm
  have hnm : n < m := hν.1.lt_iff_lt.1 (by linarith [hm.1])
  have : t (n + 1) ≤ t m := hν.1.monotone hnm
  linarith [hm.2]

lemma disc_exists_idx {t : ℕ → ℝ} (hlim : Tendsto t atTop atTop) (s : ℝ) :
    ∃ n, s < t (n + 1) := by
  obtain ⟨n, hn⟩ := ((hlim.comp (tendsto_add_atTop_nat 1)).eventually (eventually_gt_atTop s)).exists
  exact ⟨n, hn⟩

/-- the index `N` with `s < t (N+1)`, and `t N ≤ s` when `t 0 ≤ s`. -/
noncomputable def idx {t : ℕ → ℝ} (hlim : Tendsto t atTop atTop) (s : ℝ) : ℕ :=
  Nat.find (disc_exists_idx hlim s)

lemma idx_lt {t : ℕ → ℝ} (hlim : Tendsto t atTop atTop) (s : ℝ) : s < t (idx hlim s + 1) :=
  Nat.find_spec (disc_exists_idx hlim s)

lemma le_idx {t : ℕ → ℝ} (hlim : Tendsto t atTop atTop) (hmono : Monotone t) (s : ℝ) (m : ℕ)
    (hm : t m ≤ s) : m ≤ idx hlim s := by
  unfold idx
  rw [Nat.le_find_iff]
  intro j hj
  exact not_lt.2 (le_trans (hmono (by omega : j + 1 ≤ m)) hm)

lemma idx_le {t : ℕ → ℝ} (hlim : Tendsto t atTop atTop) (s : ℝ) (hs : t 0 ≤ s) :
    t (idx hlim s) ≤ s := by
  by_contra h
  push_neg at h
  rcases Nat.eq_zero_or_pos (idx hlim s) with h0 | h0
  · rw [h0] at h; linarith
  · obtain ⟨j, hj⟩ : ∃ j, idx hlim s = j + 1 := ⟨idx hlim s - 1, by omega⟩
    have := Nat.find_min (disc_exists_idx hlim s) (show j < idx hlim s by omega)
    rw [← hj] at this
    exact this h

lemma idx_tendsto {t : ℕ → ℝ} (hlim : Tendsto t atTop atTop) (hmono : Monotone t) :
    Tendsto (idx hlim) atTop atTop :=
  tendsto_atTop_atTop.2 fun m => ⟨t m, fun s hs => le_idx hlim hmono s m hs⟩

/-- `R_{n+k}/R_n → e^{-pk}` -/
lemma tailRatio_pow {ν : Measure ℝ} {t : ℕ → ℝ} [IsFiniteMeasure ν] {p : ℝ}
    (hν : IsDiscreteWithJumps ν t) (h : TailRatio ν t p) (k : ℕ) :
    Tendsto (fun n => tailR ν t (n + k) / tailR ν t n) atTop (𝓝 (Real.exp (-p) ^ k)) := by
  induction k with
  | zero =>
    simp only [Nat.add_zero, pow_zero]
    apply tendsto_const_nhds.congr
    intro n; rw [div_self (disc_tailR_pos hν n).ne']
  | succ k ih =>
    have h1 : Tendsto (fun n => tailR ν t (n + k + 1) / tailR ν t (n + k)) atTop
        (𝓝 (Real.exp (-p))) := h.comp (tendsto_add_atTop_nat k)
    have := h1.mul ih
    rw [pow_succ, mul_comm]
    apply this.congr
    intro n
    have := (disc_tailR_pos hν (n + k)).ne'
    have := (disc_tailR_pos hν n).ne'
    rw [show n + (k + 1) = n + k + 1 by ring]
    field_simp

/-- `g_{n+k}/g_n → q^k` -/
lemma gapRatio_pow {t : ℕ → ℝ} {p c : ℝ} (hmono : StrictMono t) (h : GapRatio t p c) (k : ℕ) :
    Tendsto (fun n => gap t (n + k) / gap t n) atTop (𝓝 (Real.exp (c * p) ^ k)) := by
  induction k with
  | zero =>
    simp only [Nat.add_zero, pow_zero]
    apply tendsto_const_nhds.congr
    intro n; rw [div_self (gap_pos hmono n).ne']
  | succ k ih =>
    have h1 : Tendsto (fun n => gap t (n + k + 1) / gap t (n + k)) atTop
        (𝓝 (Real.exp (c * p))) := by
      rw [mul_comm c p]
      exact h.comp (tendsto_add_atTop_nat k)
    have := h1.mul ih
    rw [pow_succ, mul_comm]
    apply this.congr
    intro n
    have := (gap_pos hmono (n + k)).ne'
    have := (gap_pos hmono n).ne'
    rw [show n + (k + 1) = n + k + 1 by ring]
    field_simp

/-- `(t_{n+k} - t_n)/g_n → C w_k` -/
lemma gap_sum {t : ℕ → ℝ} {p c : ℝ} (hp : 0 < p) (hc : 0 ≤ c) (hmono : StrictMono t)
    (h : GapRatio t p c) (k : ℕ) :
    Tendsto (fun n => (t (n + k) - t n) / gap t n) atTop (𝓝 (Cfun p c * wfun p c k)) := by
  induction k with
  | zero =>
    simp only [Nat.add_zero, sub_self, zero_div, Nat.cast_zero, Cfun_wfun_zero]
    exact tendsto_const_nhds
  | succ k ih =>
    have := ih.add (gapRatio_pow hmono h k)
    rw [← Cfun_wfun_succ p c hp hc k] at this
    push_cast
    apply this.congr
    intro n
    have := (gap_pos hmono n).ne'
    rw [show n + (k + 1) = n + k + 1 by ring]
    unfold gap
    field_simp
    ring

/-- A discrete law with (12a) and (12b) lies in `D_r(Π_{p,c})`. -/
theorem discrete_mem_Dr_core (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℕ → ℝ)
    (hν : IsDiscreteWithJumps ν t) (h12a : GapRatio t p c) (h12b : TailRatio ν t p) :
    InDr ν (piPC p c) := by
  have hmono := hν.1
  have hlim := hν.2.1
  have hC := Cfun_pos p c hp hc
  refine ⟨fun s => disc_tail_pos hν s,
    fun s => Cfun p c * gap t (idx hlim s + 1), fun s => t (idx hlim s + 1) - s,
    fun s => mul_pos hC (gap_pos hmono _), ?_⟩
  intro x hx
  show Tendsto (fun s => BalkemaDeHaan.LimitTypes.residualCDF ν s
    (t (idx hlim s + 1) - s + x * (Cfun p c * gap t (idx hlim s + 1)))) atTop (𝓝 (piPC p c x))
  rcases lt_or_ge x 0 with hxneg | hxnn
  · rw [piPC_of_neg p c x hxneg]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (t 0)] with s hs
    symm
    by_cases hy : 0 ≤ t (idx hlim s + 1) - s + x * (Cfun p c * gap t (idx hlim s + 1))
    · unfold BalkemaDeHaan.LimitTypes.residualCDF
      rw [disc_Ioc_null hν, ENNReal.toReal_zero, zero_div]
      intro m hm
      have hxa : x * (Cfun p c * gap t (idx hlim s + 1)) < 0 :=
        mul_neg_of_neg_of_pos hxneg (mul_pos hC (gap_pos hmono _))
      rcases le_or_gt m (idx hlim s) with hm' | hm'
      · have := hmono.monotone hm'
        have := idx_le hlim s hs
        linarith [hm.1]
      · have := hmono.monotone (show idx hlim s + 1 ≤ m by omega)
        linarith [hm.2]
    · push_neg at hy
      exact te_residualCDF_of_neg ν s _ hy
  · obtain ⟨k, hk1, hk2⟩ := exists_level_of_continuousAt p c hp hc x hxnn hx
    rw [piPC_eq_on p c hp hc k x hk1.le hk2]
    have hS1 : Tendsto (fun n => (t (n + 1 + k) - t (n + 1)) / gap t (n + 1)) atTop
        (𝓝 (Cfun p c * wfun p c k)) := (gap_sum hp hc hmono h12a k).comp (tendsto_add_atTop_nat 1)
    have hS2 : Tendsto (fun n => (t (n + 1 + (k + 1)) - t (n + 1)) / gap t (n + 1)) atTop
        (𝓝 (Cfun p c * wfun p c (k + 1))) := by
      have := (gap_sum hp hc hmono h12a (k + 1)).comp (tendsto_add_atTop_nat 1)
      push_cast at this
      exact this
    have hlt1 : Cfun p c * wfun p c k < Cfun p c * x := mul_lt_mul_of_pos_left hk1 hC
    have hlt2 : Cfun p c * x < Cfun p c * wfun p c (k + 1) := mul_lt_mul_of_pos_left hk2 hC
    have hev : ∀ᶠ n in atTop, t (n + 1 + k) < t (n + 1) + x * (Cfun p c * gap t (n + 1)) ∧
        t (n + 1) + x * (Cfun p c * gap t (n + 1)) < t (n + 1 + k + 1) := by
      filter_upwards [hS1.eventually (eventually_lt_nhds hlt1),
        hS2.eventually (eventually_gt_nhds hlt2)] with n h1 h2
      have hg := gap_pos hmono (n + 1)
      rw [div_lt_iff₀ hg] at h1
      rw [lt_div_iff₀ hg] at h2
      rw [show n + 1 + (k + 1) = n + 1 + k + 1 by ring] at h2
      constructor <;> nlinarith
    have hratio := tailRatio_pow hν h12b (k + 1)
    have hfinal : Tendsto (fun n => 1 - tailR ν t (n + (k + 1)) / tailR ν t n) atTop
        (𝓝 (1 - Real.exp (-p) ^ (k + 1))) := tendsto_const_nhds.sub hratio
    have hexp : Real.exp (-p * ((k : ℝ) + 1)) = Real.exp (-p) ^ (k + 1) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hexp]
    apply (hfinal.comp (idx_tendsto hlim hmono.monotone)).congr'
    filter_upwards [eventually_ge_atTop (t 0), (idx_tendsto hlim hmono.monotone).eventually hev]
      with s hs hs2
    have hy : 0 ≤ t (idx hlim s + 1) - s + x * (Cfun p c * gap t (idx hlim s + 1)) := by
      have := idx_lt hlim s
      have := mul_nonneg hxnn (mul_pos hC (gap_pos hmono (idx hlim s + 1))).le
      linarith
    simp only [Function.comp]
    rw [te_residualCDF_of_nonneg ν s _ hy (disc_tail_pos hν s)]
    unfold tailR
    rw [disc_Ioi_eq_of_mem hν (idx hlim s) s (idx_le hlim s hs) (idx_lt hlim s)]
    rw [show s + (t (idx hlim s + 1) - s + x * (Cfun p c * gap t (idx hlim s + 1))) =
      t (idx hlim s + 1) + x * (Cfun p c * gap t (idx hlim s + 1)) by ring]
    rw [disc_Ioi_eq_of_mem hν (idx hlim s + 1 + k) _ hs2.1.le hs2.2]
    rw [show idx hlim s + (k + 1) = idx hlim s + 1 + k by ring]

end BalkemaDeHaan.DiscreteDomain

open BalkemaDeHaan.DiscreteDomain


theorem solution (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℕ → ℝ)
    (hν : IsDiscreteWithJumps ν t) (h12a : GapRatio t p c) (h12b : TailRatio ν t p) :
    InDr ν (piPC p c) := by
  exact discrete_mem_Dr_core p c hp hc ν t hν h12a h12b
