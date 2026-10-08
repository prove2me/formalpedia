-- Prove2me | solution 1 for BalkemaDeHaan.DiscreteDomain.levels_12b_12a
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:54:27.187722+00:00
-- url     : https://prove2.me/submissions/ed7d61a0-fd15-4ca7-baa8-345586c327df

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

/-- Tail equivalence transfers the weak convergence of residual distribution functions. -/
theorem tailEquiv_mem_Dr_core (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h12 : TailEquiv μ₁ μ₂) (h2 : InDr μ₂ (piPC p c)) :
    InDr μ₁ (piPC p c) := by
  obtain ⟨hpos1, hpos2, hlim⟩ := h12
  obtain ⟨_, a, b, ha, hconv⟩ := h2
  refine ⟨hpos1, a, b, ha, ?_⟩
  intro x hx
  have h2x := hconv x hx
  have key : Tendsto (fun t => BalkemaDeHaan.LimitTypes.residualCDF μ₁ t (b t + x * a t) -
      BalkemaDeHaan.LimitTypes.residualCDF μ₂ t (b t + x * a t)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hη0 : 0 < min (ε / 8) (1 / 2) := lt_min (by linarith) (by norm_num)
    have hη1 : min (ε / 8) (1 / 2) ≤ 1 / 2 := min_le_right _ _
    have hηε : min (ε / 8) (1 / 2) ≤ ε / 8 := min_le_left _ _
    obtain ⟨T, hT⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hlim) _ hη0)
    rw [eventually_atTop]
    refine ⟨T, fun t ht => ?_⟩
    rw [Real.dist_eq, sub_zero]
    by_cases hy : 0 ≤ b t + x * a t
    · rw [te_residualCDF_of_nonneg μ₁ t _ hy (hpos1 t), te_residualCDF_of_nonneg μ₂ t _ hy (hpos2 t)]
      have hA : 0 < (μ₂ (Set.Ioi t)).toReal :=
        ENNReal.toReal_pos (hpos2 t).ne' (measure_ne_top _ _)
      have hB : 0 < (μ₂ (Set.Ioi (t + (b t + x * a t)))).toReal :=
        ENNReal.toReal_pos (hpos2 _).ne' (measure_ne_top _ _)
      have hBA : (μ₂ (Set.Ioi (t + (b t + x * a t)))).toReal ≤ (μ₂ (Set.Ioi t)).toReal :=
        te_tail_antitone μ₂ (by linarith)
      have hu := hT t ht
      have hv := hT (t + (b t + x * a t)) (by linarith)
      rw [Real.dist_eq] at hu hv
      set u := (μ₁ (Set.Ioi t)).toReal / (μ₂ (Set.Ioi t)).toReal with hu_def
      set v := (μ₁ (Set.Ioi (t + (b t + x * a t)))).toReal /
        (μ₂ (Set.Ioi (t + (b t + x * a t)))).toReal with hv_def
      set A := (μ₂ (Set.Ioi t)).toReal
      set B := (μ₂ (Set.Ioi (t + (b t + x * a t)))).toReal
      have hR1 : (μ₁ (Set.Ioi t)).toReal = u * A := by
        rw [hu_def]; field_simp
      have hR1' : (μ₁ (Set.Ioi (t + (b t + x * a t)))).toReal = v * B := by
        rw [hv_def]; field_simp
      rw [hR1, hR1']
      have hu' := abs_sub_lt_iff.1 hu
      have hv' := abs_sub_lt_iff.1 hv
      have hu0 : 0 < u := by linarith
      have heq : 1 - v * B / (u * A) - (1 - B / A) = (B / A) * ((u - v) / u) := by
        field_simp; ring
      rw [heq, abs_mul]
      have h1 : |B / A| ≤ 1 := by
        rw [abs_of_nonneg (div_nonneg hB.le hA.le)]; exact div_le_one_of_le₀ hBA hA.le
      have h2 : |(u - v) / u| ≤ 4 * min (ε / 8) (1 / 2) := by
        rw [abs_div, abs_of_pos hu0, div_le_iff₀ hu0]
        calc |u - v| ≤ 2 * min (ε / 8) (1 / 2) := by
              rw [abs_sub_le_iff]; constructor <;> linarith
          _ ≤ 4 * min (ε / 8) (1 / 2) * u := by nlinarith
      calc |B / A| * |(u - v) / u| ≤ 1 * (4 * min (ε / 8) (1 / 2)) :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ < ε := by linarith
    · push_neg at hy
      rw [te_residualCDF_of_neg μ₁ t _ hy, te_residualCDF_of_neg μ₂ t _ hy]
      simpa using hε
  have := key.add h2x
  simp only [sub_add_cancel, zero_add] at this
  exact this


/-! ### the converse: from `D_r(Π_{p,c})` to the gap condition -/

lemma disc_Ioi_ge {ν : Measure ℝ} {t : ℕ → ℝ} [IsFiniteMeasure ν] (hν : IsDiscreteWithJumps ν t)
    (m : ℕ) (s : ℝ) (hs : s < t (m + 1)) :
    (ν (Set.Ioi (t m))).toReal ≤ (ν (Set.Ioi s)).toReal := by
  rcases lt_or_ge s (t m) with h | h
  · exact te_tail_antitone ν h.le
  · rw [disc_Ioi_eq_of_mem hν m s h hs]

lemma disc_le_of_lt {ν : Measure ℝ} {t : ℕ → ℝ} [IsFiniteMeasure ν] (hν : IsDiscreteWithJumps ν t)
    (m : ℕ) (s : ℝ) (h : (ν (Set.Ioi s)).toReal < (ν (Set.Ioi (t m))).toReal) : t (m + 1) ≤ s := by
  by_contra h'
  push_neg at h'
  exact absurd h (not_lt.2 (disc_Ioi_ge hν m s h'))

lemma disc_lt_of_lt {ν : Measure ℝ} {t : ℕ → ℝ} [IsFiniteMeasure ν]
    (m : ℕ) (s : ℝ) (h : (ν (Set.Ioi (t m))).toReal < (ν (Set.Ioi s)).toReal) : s < t m := by
  by_contra h'
  push_neg at h'
  exact absurd h (not_lt.2 (te_tail_antitone ν h'))

/-- Along `s = t_n`, a continuity point `x ∈ (w_k, w_{k+1})` is sent into `[t_{n+k+1}, t_{n+k+2})`. -/
lemma levelL {ν : Measure ℝ} {t : ℕ → ℝ} [IsProbabilityMeasure ν] {p c : ℝ} (hp : 0 < p)
    (hc : 0 ≤ c) (hν : IsDiscreteWithJumps ν t) (hR : TailRatio ν t p) (a b : ℝ → ℝ)
    (hconv : BalkemaDeHaan.LimitTypes.WeakConv
      (fun s x => BalkemaDeHaan.LimitTypes.residualCDF ν s (b s + x * a s)) (piPC p c))
    (k : ℕ) (x : ℝ) (h1 : wfun p c k < x) (h2 : x < wfun p c (k + 1)) :
    ∀ᶠ n in atTop, t (n + k + 1) ≤ t n + (b (t n) + x * a (t n)) ∧
      t n + (b (t n) + x * a (t n)) < t (n + k + 2) := by
  have hcx := hconv x (piPC_continuousAt_of_mem p c hp hc k x h1 h2)
  rw [piPC_eq_on p c hp hc k x h1.le h2] at hcx
  have hcn : Tendsto (fun n => BalkemaDeHaan.LimitTypes.residualCDF ν (t n) (b (t n) + x * a (t n)))
    atTop (𝓝 (1 - Real.exp (-p * ((k : ℝ) + 1)))) := hcx.comp hν.2.1
  have hexp : Real.exp (-p * ((k : ℝ) + 1)) = Real.exp (-p) ^ (k + 1) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [hexp] at hcn
  have he0 : 0 < Real.exp (-p) := Real.exp_pos _
  have he1 : Real.exp (-p) < 1 := by
    have := Real.exp_lt_exp.2 (show -p < 0 by linarith); rwa [Real.exp_zero] at this
  have hEpos : 0 < Real.exp (-p) ^ (k + 1) := pow_pos he0 _
  have hElt : Real.exp (-p) ^ (k + 1) < 1 := pow_lt_one₀ he0.le he1 (by omega)
  have hy : ∀ᶠ n in atTop, 0 ≤ b (t n) + x * a (t n) := by
    filter_upwards [hcn.eventually (eventually_gt_nhds
      (by linarith : (0:ℝ) < 1 - Real.exp (-p) ^ (k + 1)))] with n hn
    by_contra h
    push_neg at h
    rw [te_residualCDF_of_neg ν _ _ h] at hn
    exact lt_irrefl _ hn
  have hrat : Tendsto (fun n => (ν (Set.Ioi (t n + (b (t n) + x * a (t n))))).toReal / tailR ν t n)
      atTop (𝓝 (Real.exp (-p) ^ (k + 1))) := by
    have := (tendsto_const_nhds (x := (1:ℝ))).sub hcn
    rw [sub_sub_cancel] at this
    apply this.congr'
    filter_upwards [hy] with n hn
    rw [te_residualCDF_of_nonneg ν _ _ hn (disc_tail_pos hν _)]
    unfold tailR; ring
  have hk := tailRatio_pow hν hR k
  have hk2 := tailRatio_pow hν hR (k + 2)
  have hlt1 : Real.exp (-p) ^ (k + 1) < Real.exp (-p) ^ k := by
    rw [pow_succ]; nlinarith [pow_pos he0 k]
  have hlt2 : Real.exp (-p) ^ (k + 2) < Real.exp (-p) ^ (k + 1) := by
    rw [pow_succ _ (k + 1)]; nlinarith [pow_pos he0 (k + 1)]
  filter_upwards [hrat.eventually (eventually_lt_nhds (by linarith : Real.exp (-p) ^ (k + 1) <
      (Real.exp (-p) ^ (k + 1) + Real.exp (-p) ^ k) / 2)),
    hk.eventually (eventually_gt_nhds (by linarith :
      (Real.exp (-p) ^ (k + 1) + Real.exp (-p) ^ k) / 2 < Real.exp (-p) ^ k)),
    hrat.eventually (eventually_gt_nhds (by linarith :
      (Real.exp (-p) ^ (k + 2) + Real.exp (-p) ^ (k + 1)) / 2 < Real.exp (-p) ^ (k + 1))),
    hk2.eventually (eventually_lt_nhds (by linarith : Real.exp (-p) ^ (k + 2) <
      (Real.exp (-p) ^ (k + 2) + Real.exp (-p) ^ (k + 1)) / 2))] with n hn1 hn2 hn3 hn4
  have hRn := disc_tailR_pos hν n
  constructor
  · apply disc_le_of_lt hν
    have : (ν (Set.Ioi (t n + (b (t n) + x * a (t n))))).toReal / tailR ν t n <
        tailR ν t (n + k) / tailR ν t n := by linarith
    rw [div_lt_div_iff_of_pos_right hRn] at this
    exact this
  · apply disc_lt_of_lt (ν := ν)
    have : tailR ν t (n + (k + 2)) / tailR ν t n <
        (ν (Set.Ioi (t n + (b (t n) + x * a (t n))))).toReal / tailR ν t n := by linarith
    rw [div_lt_div_iff_of_pos_right hRn] at this
    rw [show n + k + 2 = n + (k + 2) by ring]
    exact this

/-- Along `s = t_n`, a negative `x` is sent below `t_{n+1}`. -/
lemma levelNeg {ν : Measure ℝ} {t : ℕ → ℝ} [IsProbabilityMeasure ν] {p c : ℝ} (hp : 0 < p)
    (hν : IsDiscreteWithJumps ν t) (hR : TailRatio ν t p) (a b : ℝ → ℝ)
    (hconv : BalkemaDeHaan.LimitTypes.WeakConv
      (fun s x => BalkemaDeHaan.LimitTypes.residualCDF ν s (b s + x * a s)) (piPC p c))
    (x : ℝ) (hx : x < 0) :
    ∀ᶠ n in atTop, t n + (b (t n) + x * a (t n)) < t (n + 1) := by
  have hcx := hconv x (piPC_continuousAt_of_neg p c x hx)
  rw [piPC_of_neg p c x hx] at hcx
  have hcn : Tendsto (fun n => BalkemaDeHaan.LimitTypes.residualCDF ν (t n) (b (t n) + x * a (t n)))
    atTop (𝓝 0) := hcx.comp hν.2.1
  have h1 := tailRatio_pow hν hR 1
  simp only [pow_one] at h1
  have he1 : Real.exp (-p) < 1 := by
    have := Real.exp_lt_exp.2 (show -p < 0 by linarith); rwa [Real.exp_zero] at this
  filter_upwards [hcn.eventually (eventually_lt_nhds
      (by linarith : (0:ℝ) < (1 - Real.exp (-p)) / 2)),
    h1.eventually (eventually_lt_nhds
      (by linarith : Real.exp (-p) < (1 + Real.exp (-p)) / 2))] with n hn1 hn2
  by_contra h
  push_neg at h
  have hy : 0 ≤ b (t n) + x * a (t n) := by linarith [hν.1 (Nat.lt_succ_self n)]
  rw [te_residualCDF_of_nonneg ν _ _ hy (disc_tail_pos hν _)] at hn1
  have hRn := disc_tailR_pos hν n
  have : (ν (Set.Ioi (t n + (b (t n) + x * a (t n))))).toReal / tailR ν t n ≤
      tailR ν t (n + 1) / tailR ν t n :=
    div_le_div_of_nonneg_right (te_tail_antitone ν h) hRn.le
  unfold tailR at this hn2
  linarith

lemma wfun_two_sub_one (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c) :
    wfun p c 2 - wfun p c 1 = Real.exp (c * p) * wfun p c 1 := by
  unfold wfun
  split_ifs with h
  · subst h; simp; ring
  · have hc' : 0 < c := lt_of_le_of_ne hc (Ne.symm h)
    field_simp
    rw [show c * p * 2 = c * p + c * p by ring, Real.exp_add]
    ring

theorem levels_12b_12a_core (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : InDr μ (piPC p c))
    (b : ℕ → ℝ)
    (hb : Tendsto (fun n : ℕ => (μ (Set.Ioi (b (n + 1)))).toReal / (μ (Set.Ioi (b n))).toReal)
      atTop (𝓝 (Real.exp (-p))))
    (ν₀ : Measure ℝ) [IsProbabilityMeasure ν₀] (t : ℕ → ℝ)
    (hν₀ : IsDiscreteWithJumps ν₀ t) (hlev : ∀ n, ν₀ (Set.Ioi (t n)) = μ (Set.Ioi (b n)))
    (heq : TailEquiv μ ν₀) :
    TailRatio ν₀ t p ∧ GapRatio t p c := by
  have hTR : TailRatio ν₀ t p := by
    unfold TailRatio; simp_rw [hlev]; exact hb
  refine ⟨hTR, ?_⟩
  have hsym : TailEquiv ν₀ μ := by
    obtain ⟨h1, h2, h3⟩ := heq
    refine ⟨h2, h1, ?_⟩
    have := h3.inv₀ one_ne_zero
    rw [inv_one] at this
    apply this.congr
    intro x; rw [inv_div]
  obtain ⟨_, a, b', ha, hconv⟩ := tailEquiv_mem_Dr_core p c hp hc ν₀ μ hsym hμ
  have hmono := hν₀.1
  have hw01 : 0 < wfun p c 1 := by
    rw [← wfun_zero p c]; exact wfun_strictMono p c hp hc (by norm_num)
  have hw12 : wfun p c 1 < wfun p c 2 := wfun_strictMono p c hp hc (by norm_num)
  have hw23 : wfun p c 2 < wfun p c 3 := wfun_strictMono p c hp hc (by norm_num)
  have hq : wfun p c 2 - wfun p c 1 = Real.exp (c * p) * wfun p c 1 := wfun_two_sub_one p c hp hc
  have hqpos : 0 < Real.exp (c * p) := Real.exp_pos _
  unfold GapRatio
  rw [mul_comm p c, ← tendsto_add_atTop_iff_nat 1]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδpos : 0 < min (min (wfun p c 1 / 4) ((wfun p c 2 - wfun p c 1) / 4))
      (min ((wfun p c 3 - wfun p c 2) / 2) (ε * wfun p c 1 / (8 * (1 + Real.exp (c * p))))) := by
    refine lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by positivity))
  obtain ⟨δ, hδ, hδpos, hδ1, hδ2, hδ3, hδ4⟩ : ∃ δ : ℝ, δ = min (min (wfun p c 1 / 4)
      ((wfun p c 2 - wfun p c 1) / 4))
      (min ((wfun p c 3 - wfun p c 2) / 2) (ε * wfun p c 1 / (8 * (1 + Real.exp (c * p))))) ∧
      0 < δ ∧ δ ≤ wfun p c 1 / 4 ∧ δ ≤ (wfun p c 2 - wfun p c 1) / 4 ∧
      δ ≤ (wfun p c 3 - wfun p c 2) / 2 ∧ δ ≤ ε * wfun p c 1 / (8 * (1 + Real.exp (c * p))) :=
    ⟨_, rfl, hδpos, le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _),
      le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _) (min_le_right _ _)⟩
  clear hδ
  have hδ4' : δ * (8 * (1 + Real.exp (c * p))) ≤ ε * wfun p c 1 := by
    rwa [le_div_iff₀ (by positivity)] at hδ4
  have e1 := levelNeg hp hν₀ hTR a b' hconv (-δ) (by linarith)
  have e2 := levelL hp hc hν₀ hTR a b' hconv 0 δ (by rw [Nat.cast_zero, wfun_zero]; exact hδpos)
    (by norm_num; linarith)
  have e3 := levelL hp hc hν₀ hTR a b' hconv 0 (wfun p c 1 - δ)
    (by rw [Nat.cast_zero, wfun_zero]; linarith) (by norm_num; linarith)
  have e4 := levelL hp hc hν₀ hTR a b' hconv 1 (wfun p c 1 + δ)
    (by rw [Nat.cast_one]; linarith) (by norm_num; linarith)
  have e5 := levelL hp hc hν₀ hTR a b' hconv 1 (wfun p c 2 - δ)
    (by rw [Nat.cast_one]; linarith) (by norm_num; linarith)
  have e6 := levelL hp hc hν₀ hTR a b' hconv 2 (wfun p c 2 + δ)
    (by rw [Nat.cast_ofNat]; linarith) (by norm_num; linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and (e5.and e6)))))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hN n hn
  simp only [Nat.add_zero, show n + 1 + 1 = n + 2 from rfl, show n + 1 + 2 = n + 3 from rfl,
    show n + 2 + 1 = n + 3 from rfl, show n + 2 + 2 = n + 4 from rfl] at h1 h2 h3 h4 h5 h6 ⊢
  have hA := ha (t n)
  have hG1 : 0 < t (n + 2) - t (n + 1) := by linarith [hmono (show n + 1 < n + 2 by omega)]
  have hG1lo : (wfun p c 1 - 2 * δ) * a (t n) < t (n + 2) - t (n + 1) := by nlinarith [h3.2, h2.1]
  have hG1hi : t (n + 2) - t (n + 1) ≤ (wfun p c 1 + 2 * δ) * a (t n) := by nlinarith [h4.1, h1]
  have hG2lo : (wfun p c 2 - wfun p c 1 - 2 * δ) * a (t n) < t (n + 3) - t (n + 2) := by
    nlinarith [h5.2, h4.1]
  have hG2hi : t (n + 3) - t (n + 2) ≤ (wfun p c 2 - wfun p c 1 + 2 * δ) * a (t n) := by
    nlinarith [h6.1, h3.1]
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hG1]
    have k1 : (Real.exp (c * p) * wfun p c 1 + 2 * δ) * a (t n) <
        (ε + Real.exp (c * p)) * ((wfun p c 1 - 2 * δ) * a (t n)) := by
      rw [← mul_assoc]
      apply mul_lt_mul_of_pos_right _ hA
      nlinarith
    have k2 := mul_lt_mul_of_pos_left hG1lo (by positivity : 0 < ε + Real.exp (c * p))
    rw [hq] at hG2hi
    linarith
  · rw [sub_lt_comm, lt_div_iff₀ hG1]
    rcases le_or_gt (Real.exp (c * p) - ε) 0 with hqe | hqe
    · have : (Real.exp (c * p) - ε) * (t (n + 2) - t (n + 1)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hqe hG1.le
      have : 0 < t (n + 3) - t (n + 2) := by linarith [hmono (show n + 2 < n + 3 by omega)]
      linarith
    · have k1 : (Real.exp (c * p) - ε) * ((wfun p c 1 + 2 * δ) * a (t n)) <
          (Real.exp (c * p) * wfun p c 1 - 2 * δ) * a (t n) := by
        rw [← mul_assoc]
        apply mul_lt_mul_of_pos_right _ hA
        nlinarith
      have k2 := mul_le_mul_of_nonneg_left hG1hi hqe.le
      rw [hq] at hG2lo
      linarith

end BalkemaDeHaan.DiscreteDomain

open BalkemaDeHaan.DiscreteDomain


theorem solution (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : InDr μ (piPC p c))
    (b : ℕ → ℝ)
    (hb : Tendsto (fun n : ℕ => (μ (Set.Ioi (b (n + 1)))).toReal / (μ (Set.Ioi (b n))).toReal)
      atTop (𝓝 (Real.exp (-p))))
    (ν₀ : Measure ℝ) [IsProbabilityMeasure ν₀] (t : ℕ → ℝ)
    (hν₀ : IsDiscreteWithJumps ν₀ t) (hlev : ∀ n, ν₀ (Set.Ioi (t n)) = μ (Set.Ioi (b n)))
    (heq : TailEquiv μ ν₀) :
    TailRatio ν₀ t p ∧ GapRatio t p c := by
  exact levels_12b_12a_core p c hp hc μ hμ b hb ν₀ t hν₀ hlev heq
