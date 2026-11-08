-- Prove2me | solution 1 for CommissionsSubscriptions.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T02:11:36.014108+00:00
-- url     : https://prove2.me/submissions/123d8078-c468-4120-a84e-facc402c9c9e

import Mathlib
import Definitions.Def_CommissionsSubscriptions_MarketHyp
import Definitions.Def_CommissionsSubscriptions_Assumption2
import Definitions.Def_CommissionsSubscriptions_IsOptimalPair
import Definitions.Def_CommissionsSubscriptions_IsOptimal7
import Definitions.Def_CommissionsSubscriptions_System8

set_option autoImplicit false

open Filter Topology

namespace CS5f

open CommissionsSubscriptions

/-! ## Part A: facts about a value CDF and its inverse `Finv`. -/

section PartA

variable {F : ℝ → ℝ}

lemma F_nonneg (hF : IsValueCDF F) (v : ℝ) : 0 ≤ F v := by
  rcases le_total v 0 with h | h
  · rw [hF.2.1 v h]
  · have h1 := hF.1 h
    rw [hF.2.1 0 le_rfl] at h1
    exact h1

lemma F_le_one (hF : IsValueCDF F) (v : ℝ) : F v ≤ 1 :=
  hF.1.ge_of_tendsto hF.2.2.2.1 v

lemma Finv_le_of {u r : ℝ} (hr : 0 ≤ r) (hu : u ≤ F r) : Finv F u ≤ (r : EReal) :=
  iInf₂_le r ⟨hr, hu⟩

lemma le_Finv {u a : ℝ} (h : ∀ r : ℝ, 0 ≤ r → u ≤ F r → a ≤ r) : (a : EReal) ≤ Finv F u :=
  le_iInf₂ fun r hr => EReal.coe_le_coe_iff.2 (h r hr.1 hr.2)

lemma Finv_nonneg (u : ℝ) : (0 : EReal) ≤ Finv F u :=
  le_iInf₂ fun r hr => EReal.coe_nonneg.2 hr.1

lemma Finv_zero (hF : IsValueCDF F) : Finv F 0 = 0 :=
  le_antisymm (by simpa using Finv_le_of (F := F) le_rfl (F_nonneg hF 0)) (Finv_nonneg 0)

lemma Finv_mono {u u' : ℝ} (h : u ≤ u') : Finv F u ≤ Finv F u' :=
  le_iInf₂ fun r hr => iInf₂_le r ⟨hr.1, h.trans hr.2⟩

/-- A point where `F < 1` lies strictly below the upper end of the support. -/
lemma lt_vbar (hF : IsValueCDF F) {r : ℝ} (h : F r < 1) : (r : EReal) < Finv F 1 := by
  have hev : ∀ᶠ x in 𝓝 r, F x < 1 := (hF.2.2.1.tendsto r).eventually (gt_mem_nhds h)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have h2 : F (r + ε / 2) < 1 := hball (by
    rw [Real.dist_eq]; rw [show r + ε / 2 - r = ε / 2 by ring, abs_of_pos (by linarith)]; linarith)
  have hle : ((r + ε / 2 : ℝ) : EReal) ≤ Finv F 1 := by
    apply le_Finv
    intro r' _ hr'
    by_contra hlt
    push Not at hlt
    have := hF.1 hlt.le
    linarith
  exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by linarith)) hle

lemma F_pos (hF : IsValueCDF F) {v : ℝ} (hv : 0 < v) : 0 < F v := by
  by_contra hcon
  push Not at hcon
  have h1 : F v < 1 := lt_of_le_of_lt hcon one_pos
  have hlt : F (v / 2) < F v :=
    hF.2.2.2.2.1 ⟨by linarith, lt_vbar hF (lt_of_le_of_lt (hF.1 (by linarith)) h1)⟩
      ⟨hv, lt_vbar hF h1⟩ (by linarith)
  linarith [F_nonneg hF (v / 2)]

lemma F_eq_zero_iff (hF : IsValueCDF F) (v : ℝ) : F v = 0 ↔ v ≤ 0 := by
  constructor
  · intro h
    by_contra hv
    push Not at hv
    exact (F_pos hF hv).ne' h
  · exact hF.2.1 v

/-- `Finv` inverts `F` at every point where `0 < F v < 1`. -/
lemma Finv_F (hF : IsValueCDF F) {v : ℝ} (h0 : 0 < F v) (h1 : F v < 1) :
    Finv F (F v) = (v : EReal) := by
  have hv : 0 < v := by
    by_contra hv; push Not at hv; rw [hF.2.1 v hv] at h0; exact lt_irrefl _ h0
  apply le_antisymm (Finv_le_of hv.le le_rfl)
  apply le_Finv
  intro r hr hFr
  by_contra hlt
  push Not at hlt
  rcases hr.eq_or_lt with h | h
  · subst h; rw [hF.2.1 0 le_rfl] at hFr; linarith
  · have := hF.2.2.2.2.1 ⟨h, lt_vbar hF (lt_of_le_of_lt (hF.1 hlt.le) h1)⟩ ⟨hv, lt_vbar hF h1⟩ hlt
    linarith

/-- Every level `u ∈ (0,1)` is attained, and `Finv` returns the attaining point. -/
lemma exists_F_eq (hF : IsValueCDF F) {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    ∃ v : ℝ, 0 < v ∧ F v = u ∧ Finv F u = (v : EReal) := by
  have hev : ∀ᶠ x in atTop, u < F x := hF.2.2.2.1.eventually (lt_mem_nhds h1)
  obtain ⟨N, hN⟩ := hev.exists_forall_of_atTop
  have hN0 : u < F (max N 0) := hN _ (le_max_left _ _)
  have hsub := intermediate_value_Icc (le_max_right N 0) hF.2.2.1.continuousOn
  have hmem : u ∈ Set.Icc (F 0) (F (max N 0)) := ⟨by rw [hF.2.1 0 le_rfl]; exact h0.le, hN0.le⟩
  obtain ⟨v, -, hv⟩ := hsub hmem
  have hvpos : 0 < v := by
    by_contra hc; push Not at hc; rw [hF.2.1 v hc] at hv; linarith
  refine ⟨v, hvpos, hv, ?_⟩
  rw [← hv]
  exact Finv_F hF (hv ▸ h0) (hv ▸ h1)

lemma Finv_lt_top (hF : IsValueCDF F) {u : ℝ} (h1 : u < 1) : Finv F u ≠ ⊤ := by
  rcases le_or_gt u 0 with h | h
  · have := Finv_mono (F := F) h
    rw [Finv_zero hF] at this
    exact ne_top_of_le_ne_top EReal.zero_ne_top this
  · obtain ⟨v, -, -, hv⟩ := exists_F_eq hF h h1
    rw [hv]; exact EReal.coe_ne_top v

/-- `Finv F 1 = ⊤` exactly when `F < 1` everywhere. -/
lemma vbar_top_iff (hF : IsValueCDF F) : Finv F 1 = ⊤ ↔ ∀ r, F r < 1 := by
  constructor
  · intro h r
    by_contra hc
    push Not at hc
    have hle := Finv_le_of (F := F) (le_max_right r 0) (hc.trans (hF.1 (le_max_left r 0)))
    rw [h] at hle
    exact EReal.coe_ne_top _ (top_le_iff.1 hle)
  · intro h
    apply eq_top_iff.2
    apply le_of_forall_lt
    intro c hc
    induction c using EReal.rec with
    | bot => exact lt_of_lt_of_le (EReal.bot_lt_coe 0) (Finv_nonneg 1)
    | top => exact absurd hc (lt_irrefl _)
    | coe a =>
      apply lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (lt_add_one a))
      apply le_Finv
      intro r _ hr
      linarith [h r]

/-- When the support is bounded, `F` reaches `1` at `vbar`. -/
lemma F_vbar (hF : IsValueCDF F) (hfin : Finv F 1 ≠ ⊤) : F (Finv F 1).toReal = 1 := by
  have hbot : Finv F 1 ≠ ⊥ := ne_bot_of_le_ne_bot EReal.zero_ne_bot (Finv_nonneg 1)
  set w := (Finv F 1).toReal with hw
  have hcoe : ((w : ℝ) : EReal) = Finv F 1 := EReal.coe_toReal hfin hbot
  apply le_antisymm (F_le_one hF w)
  -- for every ε > 0, F (w + ε) ≥ 1; conclude by continuity
  have hge : ∀ ε > 0, 1 ≤ F (w + ε) := by
    intro ε hε
    have hlt : Finv F 1 < ((w + ε : ℝ) : EReal) := by
      rw [← hcoe]; exact EReal.coe_lt_coe_iff.2 (by linarith)
    obtain ⟨r, hr⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hr', hr''⟩ := iInf_lt_iff.1 hr
    have : r < w + ε := EReal.coe_lt_coe_iff.1 hr''
    exact hr'.2.trans (hF.1 this.le)
  have hcont : Tendsto (fun ε : ℝ => F (w + ε)) (𝓝[>] 0) (𝓝 (F w)) := by
    have : Tendsto (fun ε : ℝ => w + ε) (𝓝[>] 0) (𝓝 w) := by
      have h : Tendsto (fun ε : ℝ => w + ε) (𝓝 0) (𝓝 (w + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      rw [add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    exact (hF.2.2.1.tendsto w).comp this
  exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall fun ε hε => hge ε hε)

/-- Unbounded support: `Finv F u` exceeds every bound for `u` close to `1`. -/
lemma Finv_unbounded (hF : IsValueCDF F) (htop : Finv F 1 = ⊤) (M : ℝ) :
    ∃ u : ℝ, 0 < u ∧ u < 1 ∧ (M : EReal) < Finv F u := by
  have hlt := (vbar_top_iff hF).1 htop
  set M' := max M 0 + 1
  have hM1 := hlt M'
  set u := (F M' + 1) / 2 with hu
  have hpos : 0 < F M' := F_pos hF (by positivity)
  refine ⟨u, by rw [hu]; linarith, by rw [hu]; linarith, ?_⟩
  apply lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (show M < M' by
    have := le_max_left M 0; linarith))
  apply le_Finv
  intro r _ hr
  by_contra hc
  push Not at hc
  have := hF.1 hc.le
  linarith [hu]

lemma Finv_F' (hF : IsValueCDF F) {v : ℝ} (hv : 0 ≤ v) (h1 : F v < 1) :
    Finv F (F v) = (v : EReal) := by
  rcases (F_nonneg hF v).lt_or_eq with h | h
  · exact Finv_F hF h h1
  · have hv0 : v = 0 := le_antisymm ((F_eq_zero_iff hF v).1 h.symm) hv
    rw [← h, Finv_zero hF, hv0, EReal.coe_zero]

end PartA


/-! ## Part B: an equilibrium is feasible for (7) and its revenue is at most `obj7`. -/

section PartB

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] {M : Market S B}

lemma coe_sum' {ι : Type} (s : Finset ι) (g : ι → ℝ) :
    ((∑ i ∈ s, g i : ℝ) : EReal) = ∑ i ∈ s, (g i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

lemma minCost_le (f : Fees S B) (p : S → ℝ) {i : S} {j : B} (h : (i, j) ∈ M.E) :
    minCost M f p j ≤ (1 + f.gb j) * p i + M.c i :=
  ciInf_le (Set.finite_range _).bddBelow (⟨i, h⟩ : {i : S // (i, j) ∈ M.E})

lemma minCost_nonneg (hM : MarketHyp M) {f : Fees S B} {p : S → ℝ} (hf : InGammaU f)
    (hp : ∀ i, 0 ≤ p i) (j : B) : 0 ≤ minCost M f p j := by
  obtain ⟨i, hi⟩ := hM.2.2.2.2.1 j
  haveI : Nonempty {i : S // (i, j) ∈ M.E} := ⟨⟨i, hi⟩⟩
  exact le_ciInf fun k => add_nonneg (mul_nonneg (by linarith [hf.2.1 j]) (hp k)) (hM.2.2.1 k)

lemma hS_le {i : S} (hF : IsValueCDF (M.Fs i)) (hs : 0 < M.s i) {w q : ℝ}
    (hq : q = M.s i * M.Fs i w) : ∃ a : ℝ, hS M i q = (a : EReal) ∧ a ≤ q * w := by
  have hq' : q / M.s i = M.Fs i w := by rw [hq, mul_div_cancel_left₀ _ hs.ne']
  unfold hS; rw [hq']
  rcases le_or_gt w 0 with hw | hw
  · have h0 : M.Fs i w = 0 := hF.2.1 w hw
    have hq0 : q = 0 := by rw [hq, h0, mul_zero]
    refine ⟨0, ?_, by rw [hq0, zero_mul]⟩
    rw [h0, Finv_zero hF, hq0]; simp
  · have hle : Finv (M.Fs i) (M.Fs i w) ≤ (w : EReal) := Finv_le_of hw.le le_rfl
    have hnn := Finv_nonneg (F := M.Fs i) (M.Fs i w)
    have htop : Finv (M.Fs i) (M.Fs i w) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top w) hle
    have hbot : Finv (M.Fs i) (M.Fs i w) ≠ ⊥ := ne_bot_of_le_ne_bot EReal.zero_ne_bot hnn
    have hcoe : (((Finv (M.Fs i) (M.Fs i w)).toReal : ℝ) : EReal) = Finv (M.Fs i) (M.Fs i w) :=
      EReal.coe_toReal htop hbot
    refine ⟨(Finv (M.Fs i) (M.Fs i w)).toReal * q, ?_, ?_⟩
    · rw [EReal.coe_mul, hcoe]
    · have hrw : (Finv (M.Fs i) (M.Fs i w)).toReal ≤ w := by
        rw [← EReal.coe_le_coe_iff, hcoe]; exact hle
      have hq0 : 0 ≤ q := by rw [hq]; exact mul_nonneg hs.le (F_nonneg hF w)
      nlinarith

lemma gB_eq {j : B} (hF : IsValueCDF (M.Fb j)) (hb : 0 < M.b j) {v q : ℝ} (hv : 0 ≤ v)
    (hq : q = M.b j * (1 - M.Fb j v)) : gB M j q = q * v := by
  have hq' : 1 - q / M.b j = M.Fb j v := by rw [hq, mul_div_cancel_left₀ _ hb.ne']; ring
  unfold gB; rw [hq']
  rcases (F_le_one hF v).lt_or_eq with h1 | h1
  · rw [Finv_F' hF hv h1, EReal.toReal_coe]
  · have : q = 0 := by rw [hq, h1]; ring
    rw [this, zero_mul, zero_mul]

lemma rev_identity {f : Fees S B} {p : S → ℝ} {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ}
    (heq : IsEquilibrium M f p x qs qb) :
    revenue M f p x = ∑ j, qb j * (minCost M f p j + f.mb j) -
      ∑ i, qs i * (M.c i + ((1 - f.gs i) * p i - f.ms i)) := by
  have hterm : ∀ e ∈ M.E, (f.gs e.1 + f.gb e.2) * p e.1 * x e.1 e.2 +
      (f.ms e.1 + f.mb e.2) * x e.1 e.2 = (minCost M f p e.2 + f.mb e.2) * x e.1 e.2 -
      (M.c e.1 + ((1 - f.gs e.1) * p e.1 - f.ms e.1)) * x e.1 e.2 := by
    intro e he
    by_cases hx : x e.1 e.2 = 0
    · rw [hx]; ring
    · have hm : (1 + f.gb e.2) * p e.1 + M.c e.1 = minCost M f p e.2 := by
        by_contra hne; exact hx (heq.2.2.2.2.2.2 e he hne)
      rw [← hm]; ring
  unfold revenue
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  have h1 : ∑ e ∈ M.E, (minCost M f p e.2 + f.mb e.2) * x e.1 e.2 =
      ∑ j, qb j * (minCost M f p j + f.mb j) := by
    rw [Finset.sum_finset_product_right M.E Finset.univ
      (fun j => Finset.univ.filter (fun i => (i, j) ∈ M.E)) (by intro e; simp)]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    rw [← Finset.mul_sum, ← heq.2.2.2.2.1 j, mul_comm]
  have h2 : ∑ e ∈ M.E, (M.c e.1 + ((1 - f.gs e.1) * p e.1 - f.ms e.1)) * x e.1 e.2 =
      ∑ i, qs i * (M.c i + ((1 - f.gs i) * p i - f.ms i)) := by
    rw [Finset.sum_finset_product M.E Finset.univ
      (fun i => Finset.univ.filter (fun j => (i, j) ∈ M.E)) (by intro e; simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [← Finset.mul_sum, ← heq.2.2.2.1 i, mul_comm]
  rw [h1, h2]

lemma eq_feasible7 (hM : MarketHyp M) {f : Fees S B} {p : S → ℝ} {x : S → B → ℝ}
    {qs : S → ℝ} {qb : B → ℝ} (heq : IsEquilibrium M f p x qs qb) : Feasible7 M x qs qb := by
  refine ⟨fun j => by rw [heq.2.2.2.2.1 j]; ring, fun i => by rw [heq.2.2.2.1 i]; ring,
    fun j => ?_, fun i => ?_, heq.2.2.2.2.2.1⟩
  · rw [heq.2.2.1 j]
    have := mul_nonneg (hM.2.1 j).le (F_nonneg (hM.2.2.2.2.2.2 j) (minCost M f p j + f.mb j))
    nlinarith
  · rw [heq.2.1 i]
    exact mul_le_of_le_one_right (hM.1 i).le (F_le_one (hM.2.2.2.2.2.1 i) _)

lemma eq_rev_le_obj7 (hM : MarketHyp M) {f : Fees S B} {p : S → ℝ} {x : S → B → ℝ}
    {qs : S → ℝ} {qb : B → ℝ} (hf : InGammaU f) (heq : IsEquilibrium M f p x qs qb) :
    ((revenue M f p x : ℝ) : EReal) ≤ obj7 M qs qb := by
  have hS' : ∀ i, ∃ a : ℝ, hS M i (qs i) = (a : EReal) ∧
      a ≤ qs i * ((1 - f.gs i) * p i - f.ms i) :=
    fun i => hS_le (hM.2.2.2.2.2.1 i) (hM.1 i) (heq.2.1 i)
  choose a ha ha' using hS'
  have hg : ∀ j, gB M j (qb j) = qb j * (minCost M f p j + f.mb j) := fun j =>
    gB_eq (hM.2.2.2.2.2.2 j) (hM.2.1 j)
      (add_nonneg (minCost_nonneg hM hf heq.1 j) (hf.2.2.2 j)) (heq.2.2.1 j)
  have hobj : obj7 M qs qb =
      ((∑ j, gB M j (qb j) - ∑ i, a i - ∑ i, M.c i * qs i : ℝ) : EReal) := by
    unfold obj7
    rw [Finset.sum_congr rfl (fun i _ => ha i), ← coe_sum', EReal.coe_sub, EReal.coe_sub]
  rw [hobj, EReal.coe_le_coe_iff, rev_identity heq, Finset.sum_congr rfl (fun j _ => hg j)]
  have h1 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ha' i)
  have h2 : ∑ i, qs i * (M.c i + ((1 - f.gs i) * p i - f.ms i)) =
      ∑ i, M.c i * qs i + ∑ i, qs i * ((1 - f.gs i) * p i - f.ms i) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  linarith

lemma Vopt_le_obj7 (hM : MarketHyp M) {xbar : S → B → ℝ} {qsbar : S → ℝ} {qbbar : B → ℝ}
    (hopt : IsOptimal7 M xbar qsbar qbbar) : Vopt M ≤ obj7 M qsbar qbbar := by
  unfold Vopt
  refine iSup_le fun f => iSup_le fun p => iSup_le fun x => iSup_le fun qs =>
    iSup_le fun qb => iSup_le fun h => ?_
  exact (eq_rev_le_obj7 hM h.1 h.2).trans (hopt.2 x qs qb (eq_feasible7 hM h.2))

end PartB


/-! ## Part C: a solution of (8) gives an equilibrium whose revenue is `obj7`. -/

section PartC

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] {M : Market S B}

lemma coe_eq_mul_coe {a : EReal} {r t : ℝ} (ht : 0 < t) (h : (r : EReal) = a * (t : EReal)) :
    a = ((r / t : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot => rw [EReal.bot_mul_coe_of_pos ht] at h; exact absurd h (EReal.coe_ne_bot r)
  | top => rw [EReal.top_mul_coe_of_pos ht] at h; exact absurd h (EReal.coe_ne_top r)
  | coe a =>
    rw [← EReal.coe_mul, EReal.coe_eq_coe_iff] at h
    rw [EReal.coe_eq_coe_iff, h, mul_div_cancel_right₀ _ ht.ne']

lemma mul_coe_le {a : EReal} {r t : ℝ} (ht : 0 < t) (h : a * (t : EReal) ≤ (r : EReal)) :
    a ≠ ⊤ ∧ a ≤ ((r / t : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot => exact ⟨bot_ne_top, bot_le⟩
  | top =>
    rw [EReal.top_mul_coe_of_pos ht] at h
    exact absurd (top_le_iff.1 h) (EReal.coe_ne_top r)
  | coe a =>
    refine ⟨EReal.coe_ne_top a, ?_⟩
    rw [← EReal.coe_mul, EReal.coe_le_coe_iff] at h
    rw [EReal.coe_le_coe_iff, le_div_iff₀ ht]
    exact h

lemma rev_le_Vopt {f : Fees S B} {p : S → ℝ} {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ}
    (h : Feasible3 M f p x qs qb) : ((revenue M f p x : ℝ) : EReal) ≤ Vopt M := by
  unfold Vopt
  exact le_iSup_of_le f (le_iSup_of_le p (le_iSup_of_le x (le_iSup_of_le qs
    (le_iSup_of_le qb (le_iSup_of_le h le_rfl)))))

lemma sys8_equilibrium (hM : MarketHyp M) {f : Fees S B} {p : S → ℝ} {x : S → B → ℝ}
    {qs : S → ℝ} {qb : B → ℝ} (hf : InGammaU f) (hg1 : ∀ i, f.gs i < 1)
    (hfeas : Feasible7 M x qs qb) (h8 : System8 M x qs qb f p) :
    IsEquilibrium M f p x qs qb ∧ ((revenue M f p x : ℝ) : EReal) = obj7 M qs qb := by
  dsimp only [System8] at h8
  obtain ⟨h8a, h8b, h8c, h8d, h8e, -⟩ := h8
  obtain ⟨hfb, hfs, hqb, hqs, hx0⟩ := hfeas
  have hp : ∀ i, 0 ≤ p i := fun i => (h8e i).2.2
  have hqs0 : ∀ i, 0 ≤ qs i := fun i => by
    have h := hfs i
    rw [sub_eq_zero] at h
    rw [h]
    exact Finset.sum_nonneg fun j hj => hx0 (i, j) (Finset.mem_filter.1 hj).2
  have hqb0 : ∀ j, 0 ≤ qb j := fun j => by
    have h := hfb j
    rw [sub_eq_zero] at h
    rw [← h]
    exact Finset.sum_nonneg fun i hi => hx0 (i, j) (Finset.mem_filter.1 hi).2
  -- sellers
  have hsel : ∀ i, qs i = M.s i * M.Fs i ((1 - f.gs i) * p i - f.ms i) ∧
      (qs i = 0 ∨ Finv (M.Fs i) (qs i / M.s i) = (((1 - f.gs i) * p i - f.ms i : ℝ) : EReal)) := by
    intro i
    have hF := hM.2.2.2.2.2.1 i
    have hs := hM.1 i
    have h1 : 0 < 1 - f.gs i := by linarith [hg1 i]
    have h1' : 1 - f.gs i ≠ 0 := h1.ne'
    rcases (hqs0 i).lt_or_eq with hpos | hzero
    · have hFv := coe_eq_mul_coe (by positivity : (0:ℝ) < 1 / (1 - f.gs i)) (h8a i hpos)
      have hw : (p i - f.ms i / (1 - f.gs i)) / (1 / (1 - f.gs i)) =
          (1 - f.gs i) * p i - f.ms i := by
        rw [div_div_eq_mul_div, div_one, sub_mul, div_mul_cancel₀ _ h1']; ring
      rw [hw] at hFv
      refine ⟨?_, Or.inr hFv⟩
      have hu0 : 0 < qs i / M.s i := div_pos hpos hs
      have hu1 : qs i / M.s i ≤ 1 := (div_le_one hs).2 (hqs i)
      rcases hu1.lt_or_eq with hlt | heq1
      · obtain ⟨v, -, hFv', hv⟩ := exists_F_eq hF hu0 hlt
        rw [hv, EReal.coe_eq_coe_iff] at hFv
        rw [← hFv, hFv']
        field_simp
      · rw [heq1] at hFv
        have hvb := F_vbar hF (by rw [hFv]; exact EReal.coe_ne_top _)
        rw [hFv, EReal.toReal_coe] at hvb
        rw [hvb, mul_one]
        exact (div_eq_one_iff_eq hs.ne').1 heq1
    · have hle := h8b i hzero.symm
      have hle' : p i * (1 - f.gs i) ≤ f.ms i := (le_div_iff₀ h1).1 (by linarith)
      have hw0 : (1 - f.gs i) * p i - f.ms i ≤ 0 := by nlinarith
      exact ⟨by rw [hF.2.1 _ hw0, mul_zero]; exact hzero.symm, Or.inl hzero.symm⟩
  -- the buyer side: a positive edge pins down `minCost` and the inverse demand
  have hmin : ∀ i j, (i, j) ∈ M.E → 0 < x i j →
      minCost M f p j = (1 + f.gb j) * p i + M.c i ∧
      Finv (M.Fb j) (1 - qb j / M.b j) = (((1 + f.gb j) * p i + M.c i + f.mb j : ℝ) : EReal) := by
    intro i j hij hx
    have hgb : (0:ℝ) < 1 + f.gb j := by linarith [hf.2.1 j]
    have hgb' : 1 + f.gb j ≠ 0 := hgb.ne'
    have ht : (0:ℝ) < 1 / (1 + f.gb j) := by positivity
    have key : ∀ k, (k, j) ∈ M.E → 0 < x k j → Finv (M.Fb j) (1 - qb j / M.b j) =
        (((1 + f.gb j) * p k + M.c k + f.mb j : ℝ) : EReal) := by
      intro k hk hxk
      have h := coe_eq_mul_coe ht (h8c (k, j) hk hxk)
      dsimp only at h
      rw [h]
      congr 1
      field_simp <;> ring
    have hV := key i hij hx
    have hge : ∀ k, (k, j) ∈ M.E → (1 + f.gb j) * p i + M.c i ≤ (1 + f.gb j) * p k + M.c k := by
      intro k hk
      rcases (hx0 (k, j) hk).lt_or_eq with hxk | hxk
      · have h := key k hk hxk
        rw [hV, EReal.coe_eq_coe_iff] at h
        linarith
      · have h := h8d (k, j) hk hxk.symm
        dsimp only at h
        have h2 := (mul_coe_le ht h).2
        rw [hV, EReal.coe_le_coe_iff] at h2
        have e : (p k + f.mb j / (1 + f.gb j) + M.c k * (1 / (1 + f.gb j))) / (1 / (1 + f.gb j)) =
            (1 + f.gb j) * p k + M.c k + f.mb j := by field_simp <;> ring
        rw [e] at h2
        linarith
    refine ⟨le_antisymm (minCost_le f p hij) ?_, hV⟩
    haveI : Nonempty {k : S // (k, j) ∈ M.E} := ⟨⟨i, hij⟩⟩
    exact le_ciInf fun k => hge k.1 k.2
  have hbuy : ∀ j, qb j = M.b j * (1 - M.Fb j (minCost M f p j + f.mb j)) := by
    intro j
    have hF := hM.2.2.2.2.2.2 j
    have hb := hM.2.1 j
    have hsum : qb j = ∑ i ∈ Finset.univ.filter (fun i => (i, j) ∈ M.E), x i j := by
      have := hfb j; linarith
    rcases (hqb0 j).lt_or_eq with hpos | hzero
    · obtain ⟨i, hi, hxi⟩ : ∃ i ∈ Finset.univ.filter (fun i => (i, j) ∈ M.E), 0 < x i j := by
        by_contra hcon
        push Not at hcon
        have := Finset.sum_nonpos hcon
        linarith
      have hij := (Finset.mem_filter.1 hi).2
      obtain ⟨hm, hV⟩ := hmin i j hij hxi
      rw [hm]
      have hu1 : 1 - qb j / M.b j < 1 := by have := div_pos hpos hb; linarith
      have hu0 : 0 ≤ 1 - qb j / M.b j := by have := (div_le_one hb).2 (hqb j); linarith
      rcases hu0.lt_or_eq with hlt | heq0
      · obtain ⟨v, -, hFv, hv⟩ := exists_F_eq hF hlt hu1
        rw [hv, EReal.coe_eq_coe_iff] at hV
        rw [← hV, hFv, sub_sub_cancel]
        field_simp
      · rw [← heq0, Finv_zero hF] at hV
        have hV0 : (1 + f.gb j) * p i + M.c i + f.mb j = 0 := by exact_mod_cast hV.symm
        rw [hV0, hF.2.1 0 le_rfl]
        have : qb j / M.b j = 1 := by linarith
        rw [(div_eq_one_iff_eq hb.ne').1 this]
        ring
    · have hzero' : qb j = 0 := hzero.symm
      have hall : ∀ i ∈ Finset.univ.filter (fun i => (i, j) ∈ M.E), x i j = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => hx0 (i, j) (Finset.mem_filter.1 hi).2)).1
          (by rw [← hsum, hzero'])
      have hgb : (0:ℝ) < 1 + f.gb j := by linarith [hf.2.1 j]
      have hgb' : 1 + f.gb j ≠ 0 := hgb.ne'
      have ht : (0:ℝ) < 1 / (1 + f.gb j) := by positivity
      have hle : ∀ i, (i, j) ∈ M.E → Finv (M.Fb j) 1 ≠ ⊤ ∧
          Finv (M.Fb j) 1 ≤ (((1 + f.gb j) * p i + M.c i + f.mb j : ℝ) : EReal) := by
        intro i hi
        have h := h8d (i, j) hi (hall i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩))
        dsimp only at h
        rw [hzero', zero_div, sub_zero] at h
        have h2 := mul_coe_le ht h
        have e : (p i + f.mb j / (1 + f.gb j) + M.c i * (1 / (1 + f.gb j))) / (1 / (1 + f.gb j)) =
            (1 + f.gb j) * p i + M.c i + f.mb j := by field_simp <;> ring
        rw [e] at h2
        exact h2
      obtain ⟨i0, hi0⟩ := hM.2.2.2.2.1 j
      have hfin := (hle i0 hi0).1
      have hbot : Finv (M.Fb j) 1 ≠ ⊥ := ne_bot_of_le_ne_bot EReal.zero_ne_bot (Finv_nonneg 1)
      have hcoe := EReal.coe_toReal hfin hbot
      have hVle : (Finv (M.Fb j) 1).toReal ≤ minCost M f p j + f.mb j := by
        haveI : Nonempty {k : S // (k, j) ∈ M.E} := ⟨⟨i0, hi0⟩⟩
        have : (Finv (M.Fb j) 1).toReal - f.mb j ≤ minCost M f p j := le_ciInf fun k => by
          have h2 := (hle k.1 k.2).2
          rw [← hcoe, EReal.coe_le_coe_iff] at h2
          linarith
        linarith
      have h1 : M.Fb j (minCost M f p j + f.mb j) = 1 :=
        le_antisymm (F_le_one hF _) (by rw [← F_vbar hF hfin]; exact hF.1 hVle)
      rw [h1, hzero']
      ring
  have heqm : IsEquilibrium M f p x qs qb := by
    refine ⟨hp, fun i => (hsel i).1, hbuy, fun i => by have := hfs i; linarith,
      fun j => by have := hfb j; linarith, hx0, ?_⟩
    intro e he hne
    by_contra hx
    have hpos : 0 < x e.1 e.2 := lt_of_le_of_ne (hx0 e he) (Ne.symm hx)
    exact hne (hmin e.1 e.2 he hpos).1.symm
  refine ⟨heqm, ?_⟩
  have hSe : ∀ i, hS M i (qs i) = ((qs i * ((1 - f.gs i) * p i - f.ms i) : ℝ) : EReal) := by
    intro i
    unfold hS
    rcases (hsel i).2 with h0 | h1
    · rw [h0]; simp
    · rw [h1, ← EReal.coe_mul, mul_comm]
  have hg : ∀ j, gB M j (qb j) = qb j * (minCost M f p j + f.mb j) := fun j =>
    gB_eq (hM.2.2.2.2.2.2 j) (hM.2.1 j) (add_nonneg (minCost_nonneg hM hf hp j) (hf.2.2.2 j))
      (hbuy j)
  unfold obj7
  rw [Finset.sum_congr rfl (fun i _ => hSe i), ← coe_sum', ← EReal.coe_sub, ← EReal.coe_sub,
    EReal.coe_eq_coe_iff, rev_identity heqm, Finset.sum_congr rfl (fun j _ => hg j)]
  have h2 : ∑ i, qs i * (M.c i + ((1 - f.gs i) * p i - f.ms i)) =
      ∑ i, M.c i * qs i + ∑ i, qs i * ((1 - f.gs i) * p i - f.ms i) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  linarith

lemma sys8_optimal (hM : MarketHyp M) {xbar : S → B → ℝ} {qsbar : S → ℝ} {qbbar : B → ℝ}
    (hopt : IsOptimal7 M xbar qsbar qbbar) {f : Fees S B} {p : S → ℝ} {x : S → B → ℝ}
    (hf : InGammaU f) (hg1 : ∀ i, f.gs i < 1) (hfeas : Feasible7 M x qsbar qbbar)
    (h8 : System8 M x qsbar qbbar f p) :
    IsEquilibrium M f p x qsbar qbbar ∧ ((revenue M f p x : ℝ) : EReal) = Vopt M ∧
      Vopt M = obj7 M qsbar qbbar := by
  obtain ⟨heq, hrev⟩ := sys8_equilibrium hM hf hg1 hfeas h8
  have h1 := rev_le_Vopt (M := M) ⟨hf, heq⟩
  have h2 := Vopt_le_obj7 hM hopt
  refine ⟨heq, le_antisymm h1 (h2.trans hrev.ge), le_antisymm h2 ?_⟩
  rw [← hrev]; exact h1

end PartC


/-! ## Part D (concavity tools for uniqueness of the optimum of (7)). -/

section PartD1

variable {F : ℝ → ℝ}

/-- Left continuity of `Finv` at `1` when the support is bounded (A10). -/
lemma Finv_toReal_tendsto (hF : IsValueCDF F) (hfin : Finv F 1 ≠ ⊤) :
    Tendsto (fun u => (Finv F u).toReal) (𝓝[<] 1) (𝓝 (Finv F 1).toReal) := by
  have hbot : ∀ u, Finv F u ≠ ⊥ := fun u => ne_bot_of_le_ne_bot EReal.zero_ne_bot (Finv_nonneg u)
  have hle : ∀ u, u ≤ 1 → (Finv F u).toReal ≤ (Finv F 1).toReal := fun u hu =>
    EReal.toReal_le_toReal (Finv_mono hu) (hbot u) hfin
  have hcoe := EReal.coe_toReal hfin (hbot 1)
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => eventually_nhdsWithin_of_forall fun u hu =>
    lt_of_le_of_lt (hle u (le_of_lt hu)) ha⟩
  set V := (Finv F 1).toReal with hV
  set r := (a + V) / 2 with hr
  rcases le_or_gt r 0 with hr0 | hr0
  · exact eventually_nhdsWithin_of_forall fun u _ =>
      lt_of_lt_of_le (by linarith) (EReal.toReal_nonneg (Finv_nonneg u))
  · have hFr : F r < 1 := by
      by_contra hc
      push Not at hc
      have h1 := Finv_le_of (F := F) hr0.le hc
      rw [← hcoe, EReal.coe_le_coe_iff] at h1
      linarith
    filter_upwards [Ioo_mem_nhdsLT hFr] with u hu
    have h1 : (r : EReal) ≤ Finv F u := le_Finv fun r' _ hr' => by
      by_contra hc
      push Not at hc
      have := hF.1 hc.le
      linarith [hu.1]
    have hfu : Finv F u ≠ ⊤ := Finv_lt_top hF hu.2
    have h2 := EReal.coe_toReal hfu (hbot u)
    rw [← h2, EReal.coe_le_coe_iff] at h1
    linarith

end PartD1

/-- Strict midpoint concavity across the endpoint `1` of `[0,1)` for a left-continuous function. -/
lemma strict_mid_endpoint {ψ : ℝ → ℝ} (hψ : StrictConcaveOn ℝ (Set.Ico (0:ℝ) 1) ψ)
    (hlim : Tendsto ψ (𝓝[<] 1) (𝓝 (ψ 1))) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (ψ a + ψ 1) / 2 < ψ ((a + 1) / 2) := by
  set m := (a + 1) / 2 with hm
  set t := (a + m) / 2 with ht
  have hmI : m ∈ Set.Ico (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have htI : t ∈ Set.Ico (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have haI : a ∈ Set.Ico (0:ℝ) 1 := ⟨ha0, ha1⟩
  have hstrict : (ψ a + ψ m) / 2 < ψ t := by
    have h := hψ.2 haI hmI (ne_of_lt (by linarith)) (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    simp only [smul_eq_mul] at h
    have e : 1/2 * a + 1/2 * m = t := by rw [ht]; ring
    rw [e] at h
    linarith
  have hweak : 2/3 * ψ t + (1 - 2/3) * ψ 1 ≤ ψ m := by
    have h1 : Tendsto (fun u : ℝ => u) (𝓝[<] 1) (𝓝 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have h1t : (1:ℝ) - t ≠ 0 := (sub_pos.2 (by linarith : t < 1)).ne'
    have hl : Tendsto (fun u : ℝ => (u - m) / (u - t)) (𝓝[<] 1) (𝓝 ((1 - m) / (1 - t))) :=
      (h1.sub_const m).div (h1.sub_const t) h1t
    have hL : Tendsto (fun u : ℝ => (u - m) / (u - t) * ψ t + (1 - (u - m) / (u - t)) * ψ u)
        (𝓝[<] 1) (𝓝 ((1 - m) / (1 - t) * ψ t + (1 - (1 - m) / (1 - t)) * ψ 1)) :=
      (hl.mul_const _).add ((tendsto_const_nhds.sub hl).mul hlim)
    have hval : (1 - m) / (1 - t) = 2/3 := by
      have e1 : 1 - t = 3/4 * (1 - a) := by rw [ht, hm]; ring
      have e2 : 1 - m = 1/2 * (1 - a) := by rw [hm]; ring
      have ha' : (1:ℝ) - a ≠ 0 := (sub_pos.2 ha1).ne'
      rw [e1, e2]
      field_simp
      ring
    rw [hval] at hL
    refine le_of_tendsto hL ?_
    filter_upwards [Ioo_mem_nhdsLT (show m < 1 by linarith)] with u hu
    have hut : 0 < u - t := by linarith [hu.1]
    have hut' : u - t ≠ 0 := hut.ne'
    have hl0 : 0 ≤ (u - m) / (u - t) := div_nonneg (by linarith [hu.1]) hut.le
    have hl1 : (u - m) / (u - t) ≤ 1 := (div_le_one hut).2 (by linarith)
    have huI : u ∈ Set.Ico (0:ℝ) 1 := ⟨by linarith [hu.1], hu.2⟩
    have hc := hψ.concaveOn.2 htI huI hl0
      (by linarith : (0:ℝ) ≤ 1 - (u - m) / (u - t)) (by ring)
    simp only [smul_eq_mul] at hc
    have e : (u - m) / (u - t) * t + (1 - (u - m) / (u - t)) * u = m := by
      field_simp
      ring
    rw [e] at hc
    exact hc
  linarith

/-- Midpoint (strict) concavity of `k * φ` for a strictly concave `φ`. -/
lemma mid_of_strict {φ : ℝ → ℝ} {C : Set ℝ} (hφ : StrictConcaveOn ℝ C φ) {k u u' : ℝ}
    (hk : 0 < k) (hu : u ∈ C) (hu' : u' ∈ C) :
    (k * φ u + k * φ u') / 2 ≤ k * φ ((u + u') / 2) ∧
      (u ≠ u' → (k * φ u + k * φ u') / 2 < k * φ ((u + u') / 2)) := by
  have e : 1/2 * u + 1/2 * u' = (u + u') / 2 := by ring
  have h := hφ.concaveOn.2 hu hu' (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num)
  simp only [smul_eq_mul] at h
  rw [e] at h
  refine ⟨by have := mul_le_mul_of_nonneg_left h hk.le; linarith, fun hne => ?_⟩
  have h2 := hφ.2 hu hu' hne (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
    (by norm_num)
  simp only [smul_eq_mul] at h2
  rw [e] at h2
  have := mul_lt_mul_of_pos_left h2 hk
  linarith

/-! ### Part D2: uniqueness of the optimal (qs, qb) of (7) -/

lemma psi_mid {ψ : ℝ → ℝ} (hc : StrictConcaveOn ℝ (Set.Ico (0:ℝ) 1) ψ) {a a' s : ℝ}
    (hlim : (a = 1 ∨ a' = 1) → Tendsto ψ (𝓝[<] 1) (𝓝 (ψ 1)))
    (hs : 0 < s) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ha0' : 0 ≤ a') (ha1' : a' ≤ 1) (hne : a ≠ a') :
    (s * ψ a + s * ψ a') / 2 < s * ψ ((a + a') / 2) := by
  rcases lt_or_eq_of_le ha1 with h1 | h1
  · rcases lt_or_eq_of_le ha1' with h1' | h1'
    · exact (mid_of_strict hc hs ⟨ha0, h1⟩ ⟨ha0', h1'⟩).2 hne
    · subst h1'
      have h := strict_mid_endpoint hc (hlim (Or.inr rfl)) ha0 h1
      have := mul_lt_mul_of_pos_left h hs
      linarith
  · subst h1
    have h1' : a' < 1 := lt_of_le_of_ne ha1' (Ne.symm hne)
    have h := strict_mid_endpoint hc (hlim (Or.inl rfl)) ha0' h1'
    have := mul_lt_mul_of_pos_left h hs
    rw [add_comm (1:ℝ) a']
    linarith

section PartD2

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] {M : Market S B}

/-- Real seller term `q F⁻¹(q/s)`. -/
noncomputable def hR (M : Market S B) (i : S) (q : ℝ) : ℝ :=
  q * (Finv (M.Fs i) (q / M.s i)).toReal

/-- Real form of the objective (7a) when every seller term is finite. -/
noncomputable def Jr (M : Market S B) (qs : S → ℝ) (qb : B → ℝ) : ℝ :=
  ∑ j, gB M j (qb j) - ∑ i, (hR M i (qs i) + M.c i * qs i)

lemma hS_coe {i : S} {q : ℝ} (hfin : Finv (M.Fs i) (q / M.s i) ≠ ⊤) :
    hS M i q = ((hR M i q : ℝ) : EReal) := by
  unfold hS hR
  have hb : Finv (M.Fs i) (q / M.s i) ≠ ⊥ :=
    ne_bot_of_le_ne_bot EReal.zero_ne_bot (Finv_nonneg _)
  rw [← EReal.coe_toReal hfin hb, ← EReal.coe_mul, EReal.toReal_coe, mul_comm]

lemma obj7_coe {qs : S → ℝ} {qb : B → ℝ}
    (hfin : ∀ i, Finv (M.Fs i) (qs i / M.s i) ≠ ⊤) :
    obj7 M qs qb = ((Jr M qs qb : ℝ) : EReal) := by
  unfold obj7 Jr
  rw [Finset.sum_congr rfl (fun i _ => hS_coe (M := M) (hfin i)), ← coe_sum',
    ← EReal.coe_sub, ← EReal.coe_sub, Finset.sum_add_distrib]
  congr 1
  ring

lemma fin_of_obj7_nonneg (hM : MarketHyp M) {qs : S → ℝ} {qb : B → ℝ}
    (hq : ∀ i, 0 ≤ qs i) (h0 : (0 : EReal) ≤ obj7 M qs qb) :
    ∀ i, Finv (M.Fs i) (qs i / M.s i) ≠ ⊤ := by
  intro i htop
  have hqi : qs i ≠ 0 := by
    intro h0'
    rw [h0', zero_div, Finv_zero (hM.2.2.2.2.2.1 i)] at htop
    exact EReal.zero_ne_top htop
  have hpos : 0 < qs i := lt_of_le_of_ne (hq i) (Ne.symm hqi)
  have hti : hS M i (qs i) = ⊤ := by
    unfold hS; rw [htop]; exact EReal.top_mul_of_pos (by exact_mod_cast hpos)
  have hnn : ∀ k ∈ (Finset.univ : Finset S), (0 : EReal) ≤ hS M k (qs k) := fun k _ =>
    EReal.mul_nonneg (Finv_nonneg _) (by exact_mod_cast hq k)
  have hsum : ∑ k, hS M k (qs k) = ⊤ := by
    have := Finset.single_le_sum hnn (Finset.mem_univ i)
    rw [hti] at this
    exact top_le_iff.1 this
  unfold obj7 at h0
  rw [hsum, EReal.sub_top, EReal.bot_sub] at h0
  exact absurd h0 (not_le.2 EReal.bot_lt_zero)

lemma feas7_nonneg {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ} (h : Feasible7 M x qs qb) :
    (∀ i, 0 ≤ qs i) ∧ (∀ j, 0 ≤ qb j) := by
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have := h.2.1 i
    have hs : 0 ≤ ∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ M.E), x i j :=
      Finset.sum_nonneg fun j hj => h.2.2.2.2 (i, j) (Finset.mem_filter.1 hj).2
    linarith
  · have := h.1 j
    have hs : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => (i, j) ∈ M.E), x i j :=
      Finset.sum_nonneg fun i hi => h.2.2.2.2 (i, j) (Finset.mem_filter.1 hi).2
    linarith

lemma feas7_mid {x x' : S → B → ℝ} {qs qs' : S → ℝ} {qb qb' : B → ℝ}
    (h : Feasible7 M x qs qb) (h' : Feasible7 M x' qs' qb') :
    Feasible7 M (fun i j => (x i j + x' i j) / 2) (fun i => (qs i + qs' i) / 2)
      (fun j => (qb j + qb' j) / 2) := by
  refine ⟨fun j => ?_, fun i => ?_, fun j => ?_, fun i => ?_, fun e he => ?_⟩
  · simp only
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    linarith [h.1 j, h'.1 j]
  · simp only
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    linarith [h.2.1 i, h'.2.1 i]
  · simp only; linarith [h.2.2.1 j, h'.2.2.1 j]
  · simp only; linarith [h.2.2.2.1 i, h'.2.2.2.1 i]
  · simp only; linarith [h.2.2.2.2 e he, h'.2.2.2.2 e he]

lemma obj7_zero (hM : MarketHyp M) : obj7 M (fun _ => 0) (fun _ => 0) = 0 := by
  have hfin : ∀ i, Finv (M.Fs i) ((fun _ : S => (0:ℝ)) i / M.s i) ≠ ⊤ := fun i => by
    simp only [zero_div]; rw [Finv_zero (hM.2.2.2.2.2.1 i)]; exact EReal.zero_ne_top
  rw [obj7_coe hfin]
  unfold Jr hR gB
  simp

lemma feas7_zero (hM : MarketHyp M) :
    Feasible7 M (fun _ _ => 0) (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun j => by simp, fun i => by simp, fun j => (hM.2.1 j).le, fun i => (hM.1 i).le,
    fun e _ => le_refl 0⟩

lemma hR_eq (i : S) (hs : 0 < M.s i) (q : ℝ) :
    hR M i q = -(M.s i * (fun u : ℝ => -u * (Finv (M.Fs i) u).toReal) (q / M.s i)) := by
  have e : M.s i * (q / M.s i) = q := by field_simp
  simp only [hR]
  rw [neg_mul, mul_neg, neg_neg, ← mul_assoc, e]

lemma gB_eq_phi (j : B) (hb : 0 < M.b j) (q : ℝ) :
    gB M j q = M.b j * (fun u : ℝ => u * (Finv (M.Fb j) (1 - u)).toReal) (q / M.b j) := by
  have e : M.b j * (q / M.b j) = q := by field_simp
  simp only [gB]
  rw [← mul_assoc, e]

lemma seller_term (hM : MarketHyp M) (hA : Assumption2 M) (i : S) {q q' : ℝ}
    (hq : 0 ≤ q) (hq' : 0 ≤ q') (hqs : q ≤ M.s i) (hqs' : q' ≤ M.s i)
    (hf : Finv (M.Fs i) (q / M.s i) ≠ ⊤) (hf' : Finv (M.Fs i) (q' / M.s i) ≠ ⊤) :
    hR M i ((q + q') / 2) ≤ (hR M i q + hR M i q') / 2 ∧
      (q ≠ q' → hR M i ((q + q') / 2) < (hR M i q + hR M i q') / 2) := by
  by_cases he : q = q'
  · subst he; rw [add_self_div_two]; exact ⟨by linarith, fun h => absurd rfl h⟩
  refine ⟨?_, fun _ => ?_⟩ <;> [skip; skip] <;> (
    have hs := hM.1 i
    have hF := hM.2.2.2.2.2.1 i
    have hne : q / M.s i ≠ q' / M.s i := fun h => he ((div_left_inj' hs.ne').1 h)
    have hlim : (q / M.s i = 1 ∨ q' / M.s i = 1) →
        Tendsto (fun u : ℝ => -u * (Finv (M.Fs i) u).toReal) (𝓝[<] 1)
          (𝓝 ((fun u : ℝ => -u * (Finv (M.Fs i) u).toReal) 1)) := by
      intro h1
      have hfin : Finv (M.Fs i) 1 ≠ ⊤ := by
        rcases h1 with h1 | h1
        · rwa [h1] at hf
        · rwa [h1] at hf'
      have hn : Tendsto (fun u : ℝ => -u) (𝓝[<] 1) (𝓝 (-1)) :=
        tendsto_nhdsWithin_of_tendsto_nhds (continuous_neg.tendsto 1)
      exact hn.mul (Finv_toReal_tendsto hF hfin)
    have key := psi_mid (hA.2 i) hlim hs (div_nonneg hq hs.le) ((div_le_one hs).2 hqs)
      (div_nonneg hq' hs.le) ((div_le_one hs).2 hqs') hne
    have hm : (q + q') / 2 / M.s i = (q / M.s i + q' / M.s i) / 2 := by ring
    rw [hR_eq i hs, hR_eq i hs, hR_eq i hs, hm]
    linarith)

lemma buyer_term (hM : MarketHyp M) (hA : Assumption2 M) (j : B) {q q' : ℝ}
    (hq : 0 ≤ q) (hq' : 0 ≤ q') (hqb : q ≤ M.b j) (hqb' : q' ≤ M.b j) :
    (gB M j q + gB M j q') / 2 ≤ gB M j ((q + q') / 2) ∧
      (q ≠ q' → (gB M j q + gB M j q') / 2 < gB M j ((q + q') / 2)) := by
  have hb := hM.2.1 j
  have key := mid_of_strict (hA.1 j) hb
    (⟨div_nonneg hq hb.le, (div_le_one hb).2 hqb⟩ : q / M.b j ∈ Set.Icc (0:ℝ) 1)
    (⟨div_nonneg hq' hb.le, (div_le_one hb).2 hqb'⟩ : q' / M.b j ∈ Set.Icc (0:ℝ) 1)
  have hm : (q + q') / 2 / M.b j = (q / M.b j + q' / M.b j) / 2 := by ring
  rw [gB_eq_phi j hb, gB_eq_phi j hb, gB_eq_phi j hb, hm]
  exact ⟨key.1, fun hne => key.2 fun h => hne ((div_left_inj' hb.ne').1 h)⟩

lemma Jr_mid_strict (hM : MarketHyp M) (hA : Assumption2 M) {qs qs' : S → ℝ} {qb qb' : B → ℝ}
    (hqs : ∀ i, 0 ≤ qs i) (hqs' : ∀ i, 0 ≤ qs' i) (hqb : ∀ j, 0 ≤ qb j) (hqb' : ∀ j, 0 ≤ qb' j)
    (hsl : ∀ i, qs i ≤ M.s i) (hsl' : ∀ i, qs' i ≤ M.s i)
    (hbl : ∀ j, qb j ≤ M.b j) (hbl' : ∀ j, qb' j ≤ M.b j)
    (hf : ∀ i, Finv (M.Fs i) (qs i / M.s i) ≠ ⊤) (hf' : ∀ i, Finv (M.Fs i) (qs' i / M.s i) ≠ ⊤)
    (hne : ¬ (qs = qs' ∧ qb = qb')) :
    (Jr M qs qb + Jr M qs' qb') / 2 <
      Jr M (fun i => (qs i + qs' i) / 2) (fun j => (qb j + qb' j) / 2) := by
  set D : B → ℝ := fun j => gB M j ((qb j + qb' j) / 2) - (gB M j (qb j) + gB M j (qb' j)) / 2
    with hD
  set E : S → ℝ := fun i => (hR M i (qs i) + M.c i * qs i + (hR M i (qs' i) + M.c i * qs' i)) / 2
    - (hR M i ((qs i + qs' i) / 2) + M.c i * ((qs i + qs' i) / 2)) with hE
  have hDn : ∀ j ∈ (Finset.univ : Finset B), 0 ≤ D j := fun j _ => by
    have := (buyer_term hM hA j (hqb j) (hqb' j) (hbl j) (hbl' j)).1
    simp only [hD]; linarith
  have hEn : ∀ i ∈ (Finset.univ : Finset S), 0 ≤ E i := fun i _ => by
    have := (seller_term hM hA i (hqs i) (hqs' i) (hsl i) (hsl' i) (hf i) (hf' i)).1
    simp only [hE]; linarith
  have e1 : ∑ j, gB M j ((qb j + qb' j) / 2) - (∑ j, gB M j (qb j) + ∑ j, gB M j (qb' j)) / 2
      = ∑ j, D j := by
    simp only [hD]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib]
  have e2 : (∑ i, (hR M i (qs i) + M.c i * qs i) + ∑ i, (hR M i (qs' i) + M.c i * qs' i)) / 2
      - ∑ i, (hR M i ((qs i + qs' i) / 2) + M.c i * ((qs i + qs' i) / 2)) = ∑ i, E i := by
    simp only [hE]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_add_distrib]
  have hpos : 0 < ∑ j, D j + ∑ i, E i := by
    rcases not_and_or.1 hne with h | h
    · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
      have : 0 < ∑ i, E i := Finset.sum_pos' hEn ⟨i, Finset.mem_univ i, by
        have := (seller_term hM hA i (hqs i) (hqs' i) (hsl i) (hsl' i) (hf i) (hf' i)).2 hi
        simp only [hE]; linarith⟩
      linarith [Finset.sum_nonneg hDn]
    · obtain ⟨j, hj⟩ := Function.ne_iff.1 h
      have : 0 < ∑ j, D j := Finset.sum_pos' hDn ⟨j, Finset.mem_univ j, by
        have := (buyer_term hM hA j (hqb j) (hqb' j) (hbl j) (hbl' j)).2 hj
        simp only [hD]; linarith⟩
      linarith [Finset.sum_nonneg hEn]
  unfold Jr
  linarith

/-- Child `opt7_unique`: the optimal `(q̄s, q̄b)` of (7) is unique. -/
lemma opt7_unique (hM : MarketHyp M) (hA : Assumption2 M) {x x' : S → B → ℝ}
    {qs qs' : S → ℝ} {qb qb' : B → ℝ}
    (h : IsOptimal7 M x qs qb) (h' : IsOptimal7 M x' qs' qb') : qs = qs' ∧ qb = qb' := by
  obtain ⟨hqs, hqb⟩ := feas7_nonneg h.1
  obtain ⟨hqs', hqb'⟩ := feas7_nonneg h'.1
  have h0 : (0 : EReal) ≤ obj7 M qs qb := by
    rw [← obj7_zero hM]; exact h.2 _ _ _ (feas7_zero hM)
  have h0' : (0 : EReal) ≤ obj7 M qs' qb' := by
    rw [← obj7_zero hM]; exact h'.2 _ _ _ (feas7_zero hM)
  have hf := fin_of_obj7_nonneg hM hqs h0
  have hf' := fin_of_obj7_nonneg hM hqs' h0'
  have hJ : Jr M qs' qb' ≤ Jr M qs qb := by
    have := h.2 _ _ _ h'.1
    rw [obj7_coe hf, obj7_coe hf'] at this
    exact_mod_cast this
  have hJ' : Jr M qs qb ≤ Jr M qs' qb' := by
    have := h'.2 _ _ _ h.1
    rw [obj7_coe hf, obj7_coe hf'] at this
    exact_mod_cast this
  by_contra hne
  have hm := feas7_mid h.1 h'.1
  have hmf : ∀ i, Finv (M.Fs i) ((fun i => (qs i + qs' i) / 2) i / M.s i) ≠ ⊤ := by
    intro i
    by_cases he : qs i = qs' i
    · simp only; rw [he, add_self_div_two]; exact hf' i
    · apply Finv_lt_top (hM.2.2.2.2.2.1 i)
      rw [div_lt_one (hM.1 i)]
      have := h.1.2.2.2.1 i
      have := h'.1.2.2.2.1 i
      rcases lt_or_gt_of_ne he with hl | hl <;> linarith
  have hlt := Jr_mid_strict hM hA hqs hqs' hqb hqb' h.1.2.2.2.1 h'.1.2.2.2.1 h.1.2.2.1
    h'.1.2.2.1 hf hf' hne
  have hle := h.2 _ _ _ hm
  rw [obj7_coe hmf, obj7_coe hf] at hle
  have := EReal.coe_le_coe_iff.1 hle
  linarith

end PartD2

/-! ### Part E (first pieces): strict monotonicity of the seller quantile, finite differences, Dec2 -/

section PartE0

variable {F : ℝ → ℝ}

lemma Finv_toReal_mono {u v : ℝ} (huv : u ≤ v) (hv : Finv F v ≠ ⊤) :
    (Finv F u).toReal ≤ (Finv F v).toReal :=
  EReal.toReal_le_toReal (Finv_mono huv)
    (ne_bot_of_le_ne_bot EReal.zero_ne_bot (Finv_nonneg _)) hv

lemma Finv_strict0 (hF : IsValueCDF F)
    (hc : StrictConcaveOn ℝ (Set.Ico (0:ℝ) 1) (fun u => -u * (Finv F u).toReal))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) :
    (Finv F a).toReal < (Finv F b).toReal := by
  have h1 := Finv_toReal_mono (F := F) (u := a) (v := (a + b) / 2) (by linarith)
    (Finv_lt_top hF (by linarith))
  have h2 := Finv_toReal_mono (F := F) (u := (a + b) / 2) (v := b) (by linarith)
    (Finv_lt_top hF hb)
  by_contra hlt
  push_neg at hlt
  have e1 : (Finv F ((a + b) / 2)).toReal = (Finv F a).toReal := le_antisymm (h2.trans hlt) h1
  have e2 : (Finv F b).toReal = (Finv F a).toReal := le_antisymm hlt (h1.trans h2)
  have h := hc.2 ⟨ha, by linarith⟩ ⟨by linarith, hb⟩ hab.ne (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  simp only [smul_eq_mul] at h
  rw [show (1/2:ℝ) * a + 1/2 * b = (a + b) / 2 by ring, e1, e2] at h
  linarith

lemma Finv_strict (hF : IsValueCDF F)
    (hc : StrictConcaveOn ℝ (Set.Ico (0:ℝ) 1) (fun u => -u * (Finv F u).toReal))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hfin : Finv F b ≠ ⊤) :
    (Finv F a).toReal < (Finv F b).toReal :=
  lt_of_lt_of_le (Finv_strict0 hF hc ha (by linarith : a < (a + b) / 2) (by linarith))
    (Finv_toReal_mono (by linarith) hfin)

end PartE0

section PartE1

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] {M : Market S B}

/-- Seller finite difference, strict (A8 from Assumption 2). -/
lemma hR_diff (hM : MarketHyp M) (hA : Assumption2 M) (i : S) {q ε : ℝ} (hε : 0 < ε)
    (hqε : 0 < q - ε) (hq : q ≤ M.s i) (hf : Finv (M.Fs i) (q / M.s i) ≠ ⊤) :
    ε * (Finv (M.Fs i) (q / M.s i)).toReal < hR M i q - hR M i (q - ε) := by
  have hs := hM.1 i
  have hlt := Finv_strict (hM.2.2.2.2.2.1 i) (hA.2 i) (div_nonneg hqε.le hs.le)
    ((div_lt_div_iff_of_pos_right hs).2 (by linarith)) ((div_le_one hs).2 hq) hf
  have := mul_pos hqε (sub_pos.2 hlt)
  simp only [hR]
  linarith

/-- Buyer finite difference (monotonicity of `Finv`). -/
lemma gB_diff (hM : MarketHyp M) (j : B) {q ε : ℝ} (hε : 0 ≤ ε) (hqε : 0 ≤ q - ε) :
    gB M j q - gB M j (q - ε) ≤ ε * (Finv (M.Fb j) (1 - q / M.b j)).toReal := by
  have hb := hM.2.1 j
  rcases eq_or_lt_of_le hqε with h0 | h0
  · have hqe : ε = q := by linarith
    subst hqe
    simp [gB]
  · have hP := Finv_toReal_mono (F := M.Fb j) (u := 1 - q / M.b j) (v := 1 - (q - ε) / M.b j)
      (by have := (div_le_div_iff_of_pos_right hb).2 (by linarith : q - ε ≤ q); linarith)
      (Finv_lt_top (hM.2.2.2.2.2.2 j) (by have := div_pos h0 hb; linarith))
    have := mul_nonneg h0.le (sub_nonneg.2 hP)
    simp only [gB]
    linarith

/-- `Dec2 x i i'`: a direction feasible at `x` that moves one unit of supply from `i'` to `i`. -/
def Dec2 (M : Market S B) (x : S → B → ℝ) (i i' : S) : Prop :=
  ∃ d : S → B → ℝ, (∀ e ∈ M.E, x e.1 e.2 = 0 → 0 ≤ d e.1 e.2) ∧
    (∀ k, ∑ j ∈ Finset.univ.filter (fun j => (k, j) ∈ M.E), d k j =
      (if k = i then (1:ℝ) else 0) - (if k = i' then (1:ℝ) else 0)) ∧
    (∀ j, ∑ k ∈ Finset.univ.filter (fun k => (k, j) ∈ M.E), d k j = 0)

lemma Dec2_refl (x : S → B → ℝ) (i : S) : Dec2 M x i i :=
  ⟨fun _ _ => 0, fun _ _ _ => le_refl 0, fun k => by simp, fun j => by simp⟩

lemma Dec2_trans {x : S → B → ℝ} {i1 i2 i3 : S} (h12 : Dec2 M x i1 i2) (h23 : Dec2 M x i2 i3) :
    Dec2 M x i1 i3 := by
  obtain ⟨d1, h1, s1, b1⟩ := h12
  obtain ⟨d2, h2, s2, b2⟩ := h23
  refine ⟨fun k l => d1 k l + d2 k l, fun e he hx => add_nonneg (h1 e he hx) (h2 e he hx),
    fun k => ?_, fun j => ?_⟩
  · rw [Finset.sum_add_distrib, s1, s2]; ring
  · rw [Finset.sum_add_distrib, b1, b2]; ring

lemma Dec2_edge {x : S → B → ℝ} {i i2 : S} {j : B} (hij : (i, j) ∈ M.E) (hi2j : (i2, j) ∈ M.E)
    (hx : 0 < x i2 j) : Dec2 M x i i2 := by
  refine ⟨fun k l => if l = j then ((if k = i then (1:ℝ) else 0) - (if k = i2 then 1 else 0))
    else 0, ?_, fun k => ?_, fun l => ?_⟩
  · rintro ⟨k, l⟩ _ hx0
    simp only at hx0 ⊢
    split_ifs <;> subst_vars <;> linarith
  · rw [Finset.sum_ite_eq']
    by_cases hkj : (k, j) ∈ M.E
    · simp [hkj]
    · have h1 : k ≠ i := by rintro rfl; exact hkj hij
      have h2 : k ≠ i2 := by rintro rfl; exact hkj hi2j
      simp [hkj, h1, h2]
  · by_cases hl : l = j
    · subst hl
      simp [Finset.sum_sub_distrib, hij, hi2j]
    · simp [hl]

end PartE1

section PartE2

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] {M : Market S B}

lemma small_eps {ι : Type} (T : Finset ι) (a g : ι → ℝ) (ha : ∀ t ∈ T, 0 < a t) {q : ℝ}
    (hq : 0 < q) : ∃ ε, 0 < ε ∧ ε < q ∧ ∀ t ∈ T, 0 ≤ a t + ε * g t := by
  have h1 : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ t ∈ T, 0 < a t + ε * g t := by
    rw [Filter.eventually_all_finset]
    intro t ht
    have h : Tendsto (fun ε : ℝ => a t + ε * g t) (𝓝[>] 0) (𝓝 (a t + 0 * g t)) :=
      tendsto_const_nhds.add
        ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).mul tendsto_const_nhds)
    exact h.eventually_const_lt (by simpa using ha t ht)
  have h2 : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε ∧ ε < q :=
    (eventually_mem_nhdsWithin).and
      ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).eventually_lt_const hq)
  obtain ⟨ε, ⟨hε0, hεq⟩, hT⟩ := (h2.and h1).exists
  exact ⟨ε, hε0, hεq, fun t ht => (hT t ht).le⟩

/-- Moving `ε` along a `Dec2 i2 i'` direction minus the support edge `(i2, j)` stays feasible:
seller `i'` and buyer `j` each lose `ε`. -/
lemma dir_feas {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ} (hfeas : Feasible7 M x qs qb)
    {d : S → B → ℝ} {i2 i' : S} {j : B}
    (hdn : ∀ e ∈ M.E, x e.1 e.2 = 0 → 0 ≤ d e.1 e.2)
    (hds : ∀ k, ∑ l ∈ Finset.univ.filter (fun l => (k, l) ∈ M.E), d k l =
      (if k = i2 then (1:ℝ) else 0) - (if k = i' then (1:ℝ) else 0))
    (hdb : ∀ l, ∑ k ∈ Finset.univ.filter (fun k => (k, l) ∈ M.E), d k l = 0)
    (hi2j : (i2, j) ∈ M.E) (hx : 0 < x i2 j) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ∀ e ∈ M.E, 0 < x e.1 e.2 →
      0 ≤ x e.1 e.2 + ε * (d e.1 e.2 - if e.1 = i2 ∧ e.2 = j then 1 else 0)) :
    Feasible7 M (fun k l => x k l + ε * (d k l - if k = i2 ∧ l = j then 1 else 0))
      (fun k => qs k - ε * if k = i' then 1 else 0)
      (fun l => qb l - ε * if l = j then 1 else 0) := by
  obtain ⟨hfb, hfs, hqb, hqs, hx0⟩ := hfeas
  have hsumS : ∀ k, ∑ l ∈ Finset.univ.filter (fun l => (k, l) ∈ M.E),
      (if k = i2 ∧ l = j then (1:ℝ) else 0) = if k = i2 then 1 else 0 := by
    intro k
    by_cases hk : k = i2
    · subst hk; simp [hi2j]
    · simp [hk]
  have hsumB : ∀ l, ∑ k ∈ Finset.univ.filter (fun k => (k, l) ∈ M.E),
      (if k = i2 ∧ l = j then (1:ℝ) else 0) = if l = j then 1 else 0 := by
    intro l
    by_cases hl : l = j
    · subst hl; simp [hi2j]
    · simp [hl]
  refine ⟨fun l => ?_, fun k => ?_, fun l => ?_, fun k => ?_, fun e he => ?_⟩
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hdb, hsumB]
    linarith [hfb l]
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hds, hsumS]
    linarith [hfs k]
  · have := hqb l
    dsimp only
    split_ifs <;> linarith
  · have := hqs k
    dsimp only
    split_ifs <;> linarith
  · dsimp only
    by_cases hxe : x e.1 e.2 = 0
    · have hn : ¬(e.1 = i2 ∧ e.2 = j) := by
        rintro ⟨h1, h2⟩; rw [h1, h2] at hxe; linarith
      rw [if_neg hn, sub_zero, hxe, zero_add]
      exact mul_nonneg hε.le (hdn e he hxe)
    · exact hsmall e he (lt_of_le_of_ne (hx0 e he) (Ne.symm hxe))

/-- E1 (Dec lemma): along a `Dec2 i2 i'` chain ending at a support edge `(i2, j)`,
`R_{i'} + c_{i'} < P_j`. -/
lemma dec_lt (hM : MarketHyp M) (hA : Assumption2 M) {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ}
    (hopt : IsOptimal7 M x qs qb) {i2 i' : S} {j : B} (hd : Dec2 M x i2 i')
    (hi2j : (i2, j) ∈ M.E) (hx : 0 < x i2 j) :
    (Finv (M.Fs i') (qs i' / M.s i')).toReal + M.c i' <
      (Finv (M.Fb j) (1 - qb j / M.b j)).toReal := by
  obtain ⟨d, hdn, hds, hdb⟩ := hd
  have key : ∀ q0 : ℝ, 0 < q0 → ∃ ε, 0 < ε ∧ ε < q0 ∧
      Feasible7 M (fun k l => x k l + ε * (d k l - if k = i2 ∧ l = j then 1 else 0))
        (fun k => qs k - ε * if k = i' then 1 else 0)
        (fun l => qb l - ε * if l = j then 1 else 0) := fun q0 hq0 => by
    obtain ⟨ε, hε, hεq, hT⟩ := small_eps (M.E.filter (fun e => 0 < x e.1 e.2))
      (fun e => x e.1 e.2) (fun e => d e.1 e.2 - if e.1 = i2 ∧ e.2 = j then 1 else 0)
      (fun e he => (Finset.mem_filter.1 he).2) hq0
    exact ⟨ε, hε, hεq, dir_feas hopt.1 hdn hds hdb hi2j hx hε
      (fun e he hxe => hT e (Finset.mem_filter.2 ⟨he, hxe⟩))⟩
  obtain ⟨ε1, hε1, -, hF1⟩ := key 1 one_pos
  have hqi' : 0 < qs i' := by
    have := (feas7_nonneg hF1).1 i'
    simp only [if_true, mul_one] at this
    linarith
  obtain ⟨ε, hε, hεq, hF⟩ := key (qs i') hqi'
  obtain ⟨hqs0, hqb0⟩ := feas7_nonneg hopt.1
  have h0 : (0 : EReal) ≤ obj7 M qs qb := by
    rw [← obj7_zero hM]; exact hopt.2 _ _ _ (feas7_zero hM)
  have hf := fin_of_obj7_nonneg hM hqs0 h0
  have hf'' : ∀ k, Finv (M.Fs k) ((fun k => qs k - ε * if k = i' then 1 else 0) k / M.s k) ≠ ⊤ := by
    intro k
    dsimp only
    by_cases hk : k = i'
    · subst hk
      rw [if_pos rfl, mul_one]
      apply Finv_lt_top (hM.2.2.2.2.2.1 _)
      rw [div_lt_one (hM.1 _)]
      linarith [hopt.1.2.2.2.1 k]
    · rw [if_neg hk, mul_zero, sub_zero]; exact hf k
  have hle := hopt.2 _ _ _ hF
  rw [obj7_coe hf'', obj7_coe hf] at hle
  have hJ := EReal.coe_le_coe_iff.1 hle
  unfold Jr at hJ
  dsimp only at hJ
  have eB : ∑ l, gB M l (qb l - ε * if l = j then 1 else 0) =
      ∑ l, gB M l (qb l) + (gB M j (qb j - ε) - gB M j (qb j)) := by
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · simp
    · intro l _ hl; simp [hl]
    · intro h; exact absurd (Finset.mem_univ j) h
  have eS : ∑ k, (hR M k (qs k - ε * if k = i' then 1 else 0) +
        M.c k * (qs k - ε * if k = i' then 1 else 0)) =
      ∑ k, (hR M k (qs k) + M.c k * qs k) +
        ((hR M i' (qs i' - ε) + M.c i' * (qs i' - ε)) - (hR M i' (qs i') + M.c i' * qs i')) := by
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single i']
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ i') h
  rw [eB, eS] at hJ
  have hqbj : 0 ≤ qb j - ε := by
    have := (feas7_nonneg hF).2 j
    simp only [if_true, mul_one] at this
    exact this
  have hgd := gB_diff hM j hε.le hqbj
  have hrd := hR_diff hM hA i' hε (by linarith) (hopt.1.2.2.2.1 i') (hf i')
  by_contra hcon
  push_neg at hcon
  have := mul_le_mul_of_nonneg_left hcon hε.le
  linarith

end PartE2

section PartE4

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] {M : Market S B}

lemma feas_perturb {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ} (hfeas : Feasible7 M x qs qb)
    (dx : S → B → ℝ) (dqs : S → ℝ) (dqb : B → ℝ)
    (hbS : ∀ k, ∑ l ∈ Finset.univ.filter (fun l => (k, l) ∈ M.E), dx k l = dqs k)
    (hbB : ∀ l, ∑ k ∈ Finset.univ.filter (fun k => (k, l) ∈ M.E), dx k l = dqb l)
    (hs : ∀ k, qs k + dqs k ≤ M.s k) (hb : ∀ l, qb l + dqb l ≤ M.b l)
    (hn : ∀ e ∈ M.E, 0 ≤ x e.1 e.2 + dx e.1 e.2) :
    Feasible7 M (fun k l => x k l + dx k l) (fun k => qs k + dqs k) (fun l => qb l + dqb l) := by
  obtain ⟨hfb, hfs, -, -, -⟩ := hfeas
  refine ⟨fun l => ?_, fun k => ?_, hb, hs, hn⟩
  · simp only [Finset.sum_add_distrib, hbB]; linarith [hfb l]
  · simp only [Finset.sum_add_distrib, hbS]; linarith [hfs k]

lemma sumS_ind {i : S} {j : B} (hij : (i, j) ∈ M.E) (a : ℝ) (k : S) :
    ∑ l ∈ Finset.univ.filter (fun l => (k, l) ∈ M.E), (if k = i ∧ l = j then a else 0) =
      if k = i then a else 0 := by
  by_cases hk : k = i
  · subst hk; simp [hij]
  · simp [hk]

lemma sumB_ind {i : S} {j : B} (hij : (i, j) ∈ M.E) (a : ℝ) (l : B) :
    ∑ k ∈ Finset.univ.filter (fun k => (k, l) ∈ M.E), (if k = i ∧ l = j then a else 0) =
      if l = j then a else 0 := by
  by_cases hl : l = j
  · subst hl; simp [hij]
  · simp [hl]

/-- E4: a buyer type that is not served at the optimum has bounded support. -/
lemma vbar_fin (hM : MarketHyp M) {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ}
    (hopt : IsOptimal7 M x qs qb) {j : B} (hqbj : qb j = 0) : Finv (M.Fb j) 1 ≠ ⊤ := by
  intro htop
  obtain ⟨i, hij⟩ := hM.2.2.2.2.1 j
  have hb := hM.2.1 j
  have hs := hM.1 i
  obtain ⟨hqs0, hqb0⟩ := feas7_nonneg hopt.1
  have h0 : (0 : EReal) ≤ obj7 M qs qb := by
    rw [← obj7_zero hM]; exact hopt.2 _ _ _ (feas7_zero hM)
  have hf := fin_of_obj7_nonneg hM hqs0 h0
  have hFb := hM.2.2.2.2.2.2 j
  -- buyer quantile near 1 beats any bound
  have big : ∀ K : ℝ, ∃ η, 0 < η ∧ η < M.b j ∧ ∀ ε, 0 < ε → ε ≤ η →
      K < (Finv (M.Fb j) (1 - ε / M.b j)).toReal := by
    intro K
    obtain ⟨u0, hu0, hu1, hK⟩ := Finv_unbounded hFb htop K
    refine ⟨M.b j * (1 - u0), by nlinarith, by nlinarith, fun ε hε hεη => ?_⟩
    have hle : u0 ≤ 1 - ε / M.b j := by
      have : ε / M.b j ≤ 1 - u0 := by rw [div_le_iff₀ hb]; linarith
      linarith
    have hlt1 : 1 - ε / M.b j < 1 := by have := div_pos hε hb; linarith
    have hfin := Finv_lt_top hFb hlt1
    have h2 : (K : EReal) < Finv (M.Fb j) (1 - ε / M.b j) := lt_of_lt_of_le hK (Finv_mono hle)
    have hbot : Finv (M.Fb j) (1 - ε / M.b j) ≠ ⊥ :=
      ne_bot_of_le_ne_bot EReal.zero_ne_bot (Finv_nonneg _)
    rw [← EReal.coe_toReal hfin hbot] at h2
    exact_mod_cast h2
  rcases eq_or_lt_of_le (hqs0 i) with hqi | hqi
  · -- case B: seller `i` idle, open new supply on `(i, j)`
    have hhalf : Finv (M.Fs i) (1 / 2) ≠ ⊤ := Finv_lt_top (hM.2.2.2.2.2.1 i) (by norm_num)
    obtain ⟨η, hη, hηb, hbig⟩ := big ((Finv (M.Fs i) (1 / 2)).toReal + M.c i)
    set ε := min η (M.s i / 2) with hεdef
    have hε : 0 < ε := lt_min hη (by linarith)
    have hεη : ε ≤ η := min_le_left _ _
    have hεs : ε ≤ M.s i / 2 := min_le_right _ _
    have hF := feas_perturb hopt.1 (fun k l => if k = i ∧ l = j then ε else 0)
      (fun k => if k = i then ε else 0) (fun l => if l = j then ε else 0)
      (sumS_ind hij ε) (sumB_ind hij ε)
      (fun k => by
        by_cases hk : k = i
        · subst hk; rw [if_pos rfl, ← hqi]; linarith
        · rw [if_neg hk]; linarith [hopt.1.2.2.2.1 k])
      (fun l => by
        by_cases hl : l = j
        · subst hl; rw [if_pos rfl, hqbj]; linarith
        · rw [if_neg hl]; linarith [hopt.1.2.2.1 l])
      (fun e he => by
        have := hopt.1.2.2.2.2 e he
        split_ifs <;> linarith)
    have hf'' : ∀ k, Finv (M.Fs k) ((fun k => qs k + if k = i then ε else 0) k / M.s k) ≠ ⊤ := by
      intro k
      dsimp only
      by_cases hk : k = i
      · subst hk
        rw [if_pos rfl, ← hqi, zero_add]
        exact Finv_lt_top (hM.2.2.2.2.2.1 _) (by rw [div_lt_one hs]; linarith)
      · rw [if_neg hk, add_zero]; exact hf k
    have hle := hopt.2 _ _ _ hF
    rw [obj7_coe hf'', obj7_coe hf] at hle
    have hJ := EReal.coe_le_coe_iff.1 hle
    unfold Jr at hJ
    dsimp only at hJ
    have eB : ∑ l, gB M l (qb l + if l = j then ε else 0) =
        ∑ l, gB M l (qb l) + (gB M j (qb j + ε) - gB M j (qb j)) := by
      rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single j]
      · simp
      · intro l _ hl; simp [hl]
      · intro h; exact absurd (Finset.mem_univ j) h
    have eS : ∑ k, (hR M k (qs k + if k = i then ε else 0) +
          M.c k * (qs k + if k = i then ε else 0)) =
        ∑ k, (hR M k (qs k) + M.c k * qs k) +
          ((hR M i (qs i + ε) + M.c i * (qs i + ε)) - (hR M i (qs i) + M.c i * qs i)) := by
      rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
      · simp
      · intro k _ hk; simp [hk]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [eB, eS, hqbj, ← hqi] at hJ
    have hT := hbig ε hε hεη
    have hR0 : hR M i 0 = 0 := by simp [hR]
    have hRε : hR M i (0 + ε) ≤ ε * (Finv (M.Fs i) (1 / 2)).toReal := by
      simp only [hR, zero_add]
      have := Finv_toReal_mono (F := M.Fs i) (u := ε / M.s i) (v := 1 / 2)
        (by rw [div_le_iff₀ hs]; linarith) hhalf
      exact mul_le_mul_of_nonneg_left this hε.le
    have hg0 : gB M j 0 = 0 := by simp [gB]
    have hgε : gB M j (0 + ε) = ε * (Finv (M.Fb j) (1 - ε / M.b j)).toReal := by
      simp only [gB, zero_add]
    rw [hR0, hg0, hgε] at hJ
    have := mul_lt_mul_of_pos_left hT hε
    linarith
  · -- case A: seller `i` active, reroute from a support edge `(i, j')`
    have hpos : ∃ j' ∈ Finset.univ.filter (fun l => (i, l) ∈ M.E), 0 < x i j' := by
      by_contra hno
      push_neg at hno
      have := Finset.sum_nonpos hno
      have h2 := hopt.1.2.1 i
      linarith
    obtain ⟨j', hj'mem, hxj'⟩ := hpos
    have hij' : (i, j') ∈ M.E := (Finset.mem_filter.1 hj'mem).2
    have hjj' : j ≠ j' := by
      rintro rfl
      have hle : x i j ≤ ∑ k ∈ Finset.univ.filter (fun k => (k, j) ∈ M.E), x k j :=
        Finset.single_le_sum (fun k hk => hopt.1.2.2.2.2 (k, j) (Finset.mem_filter.1 hk).2)
          (Finset.mem_filter.2 ⟨Finset.mem_univ i, hij⟩)
      have := hopt.1.1 j
      linarith
    obtain ⟨η, hη, hηb, hbig⟩ := big (Finv (M.Fb j') (1 - qb j' / M.b j')).toReal
    set ε := min η (x i j') with hεdef
    have hε : 0 < ε := lt_min hη hxj'
    have hεη : ε ≤ η := min_le_left _ _
    have hεx : ε ≤ x i j' := min_le_right _ _
    have hF := feas_perturb hopt.1
      (fun k l => (if k = i ∧ l = j then ε else 0) - (if k = i ∧ l = j' then ε else 0))
      (fun _ => 0) (fun l => (if l = j then ε else 0) - (if l = j' then ε else 0))
      (fun k => by simp only [Finset.sum_sub_distrib, sumS_ind hij, sumS_ind hij', sub_self])
      (fun l => by simp only [Finset.sum_sub_distrib, sumB_ind hij, sumB_ind hij'])
      (fun k => by simp only [add_zero]; exact hopt.1.2.2.2.1 k)
      (fun l => by
        by_cases h1 : l = j
        · subst h1; rw [if_pos rfl, if_neg hjj', hqbj]; linarith
        · rw [if_neg h1]
          by_cases h2 : l = j'
          · rw [if_pos h2]; linarith [hopt.1.2.2.1 l]
          · rw [if_neg h2]; linarith [hopt.1.2.2.1 l])
      (fun e he => by
        have hx0 := hopt.1.2.2.2.2 e he
        obtain ⟨k, l⟩ := e
        dsimp only at hx0 ⊢
        split_ifs with ha hb' hb'
        · linarith
        · linarith
        · obtain ⟨rfl, rfl⟩ := hb'; linarith
        · linarith)
    have hf'' : ∀ k, Finv (M.Fs k) ((fun k => qs k + (fun _ => (0:ℝ)) k) k / M.s k) ≠ ⊤ := by
      intro k; simp only [add_zero]; exact hf k
    have hle := hopt.2 _ _ _ hF
    rw [obj7_coe hf'', obj7_coe hf] at hle
    have hJ := EReal.coe_le_coe_iff.1 hle
    unfold Jr at hJ
    simp only [add_zero] at hJ
    have eB : ∑ l, gB M l (qb l + ((if l = j then ε else 0) - (if l = j' then ε else 0))) =
        ∑ l, gB M l (qb l) + ((gB M j (qb j + ε) - gB M j (qb j)) +
          (gB M j' (qb j' - ε) - gB M j' (qb j'))) := by
      rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_add j j' hjj']
      · simp [hjj', hjj'.symm, sub_eq_add_neg]
      · intro l _ hl; simp [hl.1, hl.2]
      · intro h; exact absurd (Finset.mem_univ j) h
      · intro h; exact absurd (Finset.mem_univ j') h
    rw [eB, hqbj] at hJ
    have hqj' : ε ≤ qb j' := by
      have := (feas7_nonneg hF).2 j'
      simp only [if_neg hjj'.symm, if_true] at this
      linarith
    have hgd := gB_diff hM j' hε.le (by linarith : 0 ≤ qb j' - ε)
    have hg0 : gB M j 0 = 0 := by simp [gB]
    have hgε : gB M j (0 + ε) = ε * (Finv (M.Fb j) (1 - ε / M.b j)).toReal := by
      simp only [gB, zero_add]
    rw [hg0, hgε] at hJ
    have := mul_lt_mul_of_pos_left (hbig ε hε hεη) hε
    linarith

end PartE4

section PartE3

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] {M : Market S B}

noncomputable def Rv (M : Market S B) (qs : S → ℝ) (i : S) : ℝ :=
  (Finv (M.Fs i) (qs i / M.s i)).toReal

noncomputable def Pv (M : Market S B) (qb : B → ℝ) (j : B) : ℝ :=
  (Finv (M.Fb j) (1 - qb j / M.b j)).toReal

noncomputable def Vpot (M : Market S B) (x : S → B → ℝ) (qs : S → ℝ) (i : S) : ℝ :=
  ⨆ i' : {i' : S // Dec2 M x i i'}, (Rv M qs i'.1 + M.c i'.1)

lemma Vpot_ge (x : S → B → ℝ) (qs : S → ℝ) {i i' : S} (h : Dec2 M x i i') :
    Rv M qs i' + M.c i' ≤ Vpot M x qs i :=
  le_ciSup (f := fun i' : {i' : S // Dec2 M x i i'} => Rv M qs i'.1 + M.c i'.1)
    (Set.finite_range _).bddAbove ⟨i', h⟩

lemma Vpot_attained (x : S → B → ℝ) (qs : S → ℝ) (i : S) :
    ∃ i', Dec2 M x i i' ∧ Vpot M x qs i = Rv M qs i' + M.c i' := by
  haveI : Nonempty {i' : S // Dec2 M x i i'} := ⟨⟨i, Dec2_refl x i⟩⟩
  obtain ⟨⟨i', h⟩, he⟩ := exists_eq_ciSup_of_finite
    (f := fun i' : {i' : S // Dec2 M x i i'} => Rv M qs i'.1 + M.c i'.1)
  exact ⟨i', h, by rw [Vpot, ← he]⟩

lemma Vpot_mono {x : S → B → ℝ} {qs : S → ℝ} {i i2 : S} (h : Dec2 M x i i2) :
    Vpot M x qs i2 ≤ Vpot M x qs i := by
  obtain ⟨i', h', he⟩ := Vpot_attained (M := M) x qs i2
  rw [he]; exact Vpot_ge x qs (Dec2_trans h h')

noncomputable def mpot (M : Market S B) (x : S → B → ℝ) (qs : S → ℝ) (j : B) : ℝ :=
  ⨅ i : {i : S // (i, j) ∈ M.E}, Vpot M x qs i.1

lemma mpot_le (x : S → B → ℝ) (qs : S → ℝ) {i : S} {j : B} (h : (i, j) ∈ M.E) :
    mpot M x qs j ≤ Vpot M x qs i :=
  ciInf_le (f := fun i : {i : S // (i, j) ∈ M.E} => Vpot M x qs i.1)
    (Set.finite_range _).bddBelow ⟨i, h⟩

lemma mpot_eq {x : S → B → ℝ} {qs : S → ℝ} {i : S} {j : B} (h : (i, j) ∈ M.E)
    (hx : 0 < x i j) : mpot M x qs j = Vpot M x qs i := by
  haveI : Nonempty {i : S // (i, j) ∈ M.E} := ⟨⟨i, h⟩⟩
  exact le_antisymm (mpot_le x qs h) (le_ciInf fun k => Vpot_mono (Dec2_edge k.2 h hx))

noncomputable def basemb (M : Market S B) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ)
    (j : B) : ℝ :=
  if 0 < qb j then Pv M qb j - mpot M x qs j else |Pv M qb j - mpot M x qs j| + 1

lemma pos_qb_of_x {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ} (hfeas : Feasible7 M x qs qb)
    {i : S} {j : B} (h : (i, j) ∈ M.E) (hx : 0 < x i j) : 0 < qb j := by
  have h1 := hfeas.1 j
  have h2 : x i j ≤ ∑ k ∈ Finset.univ.filter (fun k => (k, j) ∈ M.E), x k j :=
    Finset.single_le_sum (f := fun k => x k j)
      (fun k hk => hfeas.2.2.2.2 (k, j) (Finset.mem_filter.1 hk).2)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  linarith

lemma exists_x_of_qb {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ} (hfeas : Feasible7 M x qs qb)
    {j : B} (hq : 0 < qb j) : ∃ i, (i, j) ∈ M.E ∧ 0 < x i j := by
  by_contra hne
  push_neg at hne
  have h1 := hfeas.1 j
  have h2 : ∑ k ∈ Finset.univ.filter (fun k => (k, j) ∈ M.E), x k j ≤ 0 :=
    Finset.sum_nonpos fun k hk => hne k (Finset.mem_filter.1 hk).2
  linarith

lemma basemb_pos (hM : MarketHyp M) (hA : Assumption2 M) {x : S → B → ℝ} {qs : S → ℝ}
    {qb : B → ℝ} (hopt : IsOptimal7 M x qs qb) (j : B) : 0 < basemb M x qs qb j := by
  unfold basemb
  split_ifs with hq
  · obtain ⟨i, hij, hx⟩ := exists_x_of_qb hopt.1 hq
    rw [mpot_eq hij hx]
    obtain ⟨i', hd, he⟩ := Vpot_attained (M := M) x qs i
    have := dec_lt hM hA hopt hd hij hx
    rw [he]; unfold Rv Pv; linarith
  · positivity

lemma finS_opt (hM : MarketHyp M) {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ}
    (hopt : IsOptimal7 M x qs qb) (i : S) : Finv (M.Fs i) (qs i / M.s i) ≠ ⊤ := by
  have h0 : (0 : EReal) ≤ obj7 M qs qb := by
    rw [← obj7_zero hM]; exact hopt.2 _ _ _ (feas7_zero hM)
  exact fin_of_obj7_nonneg hM (feas7_nonneg hopt.1).1 h0 i

lemma finB_opt (hM : MarketHyp M) {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ}
    (hopt : IsOptimal7 M x qs qb) (j : B) : Finv (M.Fb j) (1 - qb j / M.b j) ≠ ⊤ := by
  rcases ((feas7_nonneg hopt.1).2 j).lt_or_eq with h | h
  · exact Finv_lt_top (hM.2.2.2.2.2.2 j) (by have := div_pos h (hM.2.1 j); linarith)
  · rw [← h, zero_div, sub_zero]; exact vbar_fin hM hopt h.symm

lemma coe_Rv (hM : MarketHyp M) {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ}
    (hopt : IsOptimal7 M x qs qb) (i : S) :
    Finv (M.Fs i) (qs i / M.s i) = ((Rv M qs i : ℝ) : EReal) :=
  (EReal.coe_toReal (finS_opt hM hopt i)
    (ne_bot_of_le_ne_bot EReal.zero_ne_bot (Finv_nonneg _))).symm

lemma coe_Pv (hM : MarketHyp M) {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ}
    (hopt : IsOptimal7 M x qs qb) (j : B) :
    Finv (M.Fb j) (1 - qb j / M.b j) = ((Pv M qb j : ℝ) : EReal) :=
  (EReal.coe_toReal (finB_opt hM hopt j)
    (ne_bot_of_le_ne_bot EReal.zero_ne_bot (Finv_nonneg _))).symm

lemma Rv_nonneg (qs : S → ℝ) (i : S) : 0 ≤ Rv M qs i :=
  EReal.toReal_nonneg (Finv_nonneg _)

noncomputable def feesT (M : Market S B) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ) (t : ℝ) :
    Fees S B :=
  ⟨fun _ => 0, fun _ => 0, fun i => Vpot M x qs i - M.c i - Rv M qs i + t,
    fun j => basemb M x qs qb j - t⟩

lemma feesT_ok {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ} {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ∀ j, t ≤ basemb M x qs qb j) :
    InGammaU (feesT M x qs qb t) ∧ ∀ i, (feesT M x qs qb t).gs i < 1 := by
  have hVge : ∀ i, Rv M qs i + M.c i ≤ Vpot M x qs i := fun i => Vpot_ge x qs (Dec2_refl x i)
  refine ⟨⟨fun i => ?_, fun j => ?_, fun i => ?_, fun j => ?_⟩, fun i => ?_⟩
  · dsimp only [feesT]; exact ⟨le_rfl, zero_le_one⟩
  · dsimp only [feesT]; exact le_rfl
  · dsimp only [feesT]; linarith [hVge i]
  · dsimp only [feesT]; linarith [ht j]
  · dsimp only [feesT]; exact zero_lt_one

lemma sys8_family (hM : MarketHyp M) {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ}
    (hopt : IsOptimal7 M x qs qb) {t : ℝ} (ht0 : 0 ≤ t) (ht : ∀ j, t ≤ basemb M x qs qb j) :
    System8 M x qs qb (feesT M x qs qb t) (fun i => Vpot M x qs i - M.c i + t) := by
  have hVge : ∀ i, Rv M qs i + M.c i ≤ Vpot M x qs i := fun i => Vpot_ge x qs (Dec2_refl x i)
  dsimp only [System8, feesT]
  simp only [sub_zero, add_zero, div_one, EReal.coe_one, mul_one]
  refine ⟨fun i _ => ?_, fun i hq => ?_, fun e he hx => ?_, fun e he hx => ?_, fun i => ?_,
    fun j => ?_⟩
  · rw [coe_Rv hM hopt i, EReal.coe_eq_coe_iff]; ring
  · have : Rv M qs i = 0 := by simp [Rv, hq, Finv_zero (hM.2.2.2.2.2.1 i)]
    linarith
  · rw [coe_Pv hM hopt e.2, EReal.coe_eq_coe_iff]
    have hq := pos_qb_of_x hopt.1 he hx
    simp only [basemb, if_pos hq, mpot_eq he hx]; ring
  · rw [coe_Pv hM hopt e.2, EReal.coe_le_coe_iff]
    have hm := mpot_le x qs he
    unfold basemb; split_ifs
    · linarith
    · linarith [le_abs_self (Pv M qb e.2 - mpot M x qs e.2)]
  · refine ⟨le_rfl, ?_, ?_⟩ <;> linarith [hVge i, Rv_nonneg (M := M) qs i]
  · refine ⟨zero_le_one, le_rfl, ?_⟩; linarith [ht j]

/-! Inverting the equilibrium equations (Theorem 1(ii)3, "only if"). -/

lemma Finv_tight {F : ℝ → ℝ} (hF : IsValueCDF F) {s q w : ℝ} (hs : 0 < s)
    (hq : q = s * F w) (hq0 : 0 < q) (h : Finv F (q / s) * (q : EReal) = ((q * w : ℝ) : EReal)) :
    Finv F (q / s) = (w : EReal) := by
  have hq' : q / s = F w := by rw [hq, mul_div_cancel_left₀ _ hs.ne']
  rw [hq'] at h ⊢
  have hwpos : 0 < w := by
    by_contra hw; push_neg at hw
    have h0 : F w = 0 := hF.2.1 w hw
    rw [h0, mul_zero] at hq; linarith
  have hle : Finv F (F w) ≤ (w : EReal) := Finv_le_of hwpos.le le_rfl
  have htop : Finv F (F w) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top w) hle
  have hbot : Finv F (F w) ≠ ⊥ := ne_bot_of_le_ne_bot EReal.zero_ne_bot (Finv_nonneg _)
  rw [← EReal.coe_toReal htop hbot] at h ⊢
  rw [← EReal.coe_mul, EReal.coe_eq_coe_iff] at h
  rw [EReal.coe_eq_coe_iff]
  have h2 : (Finv F (F w)).toReal * q = w * q := by rw [h]; ring
  exact mul_right_cancel₀ hq0.ne' h2

lemma tight_seller (hM : MarketHyp M) {f : Fees S B} {p : S → ℝ} {x : S → B → ℝ}
    {qs : S → ℝ} {qb : B → ℝ} (hf : InGammaU f) (heq : IsEquilibrium M f p x qs qb)
    (htight : ((revenue M f p x : ℝ) : EReal) = obj7 M qs qb) (i : S) (hqi : 0 < qs i) :
    Finv (M.Fs i) (qs i / M.s i) = (((1 - f.gs i) * p i - f.ms i : ℝ) : EReal) := by
  have hS' : ∀ i, ∃ a : ℝ, hS M i (qs i) = (a : EReal) ∧
      a ≤ qs i * ((1 - f.gs i) * p i - f.ms i) :=
    fun i => hS_le (hM.2.2.2.2.2.1 i) (hM.1 i) (heq.2.1 i)
  choose a ha ha' using hS'
  have hg : ∀ j, gB M j (qb j) = qb j * (minCost M f p j + f.mb j) := fun j =>
    gB_eq (hM.2.2.2.2.2.2 j) (hM.2.1 j)
      (add_nonneg (minCost_nonneg hM hf heq.1 j) (hf.2.2.2 j)) (heq.2.2.1 j)
  have hobj : obj7 M qs qb =
      ((∑ j, gB M j (qb j) - ∑ i, a i - ∑ i, M.c i * qs i : ℝ) : EReal) := by
    unfold obj7
    rw [Finset.sum_congr rfl (fun i _ => ha i), ← coe_sum', EReal.coe_sub, EReal.coe_sub]
  rw [hobj, EReal.coe_eq_coe_iff, rev_identity heq,
    Finset.sum_congr rfl (fun j _ => hg j)] at htight
  have h2 : ∑ i, qs i * (M.c i + ((1 - f.gs i) * p i - f.ms i)) =
      ∑ i, M.c i * qs i + ∑ i, qs i * ((1 - f.gs i) * p i - f.ms i) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  have hsum : ∑ i, a i = ∑ i, qs i * ((1 - f.gs i) * p i - f.ms i) := by linarith
  have hai : a i = qs i * ((1 - f.gs i) * p i - f.ms i) :=
    (Finset.sum_eq_sum_iff_of_le (fun i _ => ha' i)).1 hsum i (Finset.mem_univ i)
  refine Finv_tight (hM.2.2.2.2.2.1 i) (hM.1 i) (heq.2.1 i) hqi ?_
  have := ha i
  rw [hai] at this
  exact this

lemma aux_div (a b c d : ℝ) (hd : d ≠ 0) :
    a + b / d + c * (1 / d) = (d * a + c + b) * (1 / d) := by
  field_simp <;> ring

lemma eq_sys8 (hM : MarketHyp M) {f : Fees S B} {p : S → ℝ} {x : S → B → ℝ}
    {qs : S → ℝ} {qb : B → ℝ} (hf : InGammaU f) (hg1 : ∀ i, f.gs i < 1)
    (heq : IsEquilibrium M f p x qs qb)
    (htight : ((revenue M f p x : ℝ) : EReal) = obj7 M qs qb) :
    System8 M x qs qb f p := by
  dsimp only [System8]
  have hfeas := eq_feasible7 hM heq
  have hv0 : ∀ j, 0 ≤ minCost M f p j + f.mb j := fun j =>
    add_nonneg (minCost_nonneg hM hf heq.1 j) (hf.2.2.2 j)
  have hu : ∀ j, 1 - qb j / M.b j = M.Fb j (minCost M f p j + f.mb j) := fun j => by
    rw [heq.2.2.1 j, mul_div_cancel_left₀ _ (hM.2.1 j).ne']; ring
  have hBle : ∀ j, Finv (M.Fb j) (1 - qb j / M.b j) ≤
      ((minCost M f p j + f.mb j : ℝ) : EReal) := fun j => Finv_le_of (hv0 j) (hu j).le
  have hBeq : ∀ j, 0 < qb j → Finv (M.Fb j) (1 - qb j / M.b j) =
      ((minCost M f p j + f.mb j : ℝ) : EReal) := by
    intro j hq
    rw [hu j]
    apply Finv_F' (hM.2.2.2.2.2.2 j) (hv0 j)
    rw [← hu j]; have := div_pos hq (hM.2.1 j); linarith
  have hgb : ∀ j, 0 < 1 + f.gb j := fun j => by linarith [hf.2.1 j]
  have hgs : ∀ i, 0 < 1 - f.gs i := fun i => sub_pos.2 (hg1 i)
  refine ⟨fun i hqi => ?_, fun i hqi => ?_, fun e he hx => ?_, fun e he hx => ?_, fun i => ?_,
    fun j => ?_⟩
  · rw [tight_seller hM hf heq htight i hqi, ← EReal.coe_mul, EReal.coe_eq_coe_iff,
      mul_one_div, sub_div, mul_div_cancel_left₀ _ (hgs i).ne']
  · have hF0 : M.Fs i ((1 - f.gs i) * p i - f.ms i) = 0 := by
      have h := heq.2.1 i
      rw [hqi] at h
      rcases mul_eq_zero.1 h.symm with h' | h'
      · exact absurd h' (hM.1 i).ne'
      · exact h'
    have hw := (F_eq_zero_iff (hM.2.2.2.2.2.1 i) _).1 hF0
    have : p i - f.ms i / (1 - f.gs i) = ((1 - f.gs i) * p i - f.ms i) / (1 - f.gs i) := by
      rw [sub_div, mul_div_cancel_left₀ _ (hgs i).ne']
    rw [this, div_nonpos_iff]; right; exact ⟨hw, (hgs i).le⟩
  · have hm : (1 + f.gb e.2) * p e.1 + M.c e.1 = minCost M f p e.2 := by
      by_contra hne; exact hx.ne' (heq.2.2.2.2.2.2 e he hne)
    have hq := pos_qb_of_x hfeas he hx
    rw [hBeq e.2 hq, ← EReal.coe_mul, EReal.coe_eq_coe_iff, aux_div _ _ _ _ (hgb e.2).ne', hm]
  · have hle := hBle e.2
    have htop : Finv (M.Fb e.2) (1 - qb e.2 / M.b e.2) ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top _) hle
    have hbot : Finv (M.Fb e.2) (1 - qb e.2 / M.b e.2) ≠ ⊥ :=
      ne_bot_of_le_ne_bot EReal.zero_ne_bot (Finv_nonneg _)
    rw [← EReal.coe_toReal htop hbot, EReal.coe_le_coe_iff] at hle
    rw [← EReal.coe_toReal htop hbot, ← EReal.coe_mul, EReal.coe_le_coe_iff,
      aux_div _ _ _ _ (hgb e.2).ne']
    have hmc := minCost_le (M := M) f p he
    exact mul_le_mul_of_nonneg_right (by linarith) (by have := hgb e.2; positivity)
  · exact ⟨one_le_one_div (hgs i) (by linarith [(hf.1 i).1]),
      div_nonneg (hf.2.2.1 i) (hgs i).le, heq.1 i⟩
  · exact ⟨div_nonneg zero_le_one (hgb j).le, (div_le_one (hgb j)).2 (by linarith [hf.2.1 j]),
      div_nonneg (hf.2.2.2 j) (hgb j).le⟩

end PartE3

end CS5f

open CS5f

open CommissionsSubscriptions in
theorem solution {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    [Nonempty S] (M : Market S B) (hM : MarketHyp M) (hA2 : Assumption2 M)
    (xbar : S → B → ℝ) (qsbar : S → ℝ) (qbbar : B → ℝ) (hopt : IsOptimal7 M xbar qsbar qbbar) :
    -- (i)
    ((∃ (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ),
        Feasible3 M f p x qs qb ∧ ((revenue M f p x : ℝ) : EReal) = Vopt M) ∧
      Vopt M = obj7 M qsbar qbbar ∧
      (∀ (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ),
        Feasible3 M f p x qs qb → ((revenue M f p x : ℝ) : EReal) = Vopt M →
          qs = qsbar ∧ qb = qbbar)) ∧
    -- (ii)
    ((∃ f f' : Fees S B, f ≠ f' ∧ IsOptimalPair M f ∧ IsOptimalPair M f') ∧
      (∀ f : Fees S B, InGammaU f → (∀ i, f.gs i < 1) →
        ((∀ p : S → ℝ, System8 M xbar qsbar qbbar f p → IsOptimalPair M f) ∧
          (IsOptimalPair M f ↔
            ∃ x' : S → B → ℝ, IsOptimal7 M x' qsbar qbbar ∧
              ∃ p : S → ℝ, System8 M x' qsbar qbbar f p)))) := by
  obtain ⟨i0⟩ := ‹Nonempty S›
  have hpos := basemb_pos hM hA2 hopt
  obtain ⟨j0, -⟩ := hM.2.2.2.1 i0
  haveI : Nonempty B := ⟨j0⟩
  obtain ⟨jm, hjm⟩ := Finite.exists_min (basemb M xbar qsbar qbbar)
  have hf0 := feesT_ok (M := M) (x := xbar) (qs := qsbar) (qb := qbbar) le_rfl
    (fun j => (hpos j).le)
  have hf1 := feesT_ok (M := M) (x := xbar) (qs := qsbar) (qb := qbbar) (hpos jm).le hjm
  have h80 := sys8_family hM hopt le_rfl (fun j => (hpos j).le)
  have h81 := sys8_family hM hopt (hpos jm).le hjm
  have hO0 := sys8_optimal hM hopt hf0.1 hf0.2 hopt.1 h80
  have hO1 := sys8_optimal hM hopt hf1.1 hf1.2 hopt.1 h81
  have hV : Vopt M = obj7 M qsbar qbbar := hO0.2.2
  have hopt' : ∀ {f : Fees S B} {p : S → ℝ} {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ},
      InGammaU f → IsEquilibrium M f p x qs qb → ((revenue M f p x : ℝ) : EReal) = Vopt M →
        IsOptimal7 M x qs qb := by
    intro f p x qs qb hf heq hrev
    have hle := eq_rev_le_obj7 hM hf heq
    exact ⟨eq_feasible7 hM heq, fun x' qs' qb' h =>
      (hopt.2 _ _ _ h).trans (by rw [← hV, ← hrev]; exact hle)⟩
  refine ⟨⟨⟨_, _, xbar, qsbar, qbbar, ⟨hf0.1, hO0.1⟩, hO0.2.1⟩, hV, ?_⟩,
    ⟨⟨_, _, ?_, ⟨hf0.1, _, xbar, qsbar, qbbar, hO0.1, hO0.2.1⟩,
      ⟨hf1.1, _, xbar, qsbar, qbbar, hO1.1, hO1.2.1⟩⟩, ?_⟩⟩
  · intro f p x qs qb hF3 hrev
    obtain ⟨h1, h2⟩ := opt7_unique hM hA2 (hopt' hF3.1 hF3.2 hrev) hopt
    exact ⟨h1, h2⟩
  · intro h
    have := congrArg (fun f : Fees S B => f.ms i0) h
    dsimp only [feesT] at this
    linarith [hpos jm]
  · intro f hf hg1
    refine ⟨fun p h8 => ⟨hf, p, xbar, qsbar, qbbar, (sys8_optimal hM hopt hf hg1 hopt.1 h8).1,
      (sys8_optimal hM hopt hf hg1 hopt.1 h8).2.1⟩, ⟨?_, ?_⟩⟩
    · rintro ⟨-, p, x, qs, qb, heq, hrev⟩
      have ho := hopt' hf heq hrev
      obtain ⟨h1, h2⟩ := opt7_unique hM hA2 hopt ho
      subst h1 h2
      exact ⟨x, ho, p, eq_sys8 hM hf hg1 heq (by rw [hrev, hV])⟩
    · rintro ⟨x', hx', p, h8⟩
      obtain ⟨heq, hrev, -⟩ := sys8_optimal hM hopt hf hg1 hx'.1 h8
      exact ⟨hf, p, x', qsbar, qbbar, heq, hrev⟩
