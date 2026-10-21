-- Prove2me | solution 1 for Avram2004.Canadized.eta_elimination
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T09:08:02.078952+00:00
-- url     : https://prove2.me/submissions/a35cb910-20d1-4371-8bfd-1c09b1015000

import Mathlib
import Definitions.Def_Avram2004_Shared_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale
import Definitions.Def_Avram2004_Shared_reflected
import Definitions.Def_Avram2004_Shared_esscher
import Definitions.Def_Avram2004_Canadized_canadizedProblem

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Avram2004.Canadized.PathCR

/-- A càdlàg real function on `ℝ≥0` is bounded on compact sets. -/
lemma cadlag_bdd (f : ℝ≥0 → ℝ) (hr : ∀ s, ContinuousWithinAt f (Set.Ici s) s)
    (hl : ∀ s : ℝ≥0, 0 < s → ∃ l, Tendsto f (𝓝[<] s) (𝓝 l)) {K : Set ℝ≥0} (hK : IsCompact K) :
    ∃ B, ∀ u ∈ K, |f u| ≤ B := by
  refine hK.induction_on (p := fun S => ∃ B, ∀ u ∈ S, |f u| ≤ B) ⟨0, by simp⟩ ?_ ?_ ?_
  · rintro S T hST ⟨B, hB⟩
    exact ⟨B, fun u hu => hB u (hST hu)⟩
  · rintro S T ⟨B, hB⟩ ⟨C, hC⟩
    exact ⟨max B C, fun u hu => hu.elim (fun h => (hB u h).trans (le_max_left _ _))
      (fun h => (hC u h).trans (le_max_right _ _))⟩
  · intro x _
    have h1 : ∀ᶠ u in 𝓝[≥] x, |f u| ≤ |f x| + 1 :=
      (Filter.Tendsto.abs (hr x)).eventually_le_const (lt_add_one _)
    have h2 : ∃ C, ∀ᶠ u in 𝓝[<] x, |f u| ≤ C := by
      rcases (show (0 : ℝ≥0) ≤ x from zero_le).eq_or_lt with hx | hx
      · refine ⟨0, ?_⟩
        rw [← hx]
        have : Set.Iio (0 : ℝ≥0) = ∅ := by ext u; simp
        rw [this, nhdsWithin_empty]
        exact Filter.eventually_bot
      · obtain ⟨l, hl⟩ := hl x hx
        exact ⟨|l| + 1, (Filter.Tendsto.abs hl).eventually_le_const (lt_add_one _)⟩
    obtain ⟨C, hC⟩ := h2
    have h3 : ∀ᶠ u in 𝓝 x, |f u| ≤ max C (|f x| + 1) := by
      rw [← nhdsLT_sup_nhdsGE]
      exact Filter.eventually_sup.2 ⟨hC.mono fun u hu => hu.trans (le_max_left _ _),
        h1.mono fun u hu => hu.trans (le_max_right _ _)⟩
    exact ⟨_, mem_nhdsWithin_of_mem_nhds h3, ⟨_, fun u hu => hu⟩⟩

lemma cadlag_bddAbove (f : ℝ≥0 → ℝ) (hr : ∀ s, ContinuousWithinAt f (Set.Ici s) s)
    (hl : ∀ s : ℝ≥0, 0 < s → ∃ l, Tendsto f (𝓝[<] s) (𝓝 l)) (t : ℝ≥0) :
    BddAbove (f '' Set.Icc 0 t) := by
  obtain ⟨B, hB⟩ := cadlag_bdd f hr hl (isCompact_Icc (a := (0 : ℝ≥0)) (b := t))
  refine ⟨B, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact (le_abs_self _).trans (hB u hu)

lemma supIcc_nonempty (f : ℝ≥0 → ℝ) (t : ℝ≥0) : (f '' Set.Icc 0 t).Nonempty :=
  ⟨f 0, 0, ⟨le_rfl, zero_le⟩, rfl⟩

lemma le_supIcc (f : ℝ≥0 → ℝ) (hr : ∀ s, ContinuousWithinAt f (Set.Ici s) s)
    (hl : ∀ s : ℝ≥0, 0 < s → ∃ l, Tendsto f (𝓝[<] s) (𝓝 l)) {u t : ℝ≥0} (hut : u ≤ t) :
    f u ≤ sSup (f '' Set.Icc 0 t) :=
  le_csSup (cadlag_bddAbove f hr hl t) ⟨u, ⟨zero_le, hut⟩, rfl⟩

lemma supIcc_mono (f : ℝ≥0 → ℝ) (hr : ∀ s, ContinuousWithinAt f (Set.Ici s) s)
    (hl : ∀ s : ℝ≥0, 0 < s → ∃ l, Tendsto f (𝓝[<] s) (𝓝 l)) :
    Monotone (fun t => sSup (f '' Set.Icc 0 t)) := by
  intro s t hst
  exact csSup_le_csSup (cadlag_bddAbove f hr hl t) (supIcc_nonempty f s)
    (Set.image_mono (Set.Icc_subset_Icc le_rfl hst))

lemma supIcc_rightCont (f : ℝ≥0 → ℝ) (hr : ∀ s, ContinuousWithinAt f (Set.Ici s) s)
    (hl : ∀ s : ℝ≥0, 0 < s → ∃ l, Tendsto f (𝓝[<] s) (𝓝 l)) (t : ℝ≥0) :
    ContinuousWithinAt (fun t => sSup (f '' Set.Icc 0 t)) (Set.Ici t) t := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 (hr t) (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun {u} hu hdist => ?_⟩
  have hu' : t ≤ u := hu
  have hmono : sSup (f '' Set.Icc 0 t) ≤ sSup (f '' Set.Icc 0 u) := supIcc_mono f hr hl hu'
  have hup : sSup (f '' Set.Icc 0 u) ≤ sSup (f '' Set.Icc 0 t) + ε / 2 := by
    apply csSup_le (supIcc_nonempty f u)
    rintro _ ⟨v, hv, rfl⟩
    by_cases hvt : v ≤ t
    · have := le_supIcc f hr hl hvt
      linarith
    · replace hvt := not_le.mp hvt
      have hd : dist v t < δ := by
        rw [NNReal.dist_eq] at hdist ⊢
        have h1 : ((t : ℝ)) ≤ v := by exact_mod_cast hvt.le
        have h2 : ((v : ℝ)) ≤ u := by exact_mod_cast hv.2
        rw [abs_of_nonneg (by linarith)]
        rw [abs_of_nonneg (by linarith)] at hdist
        linarith
      have := hδ' (show v ∈ Set.Ici t from hvt.le) hd
      rw [Real.dist_eq, abs_lt] at this
      have := le_supIcc f hr hl (le_refl t)
      linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- A right-continuous function on `ℝ≥0`, read on `ℝ` through `toNNReal`, is measurable. -/
lemma measurable_of_rightCont (F : ℝ≥0 → ℝ) (hr : ∀ s, ContinuousWithinAt F (Set.Ici s) s) :
    Measurable (fun u : ℝ => F u.toNNReal) := by
  let c : ℕ → ℕ → ℝ≥0 := fun n k => (k : ℝ≥0) / 2 ^ n
  let G : ℕ → ℝ → ℝ := fun n u => F (c n ⌈u.toNNReal * 2 ^ n⌉₊)
  have hG : ∀ n, Measurable (G n) := by
    intro n
    have h1 : Measurable (fun u : ℝ => ⌈u.toNNReal * 2 ^ n⌉₊) :=
      ((measurable_real_toNNReal).mul_const _).nat_ceil
    exact (measurable_from_nat (f := fun k => F (c n k))).comp h1
  refine measurable_of_tendsto_metrizable hG ?_
  rw [tendsto_pi_nhds]
  intro u
  set v := u.toNNReal
  have hlim : Tendsto (fun n => c n ⌈v * 2 ^ n⌉₊) atTop (𝓝[≥] v) := by
    have hge : ∀ n, v ≤ c n ⌈v * 2 ^ n⌉₊ := by
      intro n
      simp only [c]
      rw [le_div_iff₀ (by positivity)]
      exact Nat.le_ceil _
    have hle : ∀ n, c n ⌈v * 2 ^ n⌉₊ ≤ v + 1 / 2 ^ n := by
      intro n
      simp only [c]
      rw [div_le_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity)]
      exact (Nat.ceil_lt_add_one (by positivity)).le
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall hge⟩
    have h0 : Tendsto (fun n : ℕ => v + 1 / (2 : ℝ≥0) ^ n) atTop (𝓝 (v + 0)) := by
      refine tendsto_const_nhds.add ?_
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    rw [add_zero] at h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 hge hle
  exact (hr v).tendsto.comp hlim

end Avram2004.Canadized.PathCR

namespace Avram2004.Canadized.AV2

lemma path_rc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (x : ℝ) (ω : Ω) :
    ∀ s, ContinuousWithinAt (fun u => x + X u ω) (Set.Ici s) s :=
  fun s => continuousWithinAt_const.add (hX.right_continuous ω s)

lemma path_ll {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (x : ℝ) (ω : Ω) :
    ∀ s : ℝ≥0, 0 < s → ∃ l, Tendsto (fun u => x + X u ω) (𝓝[<] s) (𝓝 l) := by
  intro s hs
  obtain ⟨l, hl⟩ := hX.left_limits ω s hs
  exact ⟨x + l, tendsto_const_nhds.add hl⟩

lemma refl_nonneg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (s0 x : ℝ) (ω : Ω) (t : ℝ≥0) : 0 ≤ Shared.refl s0 x X t ω := by
  unfold Shared.refl Shared.runMax
  have h1 := PathCR.le_supIcc _ (path_rc hX x ω) (path_ll hX x ω) (le_refl t)
  have h2 := le_max_right s0 (sSup ((fun u => x + X u ω) '' Set.Icc 0 t))
  linarith

lemma refl_rc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (s0 x : ℝ) (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (fun t => Shared.refl s0 x X t ω) (Set.Ici t) t := by
  unfold Shared.refl Shared.runMax
  exact (continuousWithinAt_const.max
    (PathCR.supIcc_rightCont _ (path_rc hX x ω) (path_ll hX x ω) t)).sub (path_rc hX x ω t)


lemma integrand_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (s0 x : ℝ) (ω : Ω) (a : ℝ) :
    Measurable (fun u : ℝ => Real.exp (-a * u + Shared.refl s0 x X u.toNNReal ω)) := by
  have hm := PathCR.measurable_of_rightCont _ (refl_rc hX s0 x ω)
  exact Real.measurable_exp.comp ((measurable_const.mul measurable_id).add hm)


lemma payoffAt_some {Ω : Type*} (a : ℝ) (Y : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) (ω : Ω)
    (T : ℝ≥0) (hT : τ ω = (T : WithTop ℝ≥0)) :
    payoffAt a Y τ ω = ENNReal.ofReal (Real.exp (-a * (T : ℝ) + Y T ω)) := by
  unfold payoffAt
  rw [hT]

end Avram2004.Canadized.AV2

namespace Avram2004.Canadized.AV1

/-- countable dense set of times in `[0, q]` (rational times plus `q`). -/
def Dq (q : ℝ≥0) : Set ℝ≥0 := {q} ∪ {r | r ≤ q ∧ ∃ x : ℚ, (r : ℝ) = x}

lemma Dq_countable (q : ℝ≥0) : (Dq q).Countable := by
  refine (Set.countable_singleton q).union ?_
  refine ((Set.countable_range (fun x : ℚ => (x : ℝ).toNNReal))).mono ?_
  rintro r ⟨-, x, hx⟩
  exact ⟨x, show (x : ℝ).toNNReal = r by rw [← hx, Real.toNNReal_coe]⟩

lemma Dq_sub (q : ℝ≥0) : Dq q ⊆ Set.Icc 0 q := by
  rintro r (hr | ⟨hr, -⟩)
  · rw [Set.mem_singleton_iff.1 hr]; exact ⟨zero_le, le_rfl⟩
  · exact ⟨zero_le, hr⟩

/-- rational times between `u < q` arbitrarily close to `u` from the right -/
lemma exists_Dq_near (q u : ℝ≥0) (huq : u < q) (δ : ℝ) (hδ : 0 < δ) :
    ∃ r ∈ Dq q, u < r ∧ (r : ℝ) < u + δ := by
  have h1 : (u : ℝ) < min (q : ℝ) (u + δ) := lt_min (by exact_mod_cast huq) (by linarith)
  obtain ⟨x, hx1, hx2⟩ := exists_rat_btwn h1
  have hx0 : (0 : ℝ) ≤ x := le_trans u.coe_nonneg hx1.le
  refine ⟨(x : ℝ).toNNReal, Or.inr ⟨?_, x, Real.coe_toNNReal _ hx0⟩, ?_, ?_⟩
  · rw [Real.toNNReal_le_iff_le_coe]; exact (hx2.trans_le (min_le_left _ _)).le
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hx0]; exact hx1
  · rw [Real.coe_toNNReal _ hx0]; exact hx2.trans_le (min_le_right _ _)

lemma sup_eq_Dq (g : ℝ≥0 → ℝ) (hr : ∀ s, ContinuousWithinAt g (Set.Ici s) s)
    (hl : ∀ s : ℝ≥0, 0 < s → ∃ l, Tendsto g (𝓝[<] s) (𝓝 l)) (q : ℝ≥0) :
    sSup (g '' Set.Icc 0 q) = sSup (g '' Dq q) := by
  have hbdd := PathCR.cadlag_bddAbove g hr hl q
  have hne : (g '' Dq q).Nonempty := ⟨g q, q, Or.inl rfl, rfl⟩
  have hbdd' : BddAbove (g '' Dq q) := hbdd.mono (Set.image_mono (Dq_sub q))
  apply le_antisymm
  · apply csSup_le (PathCR.supIcc_nonempty g q)
    rintro _ ⟨u, hu, rfl⟩
    rcases eq_or_lt_of_le hu.2 with huq | huq
    · rw [huq]; exact le_csSup hbdd' ⟨q, Or.inl rfl, rfl⟩
    · apply le_of_forall_pos_lt_add
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 (hr u) ε hε
      obtain ⟨r, hrD, hur, hrδ⟩ := exists_Dq_near q u huq δ hδ
      have hd : dist r u < δ := by
        rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hur.le))]
        linarith
      have := hδ' (show r ∈ Set.Ici u from hur.le) hd
      rw [Real.dist_eq, abs_lt] at this
      have := le_csSup hbdd' ⟨r, hrD, rfl⟩
      linarith
  · exact csSup_le_csSup hbdd hne (Set.image_mono (Dq_sub q))

lemma measurable_sup {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m) (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X) (x : ℝ) (q : ℝ≥0) :
    Measurable[𝓕 q] (fun ω => sSup ((fun u => x + X u ω) '' Set.Icc 0 q)) := by
  have hL := hX.isSNLevy
  have heq : (fun ω => sSup ((fun u => x + X u ω) '' Set.Icc 0 q)) =
      fun ω => ⨆ d : Dq q, x + X d ω := by
    funext ω
    rw [sup_eq_Dq _ (AV2.path_rc hL x ω) (AV2.path_ll hL x ω) q, Set.image_eq_range]
    rfl
  rw [heq]
  have : Countable (Dq q) := (Dq_countable q).to_subtype
  refine Measurable.iSup fun d => ?_
  have hd : (d : ℝ≥0) ≤ q := (Dq_sub q d.2).2
  exact measurable_const.add ((hX.adapted d).mono (𝓕.mono hd) le_rfl)

lemma measurable_refl {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m) (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X) (s0 x : ℝ) (q : ℝ≥0) :
    Measurable[𝓕 q] (fun ω => Shared.refl s0 x X q ω) := by
  unfold Shared.refl Shared.runMax
  exact (measurable_const.max (measurable_sup 𝓕 P X hX x q)).sub
    (measurable_const.add (hX.adapted q))

end Avram2004.Canadized.AV1

namespace Avram2004.Canadized.ETA

lemma measurable_eval {β : Type*} [MeasurableSpace β] (Z : ℝ≥0 → β → ℝ)
    (hZm : ∀ t, Measurable (Z t))
    (hrc : ∀ b t, ContinuousWithinAt (fun t => Z t b) (Set.Ici t) t)
    (T : β → ℝ≥0) (hT : Measurable T) : Measurable (fun b => Z (T b) b) := by
  let c : ℕ → ℕ → ℝ≥0 := fun n k => (k : ℝ≥0) / 2 ^ n
  let G : ℕ → β → ℝ := fun n b => Z (c n ⌈T b * 2 ^ n⌉₊) b
  have key : ∀ n (k : β → ℕ), Measurable k → Measurable (fun b => Z (c n (k b)) b) := by
    intro n k hk
    have h2 : Measurable (fun p : β × ℕ => Z (c n p.2) p.1) :=
      measurable_from_prod_countable_left (fun j => hZm (c n j))
    exact Measurable.comp (g := fun p : β × ℕ => Z (c n p.2) p.1) (f := fun b => (b, k b)) h2
      (measurable_id'.prodMk hk)
  have hG : ∀ n, Measurable (G n) := fun n =>
    key n (fun b => ⌈T b * 2 ^ n⌉₊) ((hT.mul_const _).nat_ceil)
  refine measurable_of_tendsto_metrizable hG ?_
  rw [tendsto_pi_nhds]
  intro b
  set v := T b
  have hlim : Tendsto (fun n => c n ⌈v * 2 ^ n⌉₊) atTop (𝓝[≥] v) := by
    have hge : ∀ n, v ≤ c n ⌈v * 2 ^ n⌉₊ := by
      intro n
      simp only [c]
      rw [le_div_iff₀ (by positivity)]
      exact Nat.le_ceil _
    have hle : ∀ n, c n ⌈v * 2 ^ n⌉₊ ≤ v + 1 / 2 ^ n := by
      intro n
      simp only [c]
      rw [div_le_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity)]
      exact (Nat.ceil_lt_add_one (by positivity)).le
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall hge⟩
    have h0 : Tendsto (fun n : ℕ => v + 1 / (2 : ℝ≥0) ^ n) atTop (𝓝 (v + 0)) := by
      refine tendsto_const_nhds.add ?_
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    rw [add_zero] at h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 hge hle
  exact (hrc b v).tendsto.comp hlim

lemma stopAt_top (t : ℝ≥0) : Shared.stopAt t ⊤ = t := rfl

lemma stopAt_coe (t r : ℝ≥0) : Shared.stopAt t (r : WithTop ℝ≥0) = min t r := rfl

lemma measurable_stopAt {Ω : Type*} [MeasurableSpace Ω] (τ : Ω → WithTop ℝ≥0)
    (hτ : ∀ c : ℝ≥0, MeasurableSet {ω | τ ω ≤ c}) :
    Measurable (fun q : Ω × ℝ => Shared.stopAt q.2.toNNReal (τ q.1)) := by
  refine measurable_of_Iic fun c => ?_
  have hset : (fun q : Ω × ℝ => Shared.stopAt q.2.toNNReal (τ q.1)) ⁻¹' Set.Iic c =
      {q : Ω × ℝ | q.2.toNNReal ≤ c} ∪ Prod.fst ⁻¹' {ω | τ ω ≤ c} := by
    ext ⟨ω, s⟩
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_setOf_eq]
    cases h : τ ω with
    | top =>
      have : ¬ ((⊤ : WithTop ℝ≥0) ≤ (c : WithTop ℝ≥0)) := by
        intro hc
        exact (WithTop.coe_lt_top c).not_ge hc
      simp only [this, or_false]
      rfl
    | coe r =>
      have : ((r : WithTop ℝ≥0) ≤ (c : WithTop ℝ≥0)) ↔ r ≤ c := WithTop.coe_le_coe
      rw [this]
      exact min_le_iff
  rw [hset]
  exact (measurableSet_le (measurable_real_toNNReal.comp measurable_snd) measurable_const).union
    (measurable_fst (hτ c))

/-- the clock-free integrand `e^{-α (s ∧ τ) + Y_{s ∧ τ}}` as a function of `(ω, s)` -/
noncomputable def Fint {Ω : Type*} (α : ℝ) (Y : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0)
    (q : Ω × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-α * (Shared.stopAt q.2.toNNReal (τ q.1) : ℝ)
    + Y (Shared.stopAt q.2.toNNReal (τ q.1)) q.1))

lemma measurable_Fint {Ω : Type*} [MeasurableSpace Ω] (α : ℝ) (Y : ℝ≥0 → Ω → ℝ)
    (hYm : ∀ t, Measurable (Y t))
    (hrc : ∀ ω t, ContinuousWithinAt (fun t => Y t ω) (Set.Ici t) t)
    (τ : Ω → WithTop ℝ≥0) (hτ : ∀ c : ℝ≥0, MeasurableSet {ω | τ ω ≤ c}) :
    Measurable (Fint α Y τ) := by
  have hT := measurable_stopAt τ hτ
  have hZ := measurable_eval (fun t (q : Ω × ℝ) => Y t q.1) (fun t => (hYm t).comp measurable_fst)
    (fun q t => hrc q.1 t) _ hT
  unfold Fint
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((measurable_const.mul (measurable_coe_nnreal_real.comp hT)).add hZ))

lemma crPayoff_eq {Ω : Type*} (α z : ℝ) (X : ℝ≥0 → Ω → ℝ) (η : Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    crPayoff α z X η τ ω = Fint α (Shared.refl 0 (-z) X) τ (ω, η ω) := by
  unfold crPayoff Fint
  have hm : minTime τ η ω =
      ((Shared.stopAt (η ω).toNNReal (τ ω) : ℝ≥0) : WithTop ℝ≥0) := by
    unfold minTime
    cases h : τ ω with
    | top => exact min_eq_right le_top
    | coe r =>
      show min ((r : WithTop ℝ≥0)) (((η ω).toNNReal : ℝ≥0) : WithTop ℝ≥0) =
        ((min (η ω).toNNReal r : ℝ≥0) : WithTop ℝ≥0)
      rw [← WithTop.coe_min, min_comm]
  unfold payoffAt
  rw [hm]

lemma indep_fubini {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (f : Ω → Ω') (η : Ω → ℝ) (hf : Measurable f) (hη : Measurable η)
    (hind : IndepFun f η Q) (F : Ω' × ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, F (f ω, η ω) ∂Q = ∫⁻ ω, ∫⁻ s, F (f ω, s) ∂(Q.map η) ∂Q := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hη.aemeasurable] at hind
  calc ∫⁻ ω, F (f ω, η ω) ∂Q = ∫⁻ q, F q ∂(Q.map (fun ω => (f ω, η ω))) :=
        (lintegral_map hF (hf.prodMk hη)).symm
    _ = ∫⁻ q, F q ∂((Q.map f).prod (Q.map η)) := by rw [hind]
    _ = ∫⁻ x, ∫⁻ s, F (x, s) ∂(Q.map η) ∂(Q.map f) := lintegral_prod _ hF.aemeasurable
    _ = ∫⁻ ω, ∫⁻ s, F (f ω, s) ∂(Q.map η) ∂Q := lintegral_map hF.lintegral_prod_right' hf

lemma pdf_mul (lam α : ℝ) (hlam : 0 < lam) (s y : ℝ) (hs : 0 ≤ s) :
    exponentialPDF lam s * ENNReal.ofReal (Real.exp (-α * s + y)) =
      ENNReal.ofReal lam * ENNReal.ofReal (Real.exp (-(α + lam) * s + y)) := by
  rw [exponentialPDF_of_nonneg hs, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul hlam.le]
  congr 1
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma tail_eq (lam t0 : ℝ) (hlam : 0 < lam) (ht0 : 0 ≤ t0) :
    ∫⁻ s in Set.Ici t0, exponentialPDF lam s = ENNReal.ofReal (Real.exp (-(lam * t0))) := by
  have h1 := lintegral_add_compl (μ := volume) (fun s => exponentialPDF lam s) (measurableSet_Ici (a := t0))
  rw [Set.compl_Ici, lintegral_exponentialPDF_eq_one hlam] at h1
  have h2 : ∫⁻ s in Set.Iio t0, exponentialPDF lam s =
      ENNReal.ofReal (1 - Real.exp (-(lam * t0))) := by
    rw [setLIntegral_congr Iio_ae_eq_Iic, lintegral_exponentialPDF_eq_antiDeriv hlam, if_pos ht0]
  rw [h2] at h1
  have hle : Real.exp (-(lam * t0)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hlam.le ht0))
  rw [ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top h1, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ (sub_nonneg.2 hle)]
  congr 1
  ring

lemma runIntegral_top {Ω : Type*} (a : ℝ) (Y : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) (ω : Ω)
    (h : τ ω = ⊤) :
    runIntegral a Y τ ω = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-a * t + Y t.toNNReal ω)) := by
  unfold runIntegral
  congr 2
  ext t
  rw [h]
  exact ⟨fun h1 => h1.1, fun h1 => ⟨h1, le_top⟩⟩

lemma runIntegral_coe {Ω : Type*} (a : ℝ) (Y : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) (ω : Ω)
    (T : ℝ≥0) (h : τ ω = (T : WithTop ℝ≥0)) :
    runIntegral a Y τ ω = ∫⁻ t in Set.Ioc (0 : ℝ) T, ENNReal.ofReal (Real.exp (-a * t + Y t.toNNReal ω)) := by
  unfold runIntegral
  congr 2
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_Ioc, h, WithTop.coe_le_coe]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨h0, Real.toNNReal_le_iff_le_coe.1 h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨h0, Real.toNNReal_le_iff_le_coe.2 h1⟩

lemma inner_eq {Ω : Type*} (α lam : ℝ) (hlam : 0 < lam) (Y : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω)
    (hrc : ∀ t, ContinuousWithinAt (fun t => Y t ω) (Set.Ici t) t) :
    ∫⁻ s, Fint α Y τ (ω, s) ∂(expMeasure lam) =
      payoffAt (α + lam) Y τ ω + ENNReal.ofReal lam * runIntegral (α + lam) Y τ ω := by
  set E : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (-(α + lam) * s + Y s.toNNReal ω)) with hEdef
  have hE : Measurable E := by
    have hm := PathCR.measurable_of_rightCont _ hrc
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_const.mul measurable_id).add hm))
  have hpdf : Measurable (exponentialPDF lam) :=
    (measurable_exponentialPDFReal lam).ennreal_ofReal
  rw [show expMeasure lam = volume.withDensity (exponentialPDF lam) from rfl,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hpdf
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  cases h : τ ω with
  | top =>
    have hpt : ∀ s, (exponentialPDF lam * fun s => Fint α Y τ (ω, s)) s =
        (Set.Ici 0).indicator (fun s => ENNReal.ofReal lam * E s) s := by
      intro s
      simp only [Pi.mul_apply]
      by_cases hs : s < 0
      · rw [exponentialPDF_of_neg hs, zero_mul, Set.indicator_of_notMem (by simpa using hs)]
      · replace hs := not_lt.1 hs
        rw [Set.indicator_of_mem (show s ∈ Set.Ici 0 from hs)]
        simp only [Fint, h]
        rw [show Shared.stopAt s.toNNReal ⊤ = s.toNNReal from rfl, Real.coe_toNNReal _ hs]
        exact pdf_mul lam α hlam s _ hs
    rw [lintegral_congr hpt, lintegral_indicator measurableSet_Ici, lintegral_const_mul _ hE,
      runIntegral_top _ _ _ _ h, setLIntegral_congr Ioi_ae_eq_Ici.symm]
    have hp : payoffAt (α + lam) Y τ ω = 0 := by
      unfold payoffAt; rw [h]
    rw [hp, zero_add]
  | coe T0 =>
    have hC := AV2.payoffAt_some (α + lam) Y τ ω T0 h
    set t0 : ℝ := (T0 : ℝ) with ht0
    set C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-α * t0 + Y T0 ω)) with hCdef
    have hpt : ∀ s, (exponentialPDF lam * fun s => Fint α Y τ (ω, s)) s =
        (Set.Ico 0 t0).indicator (fun s => ENNReal.ofReal lam * E s) s +
          (Set.Ici t0).indicator (fun s => exponentialPDF lam s * C) s := by
      intro s
      simp only [Pi.mul_apply]
      by_cases hs : s < 0
      · rw [exponentialPDF_of_neg hs, zero_mul,
          Set.indicator_of_notMem (show s ∉ Set.Ico 0 t0 from fun hm => absurd hm.1 (not_le.2 hs)),
          Set.indicator_of_notMem (show s ∉ Set.Ici t0 from fun hm =>
            absurd (le_trans T0.coe_nonneg hm) (not_le.2 hs)), add_zero]
      · replace hs := not_lt.1 hs
        simp only [Fint, h]
        rw [show Shared.stopAt s.toNNReal (T0 : WithTop ℝ≥0) = min s.toNNReal T0 from rfl]
        by_cases hst : s < t0
        · have hmin : min s.toNNReal T0 = s.toNNReal :=
            min_eq_left (Real.toNNReal_le_iff_le_coe.2 hst.le)
          rw [hmin, Real.coe_toNNReal _ hs, Set.indicator_of_mem (show s ∈ Set.Ico 0 t0 from ⟨hs, hst⟩),
            Set.indicator_of_notMem (show s ∉ Set.Ici t0 from fun hm => absurd hm (not_le.2 hst)),
            add_zero]
          exact pdf_mul lam α hlam s _ hs
        · replace hst := not_lt.1 hst
          have hmin : min s.toNNReal T0 = T0 :=
            min_eq_right (Real.le_toNNReal_iff_coe_le hs |>.2 hst)
          rw [hmin, Set.indicator_of_notMem (show s ∉ Set.Ico 0 t0 from fun hm => absurd hm.2 (not_lt.2 hst)),
            Set.indicator_of_mem (show s ∈ Set.Ici t0 from hst), zero_add]
    rw [lintegral_congr hpt, lintegral_add_left ((hE.const_mul (ENNReal.ofReal lam)).indicator measurableSet_Ico),
      lintegral_indicator measurableSet_Ico, lintegral_indicator measurableSet_Ici,
      lintegral_const_mul _ hE, lintegral_mul_const _ hpdf, tail_eq lam t0 hlam T0.coe_nonneg,
      runIntegral_coe _ _ _ _ T0 h, setLIntegral_congr Ico_ae_eq_Ioc, hC]
    have hBC : ENNReal.ofReal (Real.exp (-(lam * t0))) * C =
        ENNReal.ofReal (Real.exp (-(α + lam) * t0 + Y T0 ω)) := by
      rw [hCdef, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    rw [hBC]
    exact add_comm _ _

end Avram2004.Canadized.ETA

open MeasureTheory ProbabilityTheory Filter Topology NNReal ENNReal Avram2004 Avram2004.Canadized in
theorem solution {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hS : Shared.Standing P X) (r : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (α : ℝ) (hα : 0 < α) (η : Ω → ℝ) (lam : ℝ)
    (hη : IsExpClock 𝓕 Q η lam) (p : ℝ) (hp : p = α + lam + r)
    (τ : Ω → WithTop ℝ≥0) (hτ : τ ∈ Admissible 𝓕 Q) (z : ℝ) (hz : 0 ≤ z) :
    ∫⁻ ω, crPayoff α z X η τ ω ∂Q =
      ∫⁻ ω, (payoffAt (α + lam) (Shared.refl 0 (-z) X) τ ω
        + ENNReal.ofReal lam * runIntegral (α + lam) (Shared.refl 0 (-z) X) τ ω) ∂Q := by
  obtain ⟨hlam, hηm, hlaw, hind⟩ := hη
  have hrc : ∀ ω t, ContinuousWithinAt (fun t => Shared.refl 0 (-z) X t ω) (Set.Ici t) t :=
    fun ω t => AV2.refl_rc hX.isSNLevy 0 (-z) ω t
  have hle : (⨆ t, 𝓕 t) ≤ m := iSup_le fun t => 𝓕.le t
  have hYm : ∀ t, Measurable[⨆ t, 𝓕 t] (Shared.refl 0 (-z) X t) := fun t =>
    (AV1.measurable_refl 𝓕 P X hX 0 (-z) t).mono (le_iSup (fun t => 𝓕 t) t) le_rfl
  have hτm : ∀ c : ℝ≥0, MeasurableSet[⨆ t, 𝓕 t] {ω | τ ω ≤ c} := fun c =>
    le_iSup (fun t => 𝓕 t) c _ (hτ.1 c)
  have hFm := @ETA.measurable_Fint Ω (⨆ t, 𝓕 t) α (Shared.refl 0 (-z) X) hYm hrc τ hτm
  have hIF : @IndepFun Ω Ω ℝ m (⨆ t, 𝓕 t) _ id η Q := by
    have h : Indep (MeasurableSpace.comap id (⨆ t, 𝓕 t))
        (MeasurableSpace.comap η (inferInstance : MeasurableSpace ℝ)) Q := by
      rw [MeasurableSpace.comap_id]
      exact hind.symm
    exact h
  have key := @ETA.indep_fubini Ω Ω m (⨆ t, 𝓕 t) Q _ id η (measurable_id'' hle) hηm hIF
    (ETA.Fint α (Shared.refl 0 (-z) X) τ) hFm
  calc ∫⁻ ω, crPayoff α z X η τ ω ∂Q
      = ∫⁻ ω, ETA.Fint α (Shared.refl 0 (-z) X) τ (ω, η ω) ∂Q :=
        lintegral_congr fun ω => ETA.crPayoff_eq α z X η τ ω
    _ = ∫⁻ ω, ∫⁻ s, ETA.Fint α (Shared.refl 0 (-z) X) τ (ω, s) ∂(Q.map η) ∂Q := key
    _ = _ := by
        rw [hlaw]
        exact lintegral_congr fun ω => ETA.inner_eq α lam hlam _ τ ω (hrc ω)
