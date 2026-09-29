-- Prove2me | solution 1 for BanditAlgorithm.linear_exceeds_log_threshold_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T23:25:39.020502+00:00
-- url     : https://prove2.me/submissions/a43be40d-fb96-458b-bcaa-a02d86ebbd41

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_TrackAndStop

/-!
# Measurability of the Track-and-Stop trajectory statistics

Everything Algorithm 21 computes at the end of round `t` is a function of the
first `t` rounds, hence `banditFiltration k t`-measurable.  This file proves that,
for each statistic of `Def_TrackAndStop`, and deduces the two structural clauses
of L&S Lemma 33.7:

* `isBanditStoppingTime_chernoffStoppingTime` — Chernoff's rule really is a
  stopping time of the natural filtration;
* `measurable_chernoffRecommendation` — the recommended arm is measurable with
  respect to the stopping-time σ-algebra `𝓕_τ`.

The only delicate point is that `trajEmpiricalBestArm` is defined through
`Finset.exists_max_image`, i.e. through `Classical.choose`, which carries no
measurability whatsoever.  It is handled in §3: we introduce the *canonical*
(least-index) maximiser `trajArgmax`, which is manifestly measurable, and show
that `trajGLR` — the only consumer of `trajEmpiricalBestArm` — is unchanged when
the canonical maximiser is substituted.  The proof splits on whether the maximum
is attained twice: if it is, both versions of `trajGLR` vanish (the pair term for
the two tied maximisers is `0`), and if it is not, the two maximisers coincide.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. Generic comap measurability -/

/-- `Nat.cast : ℕ → ℝ` is measurable (source σ-algebra is `⊤`). -/
theorem measurable_natCast_real : Measurable (fun n : ℕ ↦ (n : ℝ)) :=
  measurable_from_top


/-- A function that factors through `g` is measurable for the σ-algebra `g`
pulls back. -/
theorem measurable_comap_comp {α β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {g : α → β} {f : β → γ} (hf : Measurable f) :
    Measurable[MeasurableSpace.comap g inferInstance] (fun a ↦ f (g a)) :=
  fun _ hs ↦ ⟨f ⁻¹' _, hf hs, rfl⟩

/-- The coordinate `ω s` is `𝓕_t`-measurable as soon as round `s` is among the
first `t`. -/
theorem measurable_trajCoord {t s : ℕ} (hs : s < t) :
    Measurable[banditFiltration k t] (fun ω : ℕ → Fin k × ℝ ↦ ω s) := by
  have : (fun ω : ℕ → Fin k × ℝ ↦ ω s) =
      (fun h : BanditHistory k t ↦ h ⟨s, hs⟩) ∘ banditTrajPrefix k t := rfl
  rw [this]
  exact measurable_comap_comp (measurable_pi_apply _)

/-- The arm played in round `s` is `𝓕_t`-measurable for `s < t`. -/
theorem measurable_trajArm {t s : ℕ} (hs : s < t) :
    Measurable[banditFiltration k t] (fun ω : ℕ → Fin k × ℝ ↦ (ω s).1) :=
  measurable_fst.comp (measurable_trajCoord hs)

/-- The reward observed in round `s` is `𝓕_t`-measurable for `s < t`. -/
theorem measurable_trajReward {t s : ℕ} (hs : s < t) :
    Measurable[banditFiltration k t] (fun ω : ℕ → Fin k × ℝ ↦ (ω s).2) :=
  measurable_snd.comp (measurable_trajCoord hs)

/-! ## 2. The elementary statistics -/

/-- `T_i(t)` is `𝓕_t`-measurable. -/
theorem measurable_trajPullCount (i : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajPullCount i t) := by
  classical
  -- the count is a finite sum of indicators of `𝓕_t`-measurable events
  have hrw : trajPullCount i t =
      fun ω : ℕ → Fin k × ℝ ↦ ∑ s ∈ Finset.range t, if (ω s).1 = i then 1 else 0 := by
    funext ω
    rw [trajPullCount, Finset.card_filter]
  rw [hrw]
  refine Finset.measurable_sum _ fun s hs ↦ ?_
  have hs' : s < t := Finset.mem_range.mp hs
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurable_trajArm hs') (measurableSet_singleton i)

/-- The running sum of the rewards collected from arm `i` is `𝓕_t`-measurable. -/
theorem measurable_trajRewardSum (i : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t]
      (fun ω : ℕ → Fin k × ℝ ↦
        ∑ s ∈ (Finset.range t).filter fun s ↦ (ω s).1 = i, (ω s).2) := by
  classical
  have hrw : (fun ω : ℕ → Fin k × ℝ ↦
        ∑ s ∈ (Finset.range t).filter fun s ↦ (ω s).1 = i, (ω s).2) =
      fun ω : ℕ → Fin k × ℝ ↦
        ∑ s ∈ Finset.range t, if (ω s).1 = i then (ω s).2 else 0 := by
    funext ω
    rw [Finset.sum_filter]
  rw [hrw]
  refine Finset.measurable_sum _ fun s hs ↦ ?_
  have hs' : s < t := Finset.mem_range.mp hs
  exact Measurable.ite ((measurable_trajArm hs') (measurableSet_singleton i))
    (measurable_trajReward hs') measurable_const

/-- `μ̂_i(t)` is `𝓕_t`-measurable. -/
theorem measurable_trajEmpiricalMean (i : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajEmpiricalMean i t) := by
  have hrw : trajEmpiricalMean i t = fun ω : ℕ → Fin k × ℝ ↦
      (∑ s ∈ (Finset.range t).filter fun s ↦ (ω s).1 = i, (ω s).2) /
        ((trajPullCount i t ω : ℕ) : ℝ) := rfl
  rw [hrw]
  exact (measurable_trajRewardSum i t).div
    (measurable_natCast_real.comp (measurable_trajPullCount i t))

/-- `T_i(t)/t` is `𝓕_t`-measurable. -/
theorem measurable_trajAllocation (i : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajAllocation i t) := by
  have hrw : trajAllocation i t = fun ω : ℕ → Fin k × ℝ ↦
      ((trajPullCount i t ω : ℕ) : ℝ) / (t : ℝ) := rfl
  rw [hrw]
  exact (measurable_natCast_real.comp (measurable_trajPullCount i t)).div measurable_const

/-- The pairwise GLR statistic is `𝓕_t`-measurable. -/
theorem measurable_trajPairGLR (a b : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajPairGLR a b t) := by
  have hrw : trajPairGLR a b t = fun ω : ℕ → Fin k × ℝ ↦
      ((trajPullCount a t ω : ℕ) : ℝ) * ((trajPullCount b t ω : ℕ) : ℝ) /
          (((trajPullCount a t ω : ℕ) : ℝ) + ((trajPullCount b t ω : ℕ) : ℝ)) *
        (trajEmpiricalMean a t ω - trajEmpiricalMean b t ω) ^ 2 / 2 := rfl
  rw [hrw]
  have hTa : Measurable[banditFiltration k t]
      (fun ω : ℕ → Fin k × ℝ ↦ ((trajPullCount a t ω : ℕ) : ℝ)) :=
    measurable_natCast_real.comp (measurable_trajPullCount a t)
  have hTb : Measurable[banditFiltration k t]
      (fun ω : ℕ → Fin k × ℝ ↦ ((trajPullCount b t ω : ℕ) : ℝ)) :=
    measurable_natCast_real.comp (measurable_trajPullCount b t)
  exact ((((hTa.mul hTb).div (hTa.add hTb)).mul
    (((measurable_trajEmpiricalMean a t).sub
      (measurable_trajEmpiricalMean b t)).pow_const 2)).div measurable_const)

/-! ## 3. The canonical maximiser and tie-independence of `Z_t` -/

section Argmax

variable [NeZero k]

/-- The *canonical* empirical best arm: the least index at which the empirical
mean is maximal.  Unlike `trajEmpiricalBestArm`, which is defined through
`Classical.choose`, this one is measurable. -/
noncomputable def trajArgmax (t : ℕ) (ω : ℕ → Fin k × ℝ) : Fin k :=
  ((Finset.univ : Finset (Fin k)).filter fun i ↦
      ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω).min'
    (by
      obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k))
        (fun i ↦ trajEmpiricalMean i t ω) Finset.univ_nonempty
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        fun j ↦ hi j (Finset.mem_univ j)⟩⟩)

theorem trajArgmax_mem_filter (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajArgmax t ω ∈ (Finset.univ : Finset (Fin k)).filter fun i ↦
      ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω :=
  Finset.min'_mem _ _

/-- `trajArgmax` is a maximiser. -/
theorem trajArgmax_spec (t : ℕ) (ω : ℕ → Fin k × ℝ) (j : Fin k) :
    trajEmpiricalMean j t ω ≤ trajEmpiricalMean (trajArgmax t ω) t ω :=
  (Finset.mem_filter.mp (trajArgmax_mem_filter t ω)).2 j

/-- `trajArgmax` is the *least* maximiser. -/
theorem trajArgmax_le (t : ℕ) (ω : ℕ → Fin k × ℝ) {i : Fin k}
    (hi : ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω) :
    trajArgmax t ω ≤ i :=
  Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

/-- The canonical maximiser is measurable: its level sets are cut out by finitely
many inequalities between the (measurable) empirical means. -/
theorem measurable_trajArgmax (t : ℕ) :
    Measurable[banditFiltration k t] (trajArgmax (k := k) t) := by
  classical
  have hle : ∀ a b : Fin k, MeasurableSet[banditFiltration k t]
      {ω : ℕ → Fin k × ℝ | trajEmpiricalMean a t ω ≤ trajEmpiricalMean b t ω} := fun a b ↦
    measurableSet_le (measurable_trajEmpiricalMean a t) (measurable_trajEmpiricalMean b t)
  have hmax : ∀ i : Fin k, MeasurableSet[banditFiltration k t]
      {ω : ℕ → Fin k × ℝ | ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω} := by
    intro i
    have hrw : {ω : ℕ → Fin k × ℝ | ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω}
        = ⋂ j : Fin k,
          {ω : ℕ → Fin k × ℝ | trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω} := by
      ext ω; simp
    rw [hrw]
    exact MeasurableSet.iInter fun j ↦ hle j i
  refine @measurable_to_countable' (Fin k) _ _ _ (banditFiltration k t) _ fun i ↦ ?_
  have hset : (trajArgmax (k := k) t) ⁻¹' {i} =
      {ω : ℕ → Fin k × ℝ | ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω} ∩
        ⋂ j ∈ {j : Fin k | j < i},
          {ω : ℕ → Fin k × ℝ | ∀ l, trajEmpiricalMean l t ω ≤ trajEmpiricalMean j t ω}ᶜ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq, Set.mem_compl_iff]
    constructor
    · rintro rfl
      refine ⟨trajArgmax_spec t ω, fun j hj hjmax ↦ ?_⟩
      exact absurd (trajArgmax_le t ω hjmax) (not_le.mpr hj)
    · rintro ⟨himax, hmin⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hmin _ h (trajArgmax_spec t ω)
      · exact absurd (trajArgmax_le t ω himax) (not_le.mpr h)
  rw [hset]
  refine (hmax i).inter (MeasurableSet.biInter (Set.to_countable _) fun j _ ↦ (hmax j).compl)

end Argmax

end BanditAlgorithm

/-!
# The GLR statistic `Z_t` is tie-independent, and measurable

`trajGLR` is written in terms of `trajEmpiricalBestArm`, which is produced by
`Classical.choose` and therefore carries no measurability.  This file shows that
`trajGLR` does not in fact depend on which maximiser is chosen — replacing
`trajEmpiricalBestArm` by the canonical least-index maximiser `trajArgmax` leaves
it unchanged — and concludes that `trajGLR t` is `banditFiltration k t`-measurable.

The mechanism is the same one L&S use in the proof of Lemma 33.7: if the
empirical maximum is attained twice then `Z_t = 0`, because the pair term for two
tied maximisers vanishes.  So the two candidate values of `Z_t` agree: either the
maximiser is unique, and then both formulas use the same arm, or it is not, and
then both formulas return `0`.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. A generic "measurable finite case split" -/

/-- If `h` is a measurable map into a countable discrete space and each `G a` is
measurable, then so is `ω ↦ G (h ω) ω`. -/
theorem measurable_dep_of_countable {Ω γ ι : Type*} {m : MeasurableSpace Ω}
    [MeasurableSpace γ] [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {h : Ω → ι} (hh : Measurable[m] h) {G : ι → Ω → γ} (hG : ∀ a, Measurable[m] (G a)) :
    Measurable[m] fun ω ↦ G (h ω) ω := by
  intro s hs
  have hrw : (fun ω ↦ G (h ω) ω) ⁻¹' s = ⋃ a : ι, (h ⁻¹' {a} ∩ (G a) ⁻¹' s) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    exact ⟨fun hω ↦ ⟨h ω, rfl, hω⟩, fun ⟨a, ha, hω⟩ ↦ by rw [← ha] at hω; exact hω⟩
  rw [hrw]
  exact MeasurableSet.iUnion fun a ↦ (hh (measurableSet_singleton a)).inter (hG a hs)

/-! ## 2. Tie-independence -/

section Ties

variable [NeZero k]

/-- The GLR statistic computed at an arbitrary reference arm `a`. -/
noncomputable def trajGLRat (a : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) : ℝ≥0∞ :=
  ⨅ j ∈ {j : Fin k | j ≠ a}, ENNReal.ofReal (trajPairGLR a j t ω)

theorem trajGLR_eq_trajGLRat (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajGLR t ω = trajGLRat (trajEmpiricalBestArm t ω) t ω := rfl

/-- The pair term between two arms with equal empirical means vanishes. -/
theorem trajPairGLR_eq_zero_of_mean_eq {a b : Fin k} {t : ℕ} {ω : ℕ → Fin k × ℝ}
    (h : trajEmpiricalMean a t ω = trajEmpiricalMean b t ω) :
    trajPairGLR a b t ω = 0 := by
  simp [trajPairGLR, h]

/-- If the empirical maximum is attained at two distinct arms, the GLR statistic
computed at either of them is `0`. -/
theorem trajGLRat_eq_zero_of_tie {a b : Fin k} {t : ℕ} {ω : ℕ → Fin k × ℝ}
    (hab : a ≠ b) (hmean : trajEmpiricalMean a t ω = trajEmpiricalMean b t ω) :
    trajGLRat a t ω = 0 := by
  refine le_antisymm ?_ bot_le
  refine le_trans (iInf_le_of_le b (iInf_le _ (Ne.symm hab))) (le_of_eq ?_)
  rw [trajPairGLR_eq_zero_of_mean_eq hmean, ENNReal.ofReal_zero]

/-- **Tie-independence.** `Z_t` is unchanged if the arbitrary maximiser produced by
`Classical.choose` is replaced by the canonical least-index maximiser. -/
theorem trajGLR_eq_at_argmax (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajGLR t ω = trajGLRat (trajArgmax t ω) t ω := by
  rw [trajGLR_eq_trajGLRat]
  by_cases h : trajEmpiricalBestArm t ω = trajArgmax t ω
  · rw [h]
  · -- both are maximisers, so their empirical means agree and both sides vanish
    have hmean : trajEmpiricalMean (trajEmpiricalBestArm t ω) t ω
        = trajEmpiricalMean (trajArgmax t ω) t ω :=
      le_antisymm (trajArgmax_spec t ω _) (trajEmpiricalBestArm_spec t ω _)
    rw [trajGLRat_eq_zero_of_tie h hmean, trajGLRat_eq_zero_of_tie (Ne.symm h) hmean.symm]

/-- If the empirical maximum is attained twice, `Z_t = 0`. -/
theorem trajGLR_eq_zero_of_not_unique (t : ℕ) (ω : ℕ → Fin k × ℝ) {b : Fin k}
    (hb : b ≠ trajArgmax t ω) (hmax : ∀ i, trajEmpiricalMean i t ω ≤ trajEmpiricalMean b t ω) :
    trajGLR t ω = 0 := by
  have hmean : trajEmpiricalMean (trajArgmax t ω) t ω = trajEmpiricalMean b t ω :=
    le_antisymm (hmax _) (trajArgmax_spec t ω b)
  rw [trajGLR_eq_at_argmax]
  exact trajGLRat_eq_zero_of_tie (Ne.symm hb) hmean

/-- **Uniqueness from a positive GLR.** If `Z_t ≠ 0` then the empirical maximiser
is unique, so the arbitrary choice made by `trajEmpiricalBestArm` agrees with the
canonical one. -/
theorem trajEmpiricalBestArm_eq_argmax_of_trajGLR_ne_zero (t : ℕ) (ω : ℕ → Fin k × ℝ)
    (h : trajGLR t ω ≠ 0) : trajEmpiricalBestArm t ω = trajArgmax t ω := by
  by_contra hne
  exact h (trajGLR_eq_zero_of_not_unique t ω hne (trajEmpiricalBestArm_spec t ω))

/-! ## 3. Measurability of `Z_t` -/

theorem measurable_trajGLRat (a : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajGLRat a t) := by
  have hrw : trajGLRat a t = fun ω ↦ ⨅ j ∈ {j : Fin k | j ≠ a},
      ENNReal.ofReal (trajPairGLR a j t ω) := rfl
  rw [hrw]
  refine Measurable.iInf fun j ↦ ?_
  refine Measurable.iInf fun _ ↦ ?_
  exact ENNReal.measurable_ofReal.comp (measurable_trajPairGLR a j t)

/-- `Z_t` is `𝓕_t`-measurable. -/
theorem measurable_trajGLR (t : ℕ) :
    Measurable[banditFiltration k t] (trajGLR (k := k) t) := by
  have hrw : trajGLR (k := k) t = fun ω ↦ trajGLRat (trajArgmax t ω) t ω := by
    funext ω; exact trajGLR_eq_at_argmax t ω
  rw [hrw]
  exact measurable_dep_of_countable (measurable_trajArgmax t) fun a ↦ measurable_trajGLRat a t

/-- The event "Chernoff's rule fires in round `t`" is `𝓕_t`-measurable. -/
theorem measurableSet_chernoffFires (δ : ℝ) (t : ℕ) :
    MeasurableSet[banditFiltration k t]
      {ω : ℕ → Fin k × ℝ | ENNReal.ofReal (chernoffThreshold k δ t) ≤ trajGLR t ω} :=
  measurableSet_le measurable_const (measurable_trajGLR t)

end Ties

end BanditAlgorithm

/-!
# Chernoff's stopping rule: threshold arithmetic and the stopping-time property

This file establishes the two *structural* clauses of L&S Lemma 33.7 — everything
about `τ_δ` and `ψ_δ` except the probability bound itself:

* `chernoffInverse_ge`, `chernoffThreshold_pos` — the threshold `β_t(δ)` is
  strictly positive.  This is what forces the empirical maximiser to be unique
  whenever the learner stops, which is in turn what makes the recommendation
  measurable at all (`chernoffRecommendation` is built from the `Classical.choose`
  maximiser `trajEmpiricalBestArm`).
* `isBanditStoppingTime_chernoffStoppingTime` — `τ_δ` is a stopping time of the
  natural filtration.
* `measurable_chernoffRecommendation` — `ψ_δ` is `𝓕_{τ_δ}`-measurable.

The positivity argument is the one implicit in L&S p. 410: `f⁻¹(δ)` is the least
`x ≥ k` with `f(x) ≤ δ`, so `f⁻¹(δ) ≥ k ≥ 1` as soon as that set is nonempty —
which it is, because `f(x) = e^{k-x}(x/k)^k → 0` as `x → ∞`.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter Real

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. The Chernoff function and its inverse -/

/-- `f(k) = 1`. -/
theorem chernoffF_self (hk : 0 < k) : chernoffF k (k : ℝ) = 1 := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  simp [chernoffF, div_self hk']

/-- `f(x) = e^{k-x}(x/k)^k` tends to `0` as `x → ∞`. -/
theorem tendsto_chernoffF (hk : 0 < k) :
    Tendsto (chernoffF k) atTop (nhds 0) := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hrw : chernoffF k = fun x : ℝ ↦
      (Real.exp (k : ℝ) / ((k : ℝ) ^ k)) * (x ^ k * Real.exp (-x)) := by
    funext x
    rw [chernoffF, div_pow, sub_eq_add_neg, Real.exp_add]
    field_simp
  rw [hrw]
  simpa using tendsto_const_nhds.mul (tendsto_pow_mul_exp_neg_atTop_nhds_zero k)

/-- The set defining `f⁻¹(δ)` is nonempty for every `δ > 0`. -/
theorem chernoffInverse_set_nonempty (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ}.Nonempty := by
  have h1 : ∀ᶠ x : ℝ in atTop, chernoffF k x ≤ δ :=
    (tendsto_chernoffF hk).eventually (eventually_le_nhds hδ)
  have h2 : ∀ᶠ x : ℝ in atTop, (k : ℝ) ≤ x := eventually_ge_atTop _
  obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
  exact ⟨x, hx2, hx1⟩

theorem chernoffInverse_set_bddBelow {δ : ℝ} :
    BddBelow {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ} :=
  ⟨(k : ℝ), fun _ hx ↦ hx.1⟩

/-- `f⁻¹(δ) ≥ k`. -/
theorem chernoffInverse_ge (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    (k : ℝ) ≤ chernoffInverse k δ :=
  le_csInf (chernoffInverse_set_nonempty hk hδ) fun _ hx ↦ hx.1

/-- `f⁻¹(δ) > 0`. -/
theorem chernoffInverse_pos (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    0 < chernoffInverse k δ :=
  lt_of_lt_of_le (by exact_mod_cast hk) (chernoffInverse_ge hk hδ)

/-- The threshold `β_t(δ) = k log(t² + t) + f⁻¹(δ)` is strictly positive. -/
theorem chernoffThreshold_pos (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (t : ℕ) :
    0 < chernoffThreshold k δ t := by
  have hlog : 0 ≤ (k : ℝ) * Real.log ((t : ℝ) ^ 2 + (t : ℝ)) := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · norm_num
    · refine mul_nonneg (Nat.cast_nonneg k) (Real.log_nonneg ?_)
      have h1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      nlinarith
  have hinv := chernoffInverse_pos hk hδ
  rw [chernoffThreshold]
  linarith

/-! ## 2. The stopping-time property -/

section Stop

variable [NeZero k]

/-- Unfolding of the stopping rule: the learner has stopped by round `n` exactly
when the firing condition has held at some round `m ≤ n`. -/
theorem chernoffStoppingTime_le_iff (δ : ℝ) (n : ℕ) (ω : ℕ → Fin k × ℝ) :
    chernoffStoppingTime (k := k) δ ω ≤ (n : ℕ∞) ↔
      ∃ m ≤ n, ENNReal.ofReal (chernoffThreshold k δ m) ≤ trajGLR m ω := by
  constructor
  · intro hle
    by_contra hcon
    push_neg at hcon
    -- every element of the defining set exceeds `n`, hence is `≥ n + 1`
    have hlb : ((n : ℕ∞) + 1) ≤ chernoffStoppingTime (k := k) δ ω := by
      refine le_sInf ?_
      rintro t ⟨m, rfl, hm⟩
      have hmn : n < m := by
        by_contra h
        exact absurd hm (not_le.mpr (hcon m (not_lt.mp h)))
      have : ((n + 1 : ℕ) : ℕ∞) ≤ ((m : ℕ) : ℕ∞) := by
        exact_mod_cast Nat.succ_le_of_lt hmn
      simpa using this
    have hcontr : ((n + 1 : ℕ) : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := by
      push_cast
      exact le_trans hlb hle
    exact absurd (by exact_mod_cast hcontr : n + 1 ≤ n) (Nat.not_succ_le_self n)
  · rintro ⟨m, hmn, hm⟩
    refine le_trans (sInf_le ⟨m, rfl, hm⟩) ?_
    exact_mod_cast hmn

/-- **Chernoff's rule is a stopping time.** -/
theorem isBanditStoppingTime_chernoffStoppingTime (δ : ℝ) :
    IsBanditStoppingTime (chernoffStoppingTime (k := k) δ) := by
  intro n
  show MeasurableSet[banditFiltration k n]
    {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω ≤ ((n : ℕ) : ℕ∞)}
  have hrw : {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω ≤ ((n : ℕ) : ℕ∞)} =
      ⋃ m ∈ Finset.range (n + 1),
        {ω : ℕ → Fin k × ℝ | ENNReal.ofReal (chernoffThreshold k δ m) ≤ trajGLR m ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff, exists_prop]
    exact chernoffStoppingTime_le_iff δ n ω
  rw [hrw]
  refine MeasurableSet.biUnion (Set.to_countable _) fun m hm ↦ ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  exact (banditFiltration k).mono hmn _ (measurableSet_chernoffFires δ m)

/-- `{τ_δ = m}` is `𝓕_m`-measurable. -/
theorem measurableSet_chernoffStoppingTime_eq (δ : ℝ) (m : ℕ) :
    MeasurableSet[banditFiltration k m]
      {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω = ((m : ℕ) : ℕ∞)} := by
  have hτ := isBanditStoppingTime_chernoffStoppingTime (k := k) δ
  have hset : {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω = ((m : ℕ) : ℕ∞)} =
      {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω ≤ ((m : ℕ) : ℕ∞)} \
        ⋃ l ∈ Finset.range m,
          {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω ≤ ((l : ℕ) : ℕ∞)} := by
    ext ω
    simp only [Set.mem_diff, Set.mem_iUnion, Finset.mem_range, Set.mem_setOf_eq,
      exists_prop, not_exists, not_and]
    constructor
    · rintro h
      refine ⟨le_of_eq h, fun l hl hle ↦ ?_⟩
      rw [h] at hle
      exact absurd (by exact_mod_cast hle : m ≤ l) (not_le.mpr hl)
    · rintro ⟨hle, hlt⟩
      rcases lt_or_eq_of_le hle with h | h
      · exfalso
        obtain ⟨l, hl⟩ : ∃ l : ℕ, ((l : ℕ) : ℕ∞) = chernoffStoppingTime (k := k) δ ω :=
          ENat.ne_top_iff_exists.mp fun htop ↦ by
            rw [htop] at hle; exact absurd hle (by simp)
        rw [← hl] at h
        exact hlt l (by exact_mod_cast h) (le_of_eq hl.symm)
      · exact h
  rw [hset]
  refine MeasurableSet.diff (hτ m) ?_
  refine MeasurableSet.biUnion (Set.to_countable _) fun l hl ↦ ?_
  exact (banditFiltration k).mono (le_of_lt (Finset.mem_range.mp hl)) _ (hτ l)

/-- `τ_δ` is measurable for the ambient σ-algebra. -/
theorem measurable_chernoffStoppingTime (δ : ℝ) :
    Measurable (chernoffStoppingTime (k := k) δ) := by
  have hτ := isBanditStoppingTime_chernoffStoppingTime (k := k) δ
  refine @measurable_to_countable' ℕ∞ _ _ _ _ _ fun c ↦ ?_
  rcases eq_or_ne c ⊤ with rfl | hc
  · have hrw : (chernoffStoppingTime (k := k) δ) ⁻¹' {(⊤ : ℕ∞)} =
        (⋃ n : ℕ, {ω : ℕ → Fin k × ℝ |
          chernoffStoppingTime (k := k) δ ω ≤ ((n : ℕ) : ℕ∞)})ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
        Set.mem_setOf_eq, not_exists, not_le]
      constructor
      · intro h n; rw [h]; exact ENat.coe_lt_top n
      · intro h
        by_contra hne
        obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
        rw [← hn] at h
        exact absurd (h n) (lt_irrefl _)
    rw [hrw]
    exact (MeasurableSet.iUnion fun n ↦ (banditFiltration k).le n _ (hτ n)).compl
  · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hc
    have hrw : (chernoffStoppingTime (k := k) δ) ⁻¹' {((m : ℕ) : ℕ∞)} =
        {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω = ((m : ℕ) : ℕ∞)} := rfl
    rw [hrw]
    exact (banditFiltration k).le m _ (measurableSet_chernoffStoppingTime_eq δ m)

/-! ## 3. Measurability of the recommendation -/

/-- If the learner stops in round `n`, the firing condition holds in round `n`
(it holds at some `m ≤ n` by definition, and `n` is the least such `m`). -/
theorem chernoffStoppingTime_fires {δ : ℝ} {n : ℕ} {ω : ℕ → Fin k × ℝ}
    (hn : chernoffStoppingTime (k := k) δ ω = ((n : ℕ) : ℕ∞)) :
    ENNReal.ofReal (chernoffThreshold k δ n) ≤ trajGLR n ω := by
  obtain ⟨m, hmn, hm⟩ := (chernoffStoppingTime_le_iff δ n ω).mp (le_of_eq hn)
  have hnm : ((n : ℕ) : ℕ∞) ≤ ((m : ℕ) : ℕ∞) := hn ▸ sInf_le ⟨m, rfl, hm⟩
  have hnm' : n = m := le_antisymm (by exact_mod_cast hnm) hmn
  exact hnm' ▸ hm

/-- On the event that the learner stops in round `n`, the empirical maximiser is
unique, so the recommendation is the canonical maximiser. -/
theorem chernoffRecommendation_eq_argmax (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} {ω : ℕ → Fin k × ℝ} (hn : chernoffStoppingTime (k := k) δ ω = ((n : ℕ) : ℕ∞)) :
    chernoffRecommendation (k := k) δ ω = trajArgmax n ω := by
  have hfire : ENNReal.ofReal (chernoffThreshold k δ n) ≤ trajGLR n ω :=
    chernoffStoppingTime_fires hn
  have hpos : trajGLR n ω ≠ 0 := by
    intro h0
    rw [h0, le_zero_iff, ENNReal.ofReal_eq_zero] at hfire
    exact absurd hfire (not_le.mpr (chernoffThreshold_pos hk hδ n))
  have hrec : chernoffRecommendation (k := k) δ ω = trajEmpiricalBestArm n ω := by
    rw [chernoffRecommendation, hn]
  rw [hrec, trajEmpiricalBestArm_eq_argmax_of_trajGLR_ne_zero n ω hpos]

omit [NeZero k] in
/-- `Exists.choose` depends only on the proposition, so a maximiser chosen from
equal data is the same arm. -/
theorem exists_max_image_choose_congr {f g : Fin k → ℝ} (h : f = g)
    (hf : ∃ x ∈ (Finset.univ : Finset (Fin k)),
      ∀ x' ∈ (Finset.univ : Finset (Fin k)), f x' ≤ f x)
    (hg : ∃ x ∈ (Finset.univ : Finset (Fin k)),
      ∀ x' ∈ (Finset.univ : Finset (Fin k)), g x' ≤ g x) :
    hf.choose = hg.choose := by
  subst h; rfl

/-- Two trajectories with the same empirical means at time `t` produce the same
(arbitrarily chosen) empirical best arm. -/
theorem trajEmpiricalBestArm_congr {t t' : ℕ} {ω ω' : ℕ → Fin k × ℝ}
    (h : (fun i : Fin k ↦ trajEmpiricalMean i t ω)
      = fun i : Fin k ↦ trajEmpiricalMean i t' ω') :
    trajEmpiricalBestArm t ω = trajEmpiricalBestArm t' ω' :=
  exists_max_image_choose_congr h _ _

/-- At time `0` all empirical means are the junk value `0`, so the fallback
recommendation is a constant. -/
theorem trajEmpiricalBestArm_zero_const (ω ω' : ℕ → Fin k × ℝ) :
    trajEmpiricalBestArm (k := k) 0 ω = trajEmpiricalBestArm (k := k) 0 ω' := by
  refine trajEmpiricalBestArm_congr ?_
  funext i
  simp [trajEmpiricalMean, trajPullCount]

/-- **The recommendation is `𝓕_τ`-measurable.** -/
theorem measurable_chernoffRecommendation (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    Measurable[(isBanditStoppingTime_chernoffStoppingTime (k := k) δ).measurableSpace]
      (chernoffRecommendation (k := k) δ) := by
  classical
  have hτ := isBanditStoppingTime_chernoffStoppingTime (k := k) δ
  have hτm : Measurable[⨆ t, (banditFiltration k t : MeasurableSpace (ℕ → Fin k × ℝ))]
      (chernoffStoppingTime (k := k) δ) := by
    refine @measurable_to_countable' ℕ∞ _ _ _
      (⨆ t, (banditFiltration k t : MeasurableSpace (ℕ → Fin k × ℝ))) _ fun c ↦ ?_
    cases c with
    | top => exact IsStoppingTime.measurableSet_eq_top' hτ
    | coe n =>
      exact IsStoppingTime.measurableSpace_le' hτ _
        (IsStoppingTime.measurableSet_eq_of_countable' hτ n)
  -- measurability with respect to the σ-algebra generated by the filtration
  have hamb : Measurable[⨆ t, (banditFiltration k t : MeasurableSpace (ℕ → Fin k × ℝ))]
      (chernoffRecommendation (k := k) δ) := by
    refine @measurable_to_countable' (Fin k) _ _ _
      (⨆ t, (banditFiltration k t : MeasurableSpace (ℕ → Fin k × ℝ))) _ fun a ↦ ?_
    have hrw : (chernoffRecommendation (k := k) δ) ⁻¹' {a} =
        (⋃ n : ℕ, {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω = ((n : ℕ) : ℕ∞)} ∩
            {ω : ℕ → Fin k × ℝ | trajArgmax n ω = a}) ∪
          ({ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω = ⊤} ∩
            {ω : ℕ → Fin k × ℝ | trajEmpiricalBestArm (k := k) 0 ω = a}) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_iUnion,
        Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro hω
        rcases eq_or_ne (chernoffStoppingTime (k := k) δ ω) ⊤ with htop | hne
        · refine Or.inr ⟨htop, ?_⟩
          rw [← hω, chernoffRecommendation, htop]
          rfl
        · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
          exact Or.inl ⟨n, hn.symm, by rw [← hω, chernoffRecommendation_eq_argmax hk hδ hn.symm]⟩
      · rintro (⟨n, hn, ha⟩ | ⟨hn, ha⟩)
        · rw [chernoffRecommendation_eq_argmax hk hδ hn, ha]
        · rw [chernoffRecommendation, hn]
          exact ha
    rw [hrw]
    refine MeasurableSet.union (MeasurableSet.iUnion fun n ↦ ?_) ?_
    · exact (hτm (measurableSet_singleton _)).inter
        (le_iSup (fun t ↦ (banditFiltration k t : MeasurableSpace (ℕ → Fin k × ℝ))) n _
          ((measurable_trajArgmax n) (measurableSet_singleton a)))
    · rcases isEmpty_or_nonempty (ℕ → Fin k × ℝ) with _ | ⟨⟨ω₀⟩⟩
      · exact @Subsingleton.measurableSet _ _ _ _
      · by_cases hval : trajEmpiricalBestArm (k := k) 0 ω₀ = a
        · have h : {ω : ℕ → Fin k × ℝ | trajEmpiricalBestArm (k := k) 0 ω = a} = Set.univ := by
            ext ω; simp [trajEmpiricalBestArm_zero_const ω ω₀, hval]
          rw [h, Set.inter_univ]
          exact hτm (measurableSet_singleton _)
        · have h : {ω : ℕ → Fin k × ℝ | trajEmpiricalBestArm (k := k) 0 ω = a} = ∅ := by
            ext ω; simp [trajEmpiricalBestArm_zero_const ω ω₀, hval]
          rw [h, Set.inter_empty]
          exact MeasurableSpace.measurableSet_empty _
  refine @measurable_to_countable' (Fin k) _ _ _ hτ.measurableSpace _ fun i ↦ ?_
  refine ⟨hamb (measurableSet_singleton i), fun n ↦ ?_⟩
  show MeasurableSet[banditFiltration k n]
    ((chernoffRecommendation (k := k) δ) ⁻¹' {i} ∩
      {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω ≤ ((n : ℕ) : ℕ∞)})
  have hrw : (chernoffRecommendation (k := k) δ) ⁻¹' {i} ∩
      {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω ≤ ((n : ℕ) : ℕ∞)} =
      ⋃ m ∈ Finset.range (n + 1),
        ({ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω = ((m : ℕ) : ℕ∞)} ∩
          {ω : ℕ → Fin k × ℝ | trajArgmax m ω = i}) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      Finset.mem_range, Nat.lt_succ_iff, Set.mem_setOf_eq, exists_prop]
    constructor
    · rintro ⟨hi, hle⟩
      obtain ⟨m, hm⟩ : ∃ m : ℕ, ((m : ℕ) : ℕ∞) = chernoffStoppingTime (k := k) δ ω :=
        ENat.ne_top_iff_exists.mp fun htop ↦ by
          rw [htop] at hle; exact absurd hle (by simp)
      refine ⟨m, ?_, hm.symm, ?_⟩
      · rw [← hm] at hle; exact_mod_cast hle
      · rw [← hi, chernoffRecommendation_eq_argmax hk hδ hm.symm]
    · rintro ⟨m, hmn, hm, hi⟩
      refine ⟨by rw [chernoffRecommendation_eq_argmax hk hδ hm, hi], ?_⟩
      rw [hm]; exact_mod_cast hmn
  rw [hrw]
  refine MeasurableSet.biUnion (Set.to_countable _) fun m hm ↦ ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  exact ((banditFiltration k).mono hmn _ (measurableSet_chernoffStoppingTime_eq δ m)).inter
    ((banditFiltration k).mono hmn _ ((measurable_trajArgmax m) (measurableSet_singleton i)))

end Stop

end BanditAlgorithm

/-!
# The Chernoff inverse `f⁻¹(δ)`

`f(x) = e^{k−x}(x/k)^k` is continuous, equal to `1` at `x = k`, strictly
decreasing on `[k, ∞)`, and tends to `0`.  `chernoffInverse k δ` is defined as the
infimum of `{x ≥ k : f(x) ≤ δ}`, and this file proves the facts that make that
definition behave like an inverse:

* `chernoffF_chernoffInverse_le` — the infimum is attained, so `f(f⁻¹(δ)) ≤ δ`.
  This is what the soundness proof of L&S Lemma 33.7 actually consumes: the
  threshold really does deliver the promised confidence level.
* `chernoffInverse_le_of_le` — any admissible `x` bounds `f⁻¹(δ)` from above, so
  explicit thresholds can be plugged in.
* `chernoffInverse_antitone` — smaller confidence level, larger threshold.
* `chernoffF_antitoneOn` — `f` is decreasing on `[k, ∞)`, which is what makes
  `f⁻¹` an inverse rather than merely a lower bound.

Together with `chernoffThreshold_pos` these are all the properties of `β_t(δ)`
used anywhere in the Track-and-Stop analysis.
-/

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter Real Set

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. Continuity and monotonicity of `f` -/

theorem continuous_chernoffF (k : ℕ) : Continuous (chernoffF k) := by
  unfold chernoffF
  fun_prop

/-- `f` is strictly decreasing on `[k, ∞)`: its logarithmic derivative is
`k/x − 1 < 0` there.  We prove the (equivalent, and sufficient) statement that
`f` is antitone on `[k, ∞)` directly from `log x ≤ x − 1`. -/
theorem chernoffF_le_chernoffF_of_le (hk : 0 < k) {x y : ℝ} (hx : (k : ℝ) ≤ x)
    (hxy : x ≤ y) : chernoffF k y ≤ chernoffF k x := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hkR hx
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le hx0 hxy
  -- compare logarithms
  have hlog : Real.log (chernoffF k y) ≤ Real.log (chernoffF k x) := by
    have hlx : Real.log (chernoffF k x)
        = ((k : ℝ) - x) + k * (Real.log x - Real.log k) := by
      rw [chernoffF, Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp,
        Real.log_pow, Real.log_div hx0.ne' hkR.ne']
    have hly : Real.log (chernoffF k y)
        = ((k : ℝ) - y) + k * (Real.log y - Real.log k) := by
      rw [chernoffF, Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp,
        Real.log_pow, Real.log_div hy0.ne' hkR.ne']
    rw [hlx, hly]
    -- `k (log y − log x) ≤ y − x` because `log(y/x) ≤ y/x − 1` and `x ≥ k`
    have hratio : Real.log y - Real.log x ≤ y / x - 1 := by
      rw [← Real.log_div hy0.ne' hx0.ne']
      exact Real.log_le_sub_one_of_pos (by positivity)
    have hkx : (k : ℝ) * (y / x - 1) ≤ y - x := by
      have hyx : 0 ≤ y / x - 1 := by
        rw [sub_nonneg, le_div_iff₀ hx0]
        linarith
      calc (k : ℝ) * (y / x - 1) ≤ x * (y / x - 1) := by
            exact mul_le_mul_of_nonneg_right (le_trans hx (le_refl x)) hyx
        _ = y - x := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hratio (le_of_lt hkR)]
  have hposx : 0 < chernoffF k x := by
    rw [chernoffF]; positivity
  have hposy : 0 < chernoffF k y := by
    rw [chernoffF]; positivity
  exact (Real.log_le_log_iff hposy hposx).mp hlog

/-! ## 2. The infimum is attained -/

theorem isClosed_chernoffInverse_set (k : ℕ) (δ : ℝ) :
    IsClosed {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ} := by
  have h : {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ}
      = Set.Ici (k : ℝ) ∩ chernoffF k ⁻¹' Set.Iic δ := by
    ext x; simp [and_comm]
  rw [h]
  exact isClosed_Ici.inter (isClosed_Iic.preimage (continuous_chernoffF k))

/-- **The infimum defining `f⁻¹(δ)` is attained.** -/
theorem chernoffInverse_mem (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    chernoffInverse k δ ∈ {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ} :=
  IsClosed.csInf_mem (isClosed_chernoffInverse_set k δ)
    (chernoffInverse_set_nonempty hk hδ) chernoffInverse_set_bddBelow

/-- **`f⁻¹(δ)` really is a threshold at confidence `δ`.** -/
theorem chernoffF_chernoffInverse_le (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    chernoffF k (chernoffInverse k δ) ≤ δ :=
  (chernoffInverse_mem hk hδ).2

/-- Above the threshold the Chernoff function stays below `δ`. -/
theorem chernoffF_le_of_chernoffInverse_le (hk : 0 < k) {δ x : ℝ} (hδ : 0 < δ)
    (hx : chernoffInverse k δ ≤ x) : chernoffF k x ≤ δ :=
  le_trans (chernoffF_le_chernoffF_of_le hk (chernoffInverse_mem hk hδ).1 hx)
    (chernoffF_chernoffInverse_le hk hδ)

/-! ## 3. Comparison -/

/-- Any admissible point bounds the threshold. -/
theorem chernoffInverse_le_of_le {δ x : ℝ} (hx : (k : ℝ) ≤ x) (hfx : chernoffF k x ≤ δ) :
    chernoffInverse k δ ≤ x :=
  csInf_le chernoffInverse_set_bddBelow ⟨hx, hfx⟩

/-- Smaller confidence level, larger threshold. -/
theorem chernoffInverse_antitone (hk : 0 < k) {δ δ' : ℝ} (hδ : 0 < δ) (h : δ ≤ δ') :
    chernoffInverse k δ' ≤ chernoffInverse k δ :=
  chernoffInverse_le_of_le (chernoffInverse_mem hk hδ).1
    (le_trans (chernoffF_chernoffInverse_le hk hδ) h)

/-- The threshold is `k` exactly at confidence level `1`, and at least `k`
always. -/
theorem chernoffInverse_one (hk : 0 < k) : chernoffInverse k 1 = (k : ℝ) :=
  le_antisymm (chernoffInverse_le_of_le le_rfl (le_of_eq (chernoffF_self hk)))
    (chernoffInverse_ge hk one_pos)

/-! ## 4. Monotonicity of the whole threshold -/

theorem chernoffThreshold_antitone (hk : 0 < k) {δ δ' : ℝ} (hδ : 0 < δ) (h : δ ≤ δ')
    (t : ℕ) : chernoffThreshold k δ' t ≤ chernoffThreshold k δ t := by
  unfold chernoffThreshold
  exact add_le_add_right (chernoffInverse_antitone hk hδ h) _

end BanditAlgorithm

/-!
# An explicit `O(log(1/δ))` bound on the Chernoff inverse

L&S use `f⁻¹(δ) = (1 + o(1)) log(1/δ)` to keep the leading constant of
Theorem 33.6 exact.  The `o(1)` is delicate, but the *order* is elementary and is
what every finiteness argument needs:

  `f⁻¹(δ) ≤ (k + log(1/δ)) / (1 − 1/e)`.

The proof is one application of `log y ≤ y/e` (itself `log(y/e) ≤ y/e − 1`):

  `log f(x) = (k − x) + k log(x/k) ≤ (k − x) + x/e = k − x(1 − 1/e)`,

so `f(x) ≤ δ` as soon as `x (1 − 1/e) ≥ k + log(1/δ)`; and any such `x` is
automatically `≥ k`, because `1 − 1/e < 1` and `log(1/δ) ≥ 0` for `δ ≤ 1`.
-/

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter Real

namespace BanditAlgorithm

variable {k : ℕ}

/-- `log y ≤ y / e`. -/
theorem log_le_div_exp_one {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (x := y / Real.exp 1)
    (div_pos hy (Real.exp_pos 1))
  rw [Real.log_div hy.ne' (Real.exp_ne_zero 1), Real.log_exp] at h
  linarith

/-- The explicit form of `log f(x)` for `x > 0`. -/
theorem log_chernoffF (hk : 0 < k) {x : ℝ} (hx : 0 < x) :
    Real.log (chernoffF k x) = ((k : ℝ) - x) + k * (Real.log x - Real.log k) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [chernoffF, Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp,
    Real.log_pow, Real.log_div hx.ne' hkR.ne']

/-- **The order bound.**  Every `x` with `x (1 − 1/e) ≥ k + log(1/δ)` is an
admissible threshold. -/
theorem chernoffF_le_of_le (hk : 0 < k) {δ x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hx : (k : ℝ) + Real.log (1 / δ) ≤ x * (1 - (Real.exp 1)⁻¹)) :
    chernoffF k x ≤ δ := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have he : (1 : ℝ) < Real.exp 1 := by
    simpa using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hfac : (0 : ℝ) < 1 - (Real.exp 1)⁻¹ := by
    have : (Real.exp 1)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]; right; exact he
    linarith
  have hlogδ : 0 ≤ Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_nonneg ((one_le_inv_iff₀).mpr ⟨hδ, hδ1⟩)
  have hx0 : 0 < x := by
    by_contra hcon
    push_neg at hcon
    have : x * (1 - (Real.exp 1)⁻¹) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon hfac.le
    linarith
  -- the key logarithmic estimate
  have hlog : Real.log (chernoffF k x) ≤ Real.log δ := by
    rw [log_chernoffF hk hx0]
    have hbound : (k : ℝ) * (Real.log x - Real.log k) ≤ x * (Real.exp 1)⁻¹ := by
      have h := log_le_div_exp_one (y := x / (k : ℝ)) (by positivity)
      rw [Real.log_div hx0.ne' hkR.ne'] at h
      calc (k : ℝ) * (Real.log x - Real.log k) ≤ (k : ℝ) * (x / (k : ℝ) / Real.exp 1) :=
            mul_le_mul_of_nonneg_left h hkR.le
        _ = x * (Real.exp 1)⁻¹ := by field_simp
    have hδlog : Real.log (1 / δ) = -Real.log δ := by
      rw [one_div, Real.log_inv]
    rw [hδlog] at hx
    nlinarith
  have hpos : 0 < chernoffF k x := by rw [chernoffF]; positivity
  exact (Real.log_le_log_iff hpos hδ).mp hlog

/-- **`f⁻¹(δ) = O(k + log(1/δ))`.** -/
theorem chernoffInverse_le_explicit (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    chernoffInverse k δ ≤ ((k : ℝ) + Real.log (1 / δ)) / (1 - (Real.exp 1)⁻¹) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have he : (1 : ℝ) < Real.exp 1 := by
    simpa using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hfac : (0 : ℝ) < 1 - (Real.exp 1)⁻¹ := by
    have : (Real.exp 1)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]; right; exact he
    linarith
  have hfac1 : 1 - (Real.exp 1)⁻¹ ≤ 1 := by
    have : (0 : ℝ) < (Real.exp 1)⁻¹ := by positivity
    linarith
  have hlogδ : 0 ≤ Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_nonneg ((one_le_inv_iff₀).mpr ⟨hδ, hδ1⟩)
  set x : ℝ := ((k : ℝ) + Real.log (1 / δ)) / (1 - (Real.exp 1)⁻¹) with hxdef
  have hxk : (k : ℝ) ≤ x := by
    rw [hxdef, le_div_iff₀ hfac]
    nlinarith
  refine chernoffInverse_le_of_le hxk (chernoffF_le_of_le hk hδ hδ1 ?_)
  rw [hxdef, div_mul_cancel₀ _ (ne_of_gt hfac)]

/-- Consequently the whole threshold is `O(k log(t²+t) + k + log(1/δ))`. -/
theorem chernoffThreshold_le_explicit (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (t : ℕ) :
    chernoffThreshold k δ t
      ≤ (k : ℝ) * Real.log ((t : ℝ) ^ 2 + (t : ℝ))
        + ((k : ℝ) + Real.log (1 / δ)) / (1 - (Real.exp 1)⁻¹) := by
  rw [chernoffThreshold]
  exact add_le_add_right (chernoffInverse_le_explicit hk hδ hδ1) _

end BanditAlgorithm

/-!
# The sharp lower bound on the threshold constant

`Solutions/ChernoffInverseBound.lean` bounds `f⁻¹(δ)` from *above* by
`(k + log(1/δ))/(1 − e⁻¹)`, which is what shows the sample complexity of
Chernoff's rule is `O(log(1/δ))`.  Turning the mixture martingale into the
threshold `β_t(δ) = k log(t²+t) + f⁻¹(δ)` of Lattimore--Szepesvári Lemma 33.7 needs
the opposite estimate, and needs it sharp.

Taking logarithms in `f(f⁻¹(δ)) ≤ δ` — that is, in
`e^{k−f⁻¹(δ)}(f⁻¹(δ)/k)^k ≤ δ` — gives directly

  `f⁻¹(δ) ≥ k + log(1/δ) + k·log(f⁻¹(δ)/k)`.

Dropping the last term (nonnegative, since `f⁻¹(δ) ≥ k`) recovers the crude
`f⁻¹(δ) ≥ k + log(1/δ)`, but the last term is exactly what one cannot afford to
drop: it grows like `k log log(1/δ)`, and that is the slack which pays for the
`½log(1 + cT)` prices of the mixture at prior variance `c ≈ log(1/δ)/k`.  Without
it the mixture argument fails for small `δ`, no matter how the variance is tuned.
-/

open Real

namespace BanditAlgorithm

variable {k : ℕ}

/-- `f⁻¹(δ) ≥ k`, restated. -/
theorem le_chernoffInverse (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    (k : ℝ) ≤ chernoffInverse k δ := (chernoffInverse_mem hk hδ).1

theorem chernoffInverse_pos' (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    0 < chernoffInverse k δ :=
  lt_of_lt_of_le (by exact_mod_cast hk) (le_chernoffInverse hk hδ)

/-- **The sharp lower bound on the threshold constant.**  Taking logarithms in
`f(f⁻¹(δ)) ≤ δ`. -/
theorem chernoffInverse_ge_sharp (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    (k : ℝ) + Real.log (1 / δ)
        + k * Real.log (chernoffInverse k δ / (k : ℝ))
      ≤ chernoffInverse k δ := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set β := chernoffInverse k δ with hβ
  have hβpos : 0 < β := chernoffInverse_pos' hk hδ
  have hf : chernoffF k β ≤ δ := chernoffF_chernoffInverse_le hk hδ
  have hfpos : 0 < chernoffF k β := by
    unfold chernoffF
    have : (0 : ℝ) < β / (k : ℝ) := by positivity
    positivity
  -- take logarithms
  have hlog : Real.log (chernoffF k β) ≤ Real.log δ := Real.log_le_log hfpos hf
  rw [log_chernoffF hk hβpos] at hlog
  have hdiv : Real.log (β / (k : ℝ)) = Real.log β - Real.log (k : ℝ) :=
    Real.log_div hβpos.ne' hkR.ne'
  have hinv : Real.log (1 / δ) = -Real.log δ := by
    rw [one_div, Real.log_inv]
  rw [hdiv, hinv]
  linarith

/-- The crude consequence: `f⁻¹(δ) ≥ k + log(1/δ)`. -/
theorem chernoffInverse_ge_add_log (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (k : ℝ) + Real.log (1 / δ) ≤ chernoffInverse k δ := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hsharp := chernoffInverse_ge_sharp hk hδ
  have hge : (1 : ℝ) ≤ chernoffInverse k δ / (k : ℝ) :=
    (one_le_div hkR).mpr (le_chernoffInverse hk hδ)
  have hlog : 0 ≤ Real.log (chernoffInverse k δ / (k : ℝ)) := Real.log_nonneg hge
  nlinarith [mul_nonneg hkR.le hlog]

/-- The logarithmic slack, isolated: `f⁻¹(δ) − k − log(1/δ) ≥ k log(f⁻¹(δ)/k)`, and
`f⁻¹(δ)/k ≥ 1 + log(1/δ)/k`, so the slack is at least `k log(1 + log(1/δ)/k)`. -/
theorem chernoffInverse_slack (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (k : ℝ) + Real.log (1 / δ)
        + k * Real.log (1 + Real.log (1 / δ) / (k : ℝ))
      ≤ chernoffInverse k δ := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hL : 0 ≤ Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_nonneg ((one_le_inv₀ hδ).mpr hδ1)
  have hsharp := chernoffInverse_ge_sharp hk hδ
  -- `f⁻¹(δ)/k ≥ 1 + log(1/δ)/k` from the crude bound
  have hcrude := chernoffInverse_ge_add_log hk hδ hδ1
  have hratio : 1 + Real.log (1 / δ) / (k : ℝ) ≤ chernoffInverse k δ / (k : ℝ) := by
    rw [le_div_iff₀ hkR, add_mul, one_mul, div_mul_cancel₀ _ hkR.ne']
    exact hcrude

  have hmono : Real.log (1 + Real.log (1 / δ) / (k : ℝ))
      ≤ Real.log (chernoffInverse k δ / (k : ℝ)) :=
    Real.log_le_log (by positivity) hratio
  nlinarith [mul_le_mul_of_nonneg_left hmono hkR.le]

end BanditAlgorithm

/-!
# When a linear statistic overtakes Chernoff's threshold

The sample-complexity half of Theorem 33.6 rests on a deterministic estimate.
Once the empirical allocation has settled, the generalised-likelihood-ratio
statistic grows linearly, `Z_t ≳ r·t` with `r ≈ c*(ν)⁻¹`, while the threshold
`β_t(δ) = k log(t²+t) + f⁻¹(δ)` grows only logarithmically in `t`.  So the two
must cross, and Chernoff's rule stops.  What the analysis needs is not just that
they cross but *where*: an explicit round, linear in `f⁻¹(δ)` and hence in
`log(1/δ)`, beyond which the linear statistic is ahead.

That is `linear_ge_threshold`: for

  `t ≥ max( (8K/r)², 2C/r )`,   `C ≥ K log 2 + β₀`,

one has `K log(t²+t) + β₀ ≤ r·t`.  The two conditions are the two ways the
threshold can be ahead — the logarithmic term (paid for by `t ≥ (8K/r)²`) and the
constant `β₀` (paid for by `t ≥ 2C/r`).  Since `β₀ = f⁻¹(δ)` enters only through
`C`, the crossing round is linear in `f⁻¹(δ)`, which is what makes
`E[τ_δ]/log(1/δ)` converge to `c*(ν)` and not to a larger constant.

The proof uses `log t ≤ 2√t`, which is `log √t ≤ √t − 1` — a cruder bound than
`log t ≤ t/e`, but the right one here, because the linear term must dominate a
*logarithm*, not a linear function.
-/

open Real

namespace BanditAlgorithm

/-! ## `log t ≤ 2√t` -/

theorem log_le_two_sqrt {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hlog : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 :=
    Real.log_le_sub_one_of_pos hs
  have hsplit : Real.log t = 2 * Real.log (Real.sqrt t) := by
    conv_lhs => rw [← hsq]
    rw [Real.log_mul hs.ne' hs.ne']
    ring
  rw [hsplit]
  linarith

/-- `log(t² + t) ≤ log 2 + 2 log t` for `t ≥ 1`. -/
theorem log_sq_add_le {t : ℝ} (ht : 1 ≤ t) :
    Real.log (t ^ 2 + t) ≤ Real.log 2 + 2 * Real.log t := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hle : t ^ 2 + t ≤ 2 * t ^ 2 := by nlinarith
  calc Real.log (t ^ 2 + t) ≤ Real.log (2 * t ^ 2) :=
        Real.log_le_log (by positivity) hle
    _ = Real.log 2 + 2 * Real.log t := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        push_cast
        ring

/-! ## The crossing estimate -/

/-- **A linear statistic overtakes a logarithmic threshold, explicitly.**  For
`K ≥ 0`, `r > 0` and `C ≥ 0` with `K log 2 + β₀ ≤ C`, every `t ≥ 1` satisfying
`t ≥ (8K/r)²` and `t ≥ 2C/r` has `K log(t²+t) + β₀ ≤ r t`. -/
theorem linear_ge_threshold {K r C β₀ : ℝ} (hK : 0 ≤ K) (hr : 0 < r) (hC : 0 ≤ C)
    (hCge : K * Real.log 2 + β₀ ≤ C) {t : ℝ} (ht1 : 1 ≤ t)
    (ht2 : (8 * K / r) ^ 2 ≤ t) (ht3 : 2 * C / r ≤ t) :
    K * Real.log (t ^ 2 + t) + β₀ ≤ r * t := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  -- the logarithmic part
  have hlog : K * Real.log (t ^ 2 + t) ≤ K * Real.log 2 + 4 * K * Real.sqrt t := by
    have h1 : Real.log (t ^ 2 + t) ≤ Real.log 2 + 2 * Real.log t := log_sq_add_le ht1
    have h2 : Real.log t ≤ 2 * Real.sqrt t := log_le_two_sqrt ht0
    nlinarith [mul_le_mul_of_nonneg_left h1 hK, mul_le_mul_of_nonneg_left h2 hK]
  -- the constant part is covered by `t ≥ 2C/r`
  have hconst : C ≤ r * t / 2 := by
    rw [div_le_iff₀ hr] at ht3
    linarith
  -- the square-root part is covered by `t ≥ (8K/r)²`
  have hroot : 4 * K * Real.sqrt t ≤ r * t / 2 := by
    have hKr : 8 * K / r ≤ Real.sqrt t := by
      have hnn : (0 : ℝ) ≤ 8 * K / r := by positivity
      have := Real.sqrt_le_sqrt ht2
      rwa [Real.sqrt_sq hnn] at this
    have h8 : 8 * K ≤ r * Real.sqrt t := by
      rw [div_le_iff₀ hr] at hKr
      linarith
    have : 8 * K * Real.sqrt t ≤ r * Real.sqrt t * Real.sqrt t :=
      mul_le_mul_of_nonneg_right h8 hs.le
    nlinarith [hsq]
  linarith

/-! ## The bound at the Chernoff threshold

Specialised to `K = k` and `β₀ = f⁻¹(δ)`, the crossing round is linear in
`f⁻¹(δ)`, hence — by `chernoffInverse_le_explicit` — in `log(1/δ)`. -/

theorem chernoffThreshold_le_linear {k : ℕ} (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ)
    {r : ℝ} (hr : 0 < r) {t : ℝ} (ht1 : 1 ≤ t)
    (ht2 : (8 * (k : ℝ) / r) ^ 2 ≤ t)
    (ht3 : 2 * ((k : ℝ) * Real.log 2 + chernoffInverse k δ) / r ≤ t) :
    (k : ℝ) * Real.log (t ^ 2 + t) + chernoffInverse k δ ≤ r * t := by
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hC : (0 : ℝ) ≤ (k : ℝ) * Real.log 2 + chernoffInverse k δ := by
    have h1 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h2 : (0 : ℝ) < chernoffInverse k δ := chernoffInverse_pos' hk hδ
    positivity
  exact linear_ge_threshold hkR hr hC le_rfl ht1 ht2 ht3

/-- The crossing round in the form the sample-complexity argument uses: an
explicit `N` beyond which the linear statistic is ahead of the threshold at every
round. -/
theorem exists_crossing_round {k : ℕ} (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) {r : ℝ}
    (hr : 0 < r) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ t : ℝ, 1 ≤ t → N ≤ t →
      (k : ℝ) * Real.log (t ^ 2 + t) + chernoffInverse k δ ≤ r * t := by
  refine ⟨max ((8 * (k : ℝ) / r) ^ 2)
      (2 * ((k : ℝ) * Real.log 2 + chernoffInverse k δ) / r), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ (8 * (k : ℝ) / r) ^ 2 := sq_nonneg _
    exact le_trans h1 (le_max_left _ _)
  · intro t ht1 hN
    exact chernoffThreshold_le_linear hk hδ hr ht1
      (le_trans (le_max_left _ _) hN) (le_trans (le_max_right _ _) hN)

end BanditAlgorithm

/-!
# `f⁻¹(δ) ≤ (1 + ε) log(1/δ) + C(k, ε)`, uniformly in `δ`

`Solutions/ChernoffInverseBound.lean` proves the *order* bound
`f⁻¹(δ) ≤ (k + log(1/δ))/(1 − 1/e)`, whose multiplicative constant
`1/(1 − 1/e) ≈ 1.582` is fine for finiteness statements but destroys the leading
constant of Theorem 33.6.  `Solutions/ChernoffInverseAsymptotic.lean` proves
`f⁻¹(δ)/log(1/δ) → 1`, which has the right constant but only *eventually* in `δ`.

The sample-complexity argument needs both at once: a bound with multiplicative
constant `1 + ε` that holds for **every** `δ ∈ (0, 1]`, the excess being absorbed
into an additive constant depending on `k` and `ε` alone.  That is what this file
supplies:

  `f⁻¹(δ) ≤ (1 + ε) log(1/δ) + k + k(1 + ε) log((1 + ε)/ε)`.

Why one can do better than `1/(1 − 1/e)`: the order bound estimates `log y ≤ y/e`,
which is the *tangent* bound at `y = e` and so is only tight there.  Replacing it
by the tangent at an arbitrary point `c`,

  `log y ≤ y/c + log c − 1`,

makes the linear coefficient `1/c` as small as one likes, at the cost of the
additive `k log c`.  Taking `c = (1 + ε)/ε` makes the coefficient of `log(1/δ)`
come out to exactly `1 + ε`, and `k(1 + ε) log c` is then the price.  The price
blows up as `ε → 0`, which is the correct behaviour: `f⁻¹(δ) − log(1/δ) ∼
k log log(1/δ)` is genuinely unbounded, so no bound with `ε = 0` and a constant
can hold.
-/

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter Real

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## The shifted tangent bound on the logarithm -/

/-- `log y ≤ y/c + log c − 1` for all `y, c > 0`: the tangent to `log` at `y = c`.
Taking `c = e` recovers `log y ≤ y/e`. -/
theorem log_le_div_add_log_sub_one {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Real.log y ≤ y / c + Real.log c - 1 := by
  have h := Real.log_le_sub_one_of_pos (x := y / c) (div_pos hy hc)
  rw [Real.log_div hy.ne' hc.ne'] at h
  linarith

/-- The form in which the estimate is applied to `f`: `k log(x/k) ≤ x/c + k log c − k`. -/
theorem mul_log_div_le (hk : 0 < k) {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    (k : ℝ) * (Real.log x - Real.log k) ≤ x / c + (k : ℝ) * Real.log c - (k : ℝ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h := log_le_div_add_log_sub_one (y := x / (k : ℝ)) (by positivity) hc
  rw [Real.log_div hx.ne' hkR.ne'] at h
  have hmul : (k : ℝ) * (Real.log x - Real.log k)
      ≤ (k : ℝ) * (x / (k : ℝ) / c + Real.log c - 1) :=
    mul_le_mul_of_nonneg_left h hkR.le
  have hid : (k : ℝ) * (x / (k : ℝ) / c + Real.log c - 1)
      = x / c + (k : ℝ) * Real.log c - (k : ℝ) := by
    field_simp
  linarith [hid ▸ hmul]

/-! ## The additive constant -/

/-- `C(k, ε) = k + k(1 + ε) log((1 + ε)/ε)`, the additive price of forcing the
multiplicative constant down to `1 + ε`. -/
noncomputable def chernoffInverseConst (k : ℕ) (ε : ℝ) : ℝ :=
  (k : ℝ) + (k : ℝ) * (1 + ε) * Real.log ((1 + ε) / ε)

theorem one_lt_tangentPoint {ε : ℝ} (hε : 0 < ε) : 1 < (1 + ε) / ε := by
  rw [lt_div_iff₀ hε]
  linarith

theorem log_tangentPoint_nonneg {ε : ℝ} (hε : 0 < ε) : 0 ≤ Real.log ((1 + ε) / ε) :=
  Real.log_nonneg (one_lt_tangentPoint hε).le

theorem chernoffInverseConst_ge (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    (k : ℝ) ≤ chernoffInverseConst k ε := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h : 0 ≤ (k : ℝ) * (1 + ε) * Real.log ((1 + ε) / ε) := by
    have := log_tangentPoint_nonneg hε
    positivity
  rw [chernoffInverseConst]
  linarith

theorem chernoffInverseConst_nonneg (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ chernoffInverseConst k ε :=
  le_trans (Nat.cast_nonneg k) (chernoffInverseConst_ge hk hε)

/-! ## The bound -/

/-- The admissibility criterion, in the sharpened form: any `x ≥ k` with
`x/(1 + ε) ≥ log(1/δ) + k log((1 + ε)/ε)` satisfies `f(x) ≤ δ`. -/
theorem chernoffF_le_of_sharp (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) {δ x : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hx : 0 < x)
    (hxb : Real.log (1 / δ) + (k : ℝ) * Real.log ((1 + ε) / ε) ≤ x / (1 + ε)) :
    chernoffF k x ≤ δ := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set c : ℝ := (1 + ε) / ε with hcdef
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  -- `1 - 1/c = 1/(1+ε)`
  have hinv : 1 - 1 / c = 1 / (1 + ε) := by
    rw [hcdef]
    field_simp
    ring
  have hlog : Real.log (chernoffF k x) ≤ Real.log δ := by
    rw [log_chernoffF hk hx]
    have hb := mul_log_div_le hk hx hc0
    -- `log f(x) ≤ -x(1 - 1/c) + k log c`
    have hstep : ((k : ℝ) - x) + (k : ℝ) * (Real.log x - Real.log k)
        ≤ -(x * (1 - 1 / c)) + (k : ℝ) * Real.log c := by
      have hxc : x / c = x * (1 / c) := by ring
      nlinarith [hb, hxc]
    have hδlog : Real.log (1 / δ) = -Real.log δ := by
      rw [one_div, Real.log_inv]
    have hkey : x * (1 - 1 / c) ≥ Real.log (1 / δ) + (k : ℝ) * Real.log c := by
      rw [hinv]
      have : x * (1 / (1 + ε)) = x / (1 + ε) := by ring
      rw [this]
      exact hxb
    linarith
  have hpos : 0 < chernoffF k x := by rw [chernoffF]; positivity
  exact (Real.log_le_log_iff hpos hδ).mp hlog

/-- **`f⁻¹(δ) ≤ (1 + ε) log(1/δ) + C(k, ε)` for every `δ ∈ (0, 1]`.**  Unlike the
asymptotic version this holds at every confidence level, which is what the
sample-complexity bound needs: the additive constant is absorbed into the
`δ`-free random time, and the multiplicative `1 + ε` into the `ε`-slack of
Theorem 33.6. -/
theorem chernoffInverse_le_linear (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    chernoffInverse k δ ≤ (1 + ε) * Real.log (1 / δ) + chernoffInverseConst k ε := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  have hL : 0 ≤ Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_nonneg ((one_le_inv_iff₀).mpr ⟨hδ, hδ1⟩)
  set L : ℝ := Real.log (1 / δ) with hLdef
  set x : ℝ := (1 + ε) * L + chernoffInverseConst k ε with hxdef
  have hCk : (k : ℝ) ≤ chernoffInverseConst k ε := chernoffInverseConst_ge hk hε
  have hxk : (k : ℝ) ≤ x := by
    have : 0 ≤ (1 + ε) * L := by positivity
    rw [hxdef]; linarith
  have hx0 : 0 < x := lt_of_lt_of_le hkR hxk
  refine chernoffInverse_le_of_le hxk (chernoffF_le_of_sharp hk hε hδ hδ1 hx0 ?_)
  -- `x/(1+ε) = L + (k + k(1+ε) log c)/(1+ε) ≥ L + k log c`
  have hlc : 0 ≤ Real.log ((1 + ε) / ε) := log_tangentPoint_nonneg hε
  rw [hxdef, chernoffInverseConst, le_div_iff₀ hε1]
  have hexpand : (Real.log (1 / δ) + (k : ℝ) * Real.log ((1 + ε) / ε)) * (1 + ε)
      = (1 + ε) * L + (k : ℝ) * (1 + ε) * Real.log ((1 + ε) / ε) := by
    rw [hLdef]; ring
  rw [hexpand]
  linarith

/-- The threshold in the same form: `β_n(δ) ≤ k log(n² + n) + (1 + ε) log(1/δ) + C(k, ε)`. -/
theorem chernoffThreshold_le_affine_log (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (n : ℕ) :
    chernoffThreshold k δ n
      ≤ (k : ℝ) * Real.log ((n : ℝ) ^ 2 + (n : ℝ))
        + ((1 + ε) * Real.log (1 / δ) + chernoffInverseConst k ε) := by
  rw [chernoffThreshold]
  exact add_le_add_right (chernoffInverse_le_linear hk hε hδ hδ1) _

end BanditAlgorithm

/-!
# The crossing estimate with no loss in the constant

`Solutions/CrossingTime.lean` proves that a linear statistic overtakes the
logarithmic threshold at

  `t ≥ max( (8K/r)², 2(K log 2 + β₀)/r )`.

That is enough for *finiteness* of the stopping time, but the second condition
carries a factor `2` in front of `β₀`, and `β₀ = f⁻¹(δ)` is the term that grows
as `δ → 0`.  A factor `2` there is a factor `2` in the sample complexity, which
would turn Theorem 33.6's constant `c*(ν)` into `2 c*(ν)`.

The factor is an artefact of splitting `r t` into two equal halves, one for the
logarithm and one for the constant.  The logarithm needs only an *asymptotically
negligible* share, so the split can be made `(ε : 1)` instead of `(1 : 1)`:

  `r t = r' t + (r − r') t`,   `r' = εr/(1 + ε)`,   `r − r' = r/(1 + ε)`.

The first summand absorbs `K log(t² + t)` once `t` exceeds a threshold depending
on `K, r, ε` **but not on `β₀`**; the second absorbs `β₀` once
`t ≥ (1 + ε)β₀/r`.  The loss is now multiplicative-`(1 + ε)` on the `β₀` term and
purely additive elsewhere, which is exactly the shape Theorem 33.6 tolerates: the
`δ`-free part goes into the integrable random time `W`, and the `(1 + ε)` into
the `ε`-slack of the statement.
-/

open Real

namespace BanditAlgorithm

/-! ## The `δ`-free part of the crossing round -/

/-- `N(K, r, ε)`: the round beyond which the logarithmic term `K log(t² + t)` is
below the share `εr/(1 + ε)` of the linear statistic.  It does not involve the
threshold constant `β₀`, which is the whole point. -/
noncomputable def crossingConst (K r ε : ℝ) : ℝ :=
  max 1 (max ((8 * K * (1 + ε) / (ε * r)) ^ 2)
    (2 * K * Real.log 2 * (1 + ε) / (ε * r)))

theorem one_le_crossingConst (K r ε : ℝ) : 1 ≤ crossingConst K r ε :=
  le_max_left _ _

theorem crossingConst_nonneg (K r ε : ℝ) : 0 ≤ crossingConst K r ε :=
  le_trans zero_le_one (one_le_crossingConst K r ε)

/-! ## The sharp crossing lemma -/

/-- **A linear statistic overtakes a logarithmic threshold with no constant
loss.**  For `t ≥ N(K, r, ε)` and `t ≥ (1 + ε)β₀/r`,

  `K log(t² + t) + β₀ ≤ r t`.

The dependence on `β₀` is `(1 + ε)β₀/r`, not `2β₀/r`: the multiplicative loss can
be made arbitrarily small, at the cost of a larger `β₀`-free constant. -/
theorem linear_ge_threshold_sharp {K r ε β₀ : ℝ} (hK : 0 ≤ K) (hr : 0 < r)
    (hε : 0 < ε) (hβ₀ : 0 ≤ β₀) {t : ℝ}
    (hN : crossingConst K r ε ≤ t) (htβ : (1 + ε) * β₀ / r ≤ t) :
    K * Real.log (t ^ 2 + t) + β₀ ≤ r * t := by
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  set r' : ℝ := ε * r / (1 + ε) with hr'def
  have hr'0 : 0 < r' := by rw [hr'def]; positivity
  have ht1 : (1 : ℝ) ≤ t := le_trans (one_le_crossingConst K r ε) hN
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  -- the two conditions of the coarse estimate, at slope `r'`
  have hrw : 8 * K / r' = 8 * K * (1 + ε) / (ε * r) := by
    rw [hr'def]; field_simp
  have ht2 : (8 * K / r') ^ 2 ≤ t := by
    rw [hrw]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hrw2 : 2 * (K * Real.log 2) / r' = 2 * K * Real.log 2 * (1 + ε) / (ε * r) := by
    rw [hr'def]; field_simp
  have ht3 : 2 * (K * Real.log 2) / r' ≤ t := by
    rw [hrw2]
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hClog : (0 : ℝ) ≤ K * Real.log 2 :=
    mul_nonneg hK (Real.log_nonneg (by norm_num))
  -- the logarithm is below the `ε`-share
  have hlog : K * Real.log (t ^ 2 + t) + 0 ≤ r' * t :=
    linear_ge_threshold hK hr'0 hClog (by linarith) ht1 ht2 ht3
  -- the constant is below the remaining share
  have hconst : β₀ ≤ r / (1 + ε) * t := by
    rw [div_le_iff₀ hr] at htβ
    rw [div_mul_eq_mul_div, le_div_iff₀ hε1]
    nlinarith
  have hsplit : r' * t + r / (1 + ε) * t = r * t := by
    rw [hr'def]
    field_simp
    ring
  linarith

/-! ## The estimate at integer rounds -/

/-- The integer form: `⌈N(K, r, ε)⌉ + ⌈(1 + ε)β₀/r⌉` rounds suffice, and the two
summands are respectively `β₀`-free and `δ`-free-of-everything-but-`β₀`. -/
theorem linear_ge_threshold_nat {K r ε β₀ : ℝ} (hK : 0 ≤ K) (hr : 0 < r)
    (hε : 0 < ε) (hβ₀ : 0 ≤ β₀) {n : ℕ}
    (hN : ⌈crossingConst K r ε⌉₊ ≤ n) (hnβ : ⌈(1 + ε) * β₀ / r⌉₊ ≤ n) :
    K * Real.log ((n : ℝ) ^ 2 + (n : ℝ)) + β₀ ≤ r * (n : ℝ) := by
  refine linear_ge_threshold_sharp hK hr hε hβ₀ ?_ ?_
  · exact le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  · exact le_trans (Nat.le_ceil _) (by exact_mod_cast hnβ)

/-- Both conditions hold at the single round `⌈N⌉ + ⌈(1 + ε)β₀/r⌉`, and at every
later round. -/
theorem linear_ge_threshold_at_sum {K r ε β₀ : ℝ} (hK : 0 ≤ K) (hr : 0 < r)
    (hε : 0 < ε) (hβ₀ : 0 ≤ β₀) {n : ℕ}
    (hn : ⌈crossingConst K r ε⌉₊ + ⌈(1 + ε) * β₀ / r⌉₊ ≤ n) :
    K * Real.log ((n : ℝ) ^ 2 + (n : ℝ)) + β₀ ≤ r * (n : ℝ) :=
  linear_ge_threshold_nat hK hr hε hβ₀ (le_trans (Nat.le_add_right _ _) hn)
    (le_trans (Nat.le_add_left _ _) hn)

/-! ## Specialisation to Chernoff's threshold

`β_n(δ) = k log(n² + n) + f⁻¹(δ)`, and `f⁻¹(δ) ≤ (1 + ε) log(1/δ) + C(k, ε)` by
`chernoffInverse_le_linear`.  Both losses are `(1 + ε)`, so the crossing round is

  `⌈N(k, r, ε)⌉ + ⌈(1 + ε)((1 + ε) log(1/δ) + C(k, ε))/r⌉`,

whose `δ`-dependence is `(1 + ε)² log(1/δ)/r` — the constant `(1 + ε)²` tends to
`1`, which is what keeps Theorem 33.6 sharp. -/

variable {k : ℕ}

/-- The `δ`-dependent part of the crossing round: `(1 + ε)((1 + ε) log(1/δ) +
C(k, ε))/r`. -/
noncomputable def crossingBudget (k : ℕ) (r ε δ : ℝ) : ℝ :=
  (1 + ε) * ((1 + ε) * Real.log (1 / δ) + chernoffInverseConst k ε) / r

theorem crossingBudget_nonneg (hk : 0 < k) {r ε δ : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 0 ≤ crossingBudget k r ε δ := by
  have hL : 0 ≤ Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_nonneg ((one_le_inv_iff₀).mpr ⟨hδ, hδ1⟩)
  have hC : 0 ≤ chernoffInverseConst k ε := chernoffInverseConst_nonneg hk hε
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  rw [crossingBudget]
  positivity

/-- **Chernoff's threshold is below a linear statistic of slope `r` from round
`⌈N(k, r, ε)⌉ + ⌈budget⌉ on.** -/
theorem chernoffThreshold_le_of_crossing (hk : 0 < k) {r ε : ℝ} (hr : 0 < r)
    (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {n : ℕ}
    (hn : ⌈crossingConst (k : ℝ) r ε⌉₊ + ⌈crossingBudget k r ε δ⌉₊ ≤ n) :
    chernoffThreshold k δ n ≤ r * (n : ℝ) := by
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  have hL : 0 ≤ Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_nonneg ((one_le_inv_iff₀).mpr ⟨hδ, hδ1⟩)
  set β₀ : ℝ := (1 + ε) * Real.log (1 / δ) + chernoffInverseConst k ε with hβdef
  have hβ0 : 0 ≤ β₀ := by
    have hC : 0 ≤ chernoffInverseConst k ε := chernoffInverseConst_nonneg hk hε
    rw [hβdef]; positivity
  have hbud : crossingBudget k r ε δ = (1 + ε) * β₀ / r := rfl
  have hmain : (k : ℝ) * Real.log ((n : ℝ) ^ 2 + (n : ℝ)) + β₀ ≤ r * (n : ℝ) := by
    refine linear_ge_threshold_at_sum hkR hr hε hβ0 ?_
    rwa [hbud] at hn
  have hinv : chernoffInverse k δ ≤ β₀ := chernoffInverse_le_linear hk hε hδ hδ1
  rw [chernoffThreshold]
  linarith

end BanditAlgorithm

theorem _root_.solution {K r ε β₀ t : ℝ} (hK : 0 ≤ K) (hr : 0 < r) (hε : 0 < ε)
    (hβ₀ : 0 ≤ β₀) (ht1 : 1 ≤ t)
    (ht2 : (8 * K * (1 + ε) / (ε * r)) ^ 2 ≤ t)
    (ht3 : 2 * K * Real.log 2 * (1 + ε) / (ε * r) ≤ t)
    (htβ : (1 + ε) * β₀ / r ≤ t) :
    K * Real.log (t ^ 2 + t) + β₀ ≤ r * t :=
  BanditAlgorithm.linear_ge_threshold_sharp hK hr hε hβ₀
    (max_le ht1 (max_le ht2 ht3)) htβ
