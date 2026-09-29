-- Prove2me | solution 1 for BanditAlgorithm.hitting_time_lintegral_le_tsum_failure
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T23:16:57.984484+00:00
-- url     : https://prove2.me/submissions/52b6bf00-59dc-4b6c-a097-a538b4d2cd20

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# The last round at which a sequence of events fails, and when it is integrable

Garivier & Kaufmann's Proposition 13 — the finiteness half of the sample
complexity of Track-and-Stop — is an instance of a single general fact, which
has nothing to do with bandits:

> Let `G 0, G 1, …` be events ("by round `m` the empirical quantities are already
> within `ξ` of their limits").  Let `T ω` be the first round from which *all*
> the `G m` hold.  Then
>
>   `∫⁻ T dμ ≤ ∑' m, (m + 1) · μ (G m)ᶜ`.

So `T` is integrable as soon as the failure probabilities `μ (G m)ᶜ` are summable
against `m` — for instance when they decay geometrically, which is what a
concentration inequality supplies.  This is the standard "`E[T] = ∑ P(T > n)`"
argument, and the bound above is what makes the `W` of
`chernoff_stopping_time_le_integrable_plus_linear` integrable.

The proof here deliberately avoids having to prove `T` measurable: the estimate
is established *pointwise*,

  `T ω ≤ ∑' m, (m + 1) · 1_{(G m)ᶜ}(ω)`,

and `lintegral_mono` needs no measurability of the smaller function.  The
pointwise bound is sharp in the only case that matters: if `ω` fails the events
exactly on a finite set with maximum `m₀`, then `T ω = m₀ + 1` and the `m₀`-th
summand alone is `m₀ + 1`.
-/

open MeasureTheory ENNReal NNReal

namespace BanditAlgorithm

variable {α : Type*} [MeasurableSpace α]

/-! ## The first round from which every event holds -/

/-- `T ω`, the first round from which `ω` belongs to every `G m`.  The junk value
`0` is returned when no such round exists; that case has measure zero in every
application, and the estimates below are stated so that it does no harm. -/
noncomputable def eventuallyIn (G : ℕ → Set α) (ω : α) : ℕ :=
  sInf {N : ℕ | ∀ n, N ≤ n → ω ∈ G n}

theorem eventuallyIn_le {G : ℕ → Set α} {ω : α} {N : ℕ}
    (h : ∀ n, N ≤ n → ω ∈ G n) : eventuallyIn G ω ≤ N :=
  Nat.sInf_le h

/-- Widening the events makes the settling time smaller — **provided the narrower
family does settle**.  The proviso is not decorative: `eventuallyIn` returns the
junk value `0` when its family never settles, so without it the inequality can
fail in the wrong direction on the non-settling set.  In the application that set
is null. -/
theorem eventuallyIn_mono {G G' : ℕ → Set α} {ω : α} (h : ∀ n, G n ⊆ G' n)
    (hne : ∃ N : ℕ, ∀ n, N ≤ n → ω ∈ G n) :
    eventuallyIn G' ω ≤ eventuallyIn G ω := by
  obtain ⟨N, hN⟩ := hne
  refine Nat.sInf_le fun n hn ↦ ?_
  exact h n (Nat.sInf_mem (⟨N, fun m hm ↦ hN m hm⟩ :
    {N : ℕ | ∀ n, N ≤ n → ω ∈ G n}.Nonempty) n hn)

theorem eventuallyIn_eq_zero {G : ℕ → Set α} {ω : α} (h : ∀ n, ω ∈ G n) :
    eventuallyIn G ω = 0 :=
  Nat.le_zero.mp (eventuallyIn_le fun n _ ↦ h n)

/-! ## The failure set -/

/-- The rounds at which `ω` fails the event. -/
def failureSet (G : ℕ → Set α) (ω : α) : Set ℕ := {m : ℕ | ω ∉ G m}

theorem eventuallyIn_le_of_bddAbove {G : ℕ → Set α} {ω : α}
    (hbdd : BddAbove (failureSet G ω)) (hne : (failureSet G ω).Nonempty) :
    eventuallyIn G ω ≤ sSup (failureSet G ω) + 1 := by
  refine eventuallyIn_le fun n hn ↦ ?_
  by_contra hcon
  have hmem : n ∈ failureSet G ω := hcon
  have : n ≤ sSup (failureSet G ω) := le_csSup hbdd hmem
  omega

/-! ## The pointwise estimate -/

/-- The weight `∑' m, (m + 1) · 1_{(G m)ᶜ}`, whose integral is
`∑' m, (m + 1) μ (G m)ᶜ`. -/
noncomputable def failureWeight (G : ℕ → Set α) (ω : α) : ℝ≥0∞ :=
  ∑' m : ℕ, ((m : ℝ≥0∞) + 1) * (G m)ᶜ.indicator (1 : α → ℝ≥0∞) ω

theorem le_failureWeight_of_mem {G : ℕ → Set α} {ω : α} {m : ℕ}
    (hm : ω ∉ G m) : ((m : ℝ≥0∞) + 1) ≤ failureWeight G ω := by
  have hterm : ((m : ℝ≥0∞) + 1) * (G m)ᶜ.indicator (1 : α → ℝ≥0∞) ω
      = (m : ℝ≥0∞) + 1 := by
    rw [Set.indicator_of_mem (by exact hm), Pi.one_apply, mul_one]
  rw [← hterm]
  exact ENNReal.le_tsum m

/-- If infinitely many events fail, the weight is infinite. -/
theorem failureWeight_eq_top_of_infinite {G : ℕ → Set α} {ω : α}
    (h : (failureSet G ω).Infinite) : failureWeight G ω = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← ENNReal.iSup_natCast]
  refine iSup_le fun N ↦ ?_
  obtain ⟨F, hFsub, hFcard⟩ := h.exists_subset_card_eq N
  have hsum : ∑ m ∈ F, ((m : ℝ≥0∞) + 1) * (G m)ᶜ.indicator (1 : α → ℝ≥0∞) ω
      ≤ failureWeight G ω := ENNReal.sum_le_tsum F
  refine le_trans ?_ hsum
  have hlb : ∀ m ∈ F,
      (1 : ℝ≥0∞) ≤ ((m : ℝ≥0∞) + 1) * (G m)ᶜ.indicator (1 : α → ℝ≥0∞) ω := by
    intro m hm
    have hmem : ω ∉ G m := hFsub hm
    rw [Set.indicator_of_mem (by exact hmem), Pi.one_apply, mul_one]
    exact le_add_self
  calc (N : ℝ≥0∞) = ∑ _m ∈ F, (1 : ℝ≥0∞) := by
        rw [Finset.sum_const, hFcard, nsmul_eq_mul, mul_one]
    _ ≤ _ := Finset.sum_le_sum hlb

/-- **The pointwise estimate.**  `T ω ≤ ∑' m, (m + 1) 1_{(G m)ᶜ}(ω)`. -/
theorem eventuallyIn_le_failureWeight (G : ℕ → Set α) (ω : α) :
    (eventuallyIn G ω : ℝ≥0∞) ≤ failureWeight G ω := by
  rcases (failureSet G ω).eq_empty_or_nonempty with hempty | hne
  · have hall : ∀ n, ω ∈ G n := by
      intro n
      by_contra hcon
      exact Set.eq_empty_iff_forall_notMem.mp hempty n hcon
    rw [eventuallyIn_eq_zero hall]
    simp
  · by_cases hbdd : BddAbove (failureSet G ω)
    · set m₀ : ℕ := sSup (failureSet G ω) with hm₀
      have hmem : m₀ ∈ failureSet G ω := Nat.sSup_mem hne hbdd
      have hT : eventuallyIn G ω ≤ m₀ + 1 := eventuallyIn_le_of_bddAbove hbdd hne
      calc (eventuallyIn G ω : ℝ≥0∞) ≤ ((m₀ + 1 : ℕ) : ℝ≥0∞) := by
            exact_mod_cast Nat.cast_le.mpr hT
        _ = (m₀ : ℝ≥0∞) + 1 := by push_cast; ring
        _ ≤ failureWeight G ω := le_failureWeight_of_mem hmem
    · have hinf : (failureSet G ω).Infinite := fun hfin ↦ hbdd hfin.bddAbove
      rw [failureWeight_eq_top_of_infinite hinf]
      exact le_top

/-! ## The integral estimate -/

/-- The integral of the weight. -/
theorem lintegral_failureWeight (G : ℕ → Set α) (hG : ∀ m, MeasurableSet (G m))
    (μ : Measure α) :
    ∫⁻ ω, failureWeight G ω ∂μ = ∑' m : ℕ, ((m : ℝ≥0∞) + 1) * μ (G m)ᶜ := by
  simp only [failureWeight]
  rw [MeasureTheory.lintegral_tsum]
  · refine tsum_congr fun m ↦ ?_
    have hmeas : Measurable ((G m)ᶜ.indicator (1 : α → ℝ≥0∞)) :=
      measurable_const.indicator (hG m).compl
    rw [MeasureTheory.lintegral_const_mul _ hmeas]
    congr 1
    rw [MeasureTheory.lintegral_indicator_one (hG m).compl]
  · intro m
    exact ((measurable_const.indicator (hG m).compl).const_mul _).aemeasurable

/-- **The integral estimate.**  `∫ T ≤ ∑' m, (m + 1) μ (G m)ᶜ`, with no
measurability assumption on `T` itself. -/
theorem lintegral_eventuallyIn_le (G : ℕ → Set α) (hG : ∀ m, MeasurableSet (G m))
    (μ : Measure α) :
    ∫⁻ ω, (eventuallyIn G ω : ℝ≥0∞) ∂μ ≤ ∑' m : ℕ, ((m : ℝ≥0∞) + 1) * μ (G m)ᶜ := by
  rw [← lintegral_failureWeight G hG μ]
  exact lintegral_mono fun ω ↦ eventuallyIn_le_failureWeight G ω

/-- **Integrability criterion.**  `T` is integrable as soon as the failure
probabilities are summable against the round index. -/
theorem lintegral_eventuallyIn_ne_top (G : ℕ → Set α) (hG : ∀ m, MeasurableSet (G m))
    (μ : Measure α) (hsum : ∑' m : ℕ, ((m : ℝ≥0∞) + 1) * μ (G m)ᶜ ≠ ⊤) :
    ∫⁻ ω, (eventuallyIn G ω : ℝ≥0∞) ∂μ ≠ ⊤ :=
  ne_top_of_le_ne_top hsum (lintegral_eventuallyIn_le G hG μ)

/-! ## A convenient sufficient condition: geometric decay

Concentration inequalities produce failure probabilities of the form
`C exp(-c m)`, or `C m^{-p}` with `p > 2`.  Both are summable against `m + 1`;
the first is packaged here because it is the shape the Chernoff analysis
produces. -/

/-- If `μ (G m)ᶜ ≤ C ρ^m` with `ρ < 1`, the failure weight is summable. -/
theorem tsum_lt_top_of_geometric {G : ℕ → Set α} {μ : Measure α} {C : ℝ≥0∞}
    (hC : C ≠ ⊤) {ρ : ℝ≥0} (hρ : ρ < 1)
    (hbd : ∀ m, μ (G m)ᶜ ≤ C * (ρ : ℝ≥0∞) ^ m) :
    ∑' m : ℕ, ((m : ℝ≥0∞) + 1) * μ (G m)ᶜ ≠ ⊤ := by
  have hmono : ∑' m : ℕ, ((m : ℝ≥0∞) + 1) * μ (G m)ᶜ
      ≤ ∑' m : ℕ, ((m : ℝ≥0∞) + 1) * (C * (ρ : ℝ≥0∞) ^ m) :=
    ENNReal.tsum_le_tsum fun m ↦ mul_le_mul_right (hbd m) _
  refine ne_top_of_le_ne_top ?_ hmono
  have hrw : ∀ m : ℕ, ((m : ℝ≥0∞) + 1) * (C * (ρ : ℝ≥0∞) ^ m)
      = C * (((m : ℝ≥0∞) + 1) * (ρ : ℝ≥0∞) ^ m) := by
    intro m; ring
  rw [tsum_congr hrw, ENNReal.tsum_mul_left]
  refine ENNReal.mul_ne_top hC ?_
  -- `∑ (m+1) ρ^m` converges for `ρ < 1`; do the arithmetic in `ℝ≥0`
  set f : ℕ → ℝ≥0 := fun m ↦ ((m : ℝ≥0) + 1) * ρ ^ m with hfdef
  have hcoe : ∀ m : ℕ, ((f m : ℝ≥0) : ℝ≥0∞) = ((m : ℝ≥0∞) + 1) * (ρ : ℝ≥0∞) ^ m := by
    intro m
    rw [hfdef]
    push_cast
    ring
  have hreal : Summable fun m : ℕ ↦ ((f m : ℝ≥0) : ℝ) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (ρ : ℝ))
      (by rw [Real.norm_eq_abs, abs_of_nonneg ρ.coe_nonneg]; exact_mod_cast hρ)
    have hgeo : Summable fun m : ℕ ↦ (ρ : ℝ) ^ m :=
      summable_geometric_of_lt_one ρ.coe_nonneg (by exact_mod_cast hρ)
    refine (h.add hgeo).congr fun m ↦ ?_
    rw [hfdef]
    push_cast
    ring
  have hsummable : Summable f := by rw [← NNReal.summable_coe]; exact hreal
  have hne := (ENNReal.tsum_coe_ne_top_iff_summable (f := f)).mpr hsummable
  rwa [tsum_congr hcoe] at hne

end BanditAlgorithm

theorem _root_.solution {α : Type*} [MeasurableSpace α] (G : ℕ → Set α)
    (hG : ∀ m, MeasurableSet (G m)) (μ : MeasureTheory.Measure α) :
    ∫⁻ ω, ((sInf {N : ℕ | ∀ n, N ≤ n → ω ∈ G n} : ℕ) : ℝ≥0∞) ∂μ
      ≤ ∑' m : ℕ, ((m : ℝ≥0∞) + 1) * μ (G m)ᶜ :=
  BanditAlgorithm.lintegral_eventuallyIn_le G hG μ
