-- Prove2me | solution 1 for GenEmpLik.Coverage.expansion_after_37
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:09:26.242025+00:00
-- url     : https://prove2.me/submissions/3871d17c-7e6d-4aee-8fe1-cd8e5df1f0b8

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_AssumptionA
import Definitions.Def_GenEmpLik_Coverage_AssumptionB
import Definitions.Def_GenEmpLik_Coverage_optimalValue
import Definitions.Def_GenEmpLik_Coverage_empiricalOptimalValue
import Definitions.Def_GenEmpLik_Coverage_divergenceBall
import Definitions.Def_GenEmpLik_Coverage_confidenceSet
import Definitions.Def_GenEmpLik_Coverage_influence
import Definitions.Def_GenEmpLik_Coverage_remainder
import Definitions.Def_GenEmpLik_Coverage_robustUpper
import Definitions.Def_GenEmpLik_Coverage_uniqueOptimizer
import Definitions.Def_VarianceRegularization_Expansion_empMean
import Definitions.Def_VarianceRegularization_Expansion_empVar
import Definitions.Def_GenEmpLik_Expansion_IsStationaryErgodic
import Definitions.Def_GenEmpLik_Expansion_robustMean
import Definitions.Def_GenEmpLik_Expansion_AssumptionA
import Theorems.Thm_GenEmpLik_Coverage_lemma_16
import Theorems.Thm_GenEmpLik_Expansion_lemma_1

open MeasureTheory ProbabilityTheory Filter Topology

namespace GEL3
open GenEmpLik.Coverage

lemma ereal_coe_sum {ι : Type*} (s : Finset ι) (r : ι → ℝ) :
    ((∑ i ∈ s, r i : ℝ) : EReal) = ∑ i ∈ s, (r i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

lemma f_nonneg (f : ℝ → EReal) (hA : AssumptionA f) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ f t := by
  obtain ⟨hφ, _, a, b, ha0, ha1, hb1, hcd, hd1, _⟩ := hA
  by_contra hneg0
  have hneg := not_le.mp hneg0
  set g : ℝ → ℝ := fun s => (f s).toReal with hg
  have hft_ne_bot := hφ.ne_bot t
  have hft_ne_top : f t ≠ ⊤ := fun h => by rw [h] at hneg; exact absurd hneg (not_lt.2 le_top)
  set c := (f t).toReal with hc_def
  have hfc : f t = (c : EReal) := (EReal.coe_toReal hft_ne_top hft_ne_bot).symm
  have hc : c < 0 := by rw [hfc] at hneg; exact_mod_cast hneg
  have hdiff : DifferentiableAt ℝ g 1 := by
    have := hcd.differentiableOn (by norm_num)
    exact (this 1 ⟨ha1, hb1⟩).differentiableAt (Ioo_mem_nhds ha1 hb1)
  have hder : HasDerivAt g 0 (1 + 0 * (t - 1)) := by
    have : HasDerivAt g (deriv g 1) 1 := hdiff.hasDerivAt
    rw [hd1] at this
    simpa using this
  have h1 : HasDerivAt (fun θ : ℝ => 1 + θ * (t - 1)) (t - 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (t - 1)).const_add 1
  have hcomp := hder.comp (0:ℝ) h1
  rw [zero_mul, hasDerivAt_iff_tendsto_slope] at hcomp
  have hlim : Tendsto (slope (g ∘ fun θ : ℝ => 1 + θ * (t - 1)) 0) (𝓝[>] 0) (𝓝 0) :=
    hcomp.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))
  have hle : ∀ᶠ θ in 𝓝[>] (0:ℝ), slope (g ∘ fun θ : ℝ => 1 + θ * (t - 1)) 0 θ ≤ c := by
    have : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [this] with θ hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hconv := hφ.convex t 1 θ ht zero_le_one hθ0.le hθ1.le
    rw [hφ.map_one, hfc, mul_zero, add_zero] at hconv
    have hs : θ * t + (1 - θ) * 1 = 1 + θ * (t - 1) := by ring
    rw [hs] at hconv
    have hpos : 0 < 1 + θ * (t - 1) := by nlinarith
    have hfs_bot := hφ.ne_bot (1 + θ * (t - 1))
    have hgle : g (1 + θ * (t - 1)) ≤ θ * c := by
      have := EReal.toReal_le_toReal hconv hfs_bot (by
        rw [← EReal.coe_mul]; exact EReal.coe_ne_top _)
      rw [← EReal.coe_mul, EReal.toReal_coe] at this
      exact this
    have hg1 : g (1 + 0 * (t - 1)) = 0 := by simp [hg, hφ.map_one]
    rw [slope_def_field]
    simp only [Function.comp, sub_zero]
    rw [hg1, sub_zero, div_le_iff₀ hθ0]
    linarith
  have := le_of_tendsto hlim hle
  linarith


lemma ball_iff (f : ℝ → EReal) (hA : AssumptionA f) (ρ : ℝ) (n : ℕ) (hn : 0 < n)
    (p : Fin n → ℝ) :
    p ∈ divergenceBall f ρ n ↔ 0 ≤ p ∧ ∑ i, p i = 1 ∧ (∀ i, f (n * p i) ≠ ⊤) ∧
      ∑ i, (f (n * p i)).toReal ≤ ρ := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hdiv : ∀ i, p i / (1 / (n:ℝ)) = n * p i := fun i => by field_simp
  simp only [divergenceBall, PhiDivRobust.Counterpart.probUncertaintySet,
    PhiDivRobust.Counterpart.phiDiv, Set.mem_setOf_eq, hdiv]
  constructor
  · rintro ⟨hp0, hp1, hD⟩
    have hterm : ∀ i, 0 ≤ ((1 / (n:ℝ) : ℝ) : EReal) * f (n * p i) := fun i =>
      EReal.mul_nonneg (by exact_mod_cast (by positivity : (0:ℝ) ≤ 1 / n))
        (f_nonneg f hA _ (mul_nonneg hnR.le (hp0 i)))
    have htop : ∀ i, f (n * p i) ≠ ⊤ := by
      intro j hj
      have h1 := Finset.single_le_sum (fun i _ => hterm i) (Finset.mem_univ j)
      rw [hj, EReal.coe_mul_top_of_pos (by positivity)] at h1
      have := h1.trans hD
      exact EReal.coe_ne_top _ (top_le_iff.mp this)
    refine ⟨hp0, hp1, htop, ?_⟩
    have hfin : ∀ i, f (n * p i) = ((f (n * p i)).toReal : EReal) := fun i =>
      (EReal.coe_toReal (htop i) (hA.1.ne_bot _)).symm
    have : ∑ i, ((1 / (n:ℝ) : ℝ) : EReal) * f (n * p i) =
        ((∑ i, 1 / (n:ℝ) * (f (n * p i)).toReal : ℝ) : EReal) := by
      rw [ereal_coe_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hfin i, EReal.toReal_coe, ← EReal.coe_mul]
    rw [this] at hD
    have hD' : ∑ i, 1 / (n:ℝ) * (f (n * p i)).toReal ≤ ρ / n := by exact_mod_cast hD
    rw [← Finset.mul_sum] at hD'
    rw [div_eq_mul_inv, one_mul, div_eq_mul_inv, mul_comm ρ] at hD'
    exact le_of_mul_le_mul_left hD' (by positivity)
  · rintro ⟨hp0, hp1, htop, hsum⟩
    refine ⟨hp0, hp1, ?_⟩
    have hfin : ∀ i, f (n * p i) = ((f (n * p i)).toReal : EReal) := fun i =>
      (EReal.coe_toReal (htop i) (hA.1.ne_bot _)).symm
    have : ∑ i, ((1 / (n:ℝ) : ℝ) : EReal) * f (n * p i) =
        ((∑ i, 1 / (n:ℝ) * (f (n * p i)).toReal : ℝ) : EReal) := by
      rw [ereal_coe_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hfin i, EReal.toReal_coe, ← EReal.coe_mul]
    rw [this]
    have : ∑ i, 1 / (n:ℝ) * (f (n * p i)).toReal ≤ ρ / n := by
      rw [← Finset.mul_sum, div_eq_mul_inv ρ, one_div, mul_comm ρ]
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    exact_mod_cast this


lemma ball_nonempty (f : ℝ → EReal) (hA : AssumptionA f) (ρ : ℝ) (hρ : 0 ≤ ρ) (n : ℕ)
    (hn : 0 < n) : (fun _ : Fin n => (1:ℝ) / n) ∈ divergenceBall f ρ n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  rw [ball_iff f hA ρ n hn]
  have h1 : (n:ℝ) * (1 / n) = 1 := by field_simp
  refine ⟨fun i => by simp only [Pi.zero_apply]; positivity, ?_, ?_, ?_⟩
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  · intro i; rw [h1, hA.1.map_one]; exact EReal.zero_ne_top
  · simp only [h1, hA.1.map_one, EReal.toReal_zero, Finset.sum_const_zero]; exact hρ

lemma ball_convex (f : ℝ → EReal) (hA : AssumptionA f) (ρ : ℝ) (n : ℕ) (hn : 0 < n) :
    Convex ℝ (divergenceBall f ρ n) := by
  intro p hp q hq a b ha hb hab
  rw [ball_iff f hA ρ n hn] at hp hq ⊢
  obtain ⟨hp0, hp1, hpt, hps⟩ := hp
  obtain ⟨hq0, hq1, hqt, hqs⟩ := hq
  have hb' : b = 1 - a := by linarith
  subst hb'
  have key : ∀ i, f (n * (a • p + (1 - a) • q) i) ≤
      ((a * (f (n * p i)).toReal + (1 - a) * (f (n * q i)).toReal : ℝ) : EReal) := by
    intro i
    have hc := hA.1.convex (n * p i) (n * q i) a (mul_nonneg (Nat.cast_nonneg _) (hp0 i))
      (mul_nonneg (Nat.cast_nonneg _) (hq0 i)) ha (by linarith)
    have he : (n:ℝ) * (a • p + (1 - a) • q) i = a * (n * p i) + (1 - a) * (n * q i) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [he]
    refine hc.trans (le_of_eq ?_)
    rw [← EReal.coe_toReal (hpt i) (hA.1.ne_bot _), ← EReal.coe_toReal (hqt i) (hA.1.ne_bot _)]
    simp only [EReal.toReal_coe]
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  have hfin : ∀ i, f (n * (a • p + (1 - a) • q) i) ≠ ⊤ := fun i h => by
    have := key i; rw [h] at this; exact EReal.coe_ne_top _ (top_le_iff.mp this)
  refine ⟨?_, ?_, hfin, ?_⟩
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact add_nonneg (mul_nonneg ha (hp0 i)) (mul_nonneg hb (hq0 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp1, hq1]; ring
  · have hle : ∀ i, (f (n * (a • p + (1 - a) • q) i)).toReal ≤
        a * (f (n * p i)).toReal + (1 - a) * (f (n * q i)).toReal := fun i => by
      have := EReal.toReal_le_toReal (key i) (hA.1.ne_bot _) (EReal.coe_ne_top _)
      rwa [EReal.toReal_coe] at this
    calc ∑ i, (f (n * (a • p + (1 - a) • q) i)).toReal
        ≤ ∑ i, (a * (f (n * p i)).toReal + (1 - a) * (f (n * q i)).toReal) :=
          Finset.sum_le_sum (fun i _ => hle i)
      _ = a * ∑ i, (f (n * p i)).toReal + (1 - a) * ∑ i, (f (n * q i)).toReal := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ a * ρ + (1 - a) * ρ := by
          gcongr
      _ = ρ := by ring

lemma ball_isClosed (f : ℝ → EReal) (hA : AssumptionA f) (ρ : ℝ) (n : ℕ) (hn : 0 < n) :
    IsClosed (divergenceBall f ρ n) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  rw [← isSeqClosed_iff_isClosed]
  intro x p hx hxp
  have hx' := fun k => (ball_iff f hA ρ n hn (x k)).1 (hx k)
  rw [ball_iff f hA ρ n hn]
  have hcoord : ∀ i, Tendsto (fun k => x k i) atTop (𝓝 (p i)) := fun i =>
    (continuous_apply i).continuousAt.tendsto.comp hxp
  have hp0 : 0 ≤ p := fun i => ge_of_tendsto (hcoord i) (Eventually.of_forall fun k => (hx' k).1 i)
  have hp1 : ∑ i, p i = 1 := by
    have : Tendsto (fun k => ∑ i, x k i) atTop (𝓝 (∑ i, p i)) := tendsto_finset_sum _ (fun i _ => hcoord i)
    exact tendsto_nhds_unique this (by simp only [fun k => (hx' k).2.1]; exact tendsto_const_nhds)
  -- eventual lower bounds from lsc
  have hlsc : ∀ i, ∀ y : EReal, y < f (n * p i) → ∀ᶠ k in atTop, y < f (n * x k i) := by
    intro i y hy
    have h := hA.2.1 (n * p i) (mul_nonneg hnR.le (hp0 i)) y hy
    have ht : Tendsto (fun k => (n:ℝ) * x k i) atTop (𝓝[Set.Ici 0] (n * p i)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨((hcoord i).const_mul _), Eventually.of_forall fun k => ?_⟩
      exact mul_nonneg hnR.le ((hx' k).1 i)
    exact ht.eventually h
  -- each term bounded by ρ
  have hterm_le : ∀ k i, (f (n * x k i)).toReal ≤ ρ := by
    intro k i
    refine le_trans ?_ (hx' k).2.2.2
    exact Finset.single_le_sum (f := fun j => (f (n * x k j)).toReal)
      (fun j _ => EReal.toReal_nonneg (f_nonneg f hA _ (mul_nonneg hnR.le ((hx' k).1 j))))
      (Finset.mem_univ i)
  have hpt : ∀ i, f (n * p i) ≠ ⊤ := by
    intro i htop
    have := (hlsc i ((ρ + 1 : ℝ) : EReal) (by rw [htop]; exact EReal.coe_lt_top _)).exists
    obtain ⟨k, hk⟩ := this
    rw [← EReal.coe_toReal ((hx' k).2.2.1 i) (hA.1.ne_bot _)] at hk
    have := EReal.coe_lt_coe_iff.1 hk
    linarith [hterm_le k i]
  refine ⟨hp0, hp1, hpt, ?_⟩
  by_contra hcon
  have hgt := not_le.mp hcon
  set S := ∑ i, (f (n * p i)).toReal
  set ε := (S - ρ) / n with hε
  have hεpos : 0 < ε := div_pos (by linarith) hnR
  have hev : ∀ᶠ k in atTop, ∀ i, (f (n * p i)).toReal - ε < (f (n * x k i)).toReal := by
    rw [Filter.eventually_all]
    intro i
    have := hlsc i (((f (n * p i)).toReal - ε : ℝ) : EReal) (by
      rw [← EReal.coe_toReal (hpt i) (hA.1.ne_bot _)]
      simp only [EReal.toReal_coe]
      exact EReal.coe_lt_coe_iff.2 (by linarith))
    filter_upwards [this] with k hk
    rw [← EReal.coe_toReal ((hx' k).2.2.1 i) (hA.1.ne_bot _)] at hk
    exact EReal.coe_lt_coe_iff.1 hk
  obtain ⟨k, hk⟩ := hev.exists
  have hsum : ∑ i, ((f (n * p i)).toReal - ε) < ∑ i, (f (n * x k i)).toReal :=
    Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 ⟨⟨0, hn⟩⟩) (fun i _ => hk i)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, hε, mul_div_cancel₀ _ hnR.ne'] at hsum
  linarith [(hx' k).2.2.2]

lemma ball_isCompact (f : ℝ → EReal) (hA : AssumptionA f) (ρ : ℝ) (n : ℕ) (hn : 0 < n) :
    IsCompact (divergenceBall f ρ n) := by
  refine (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc (a := (0:ℝ)) (b := 1))).of_isClosed_subset
    (ball_isClosed f hA ρ n hn) ?_
  intro p hp
  rw [ball_iff f hA ρ n hn] at hp
  obtain ⟨hp0, hp1, -, -⟩ := hp
  intro i _
  refine ⟨hp0 i, ?_⟩
  rw [← hp1]
  exact Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i)


lemma sInf_image_eq_iInf {α : Type*} [TopologicalSpace α] {S D : Set α} {F : α → ℝ}
    (hS : IsCompact S) (hSne : S.Nonempty) (hF : ContinuousOn F S) (hDS : D ⊆ S)
    (hdense : S ⊆ closure D) : sInf (F '' S) = ⨅ d : D, F d := by
  have hbdd : BddBelow (F '' S) := (hS.image_of_continuousOn hF).bddBelow
  have hDne : D.Nonempty := by
    obtain ⟨x, hx⟩ := hSne; exact closure_nonempty_iff.1 ⟨x, hdense hx⟩
  show sInf (F '' S) = sInf (Set.range fun d : D => F d)
  rw [← Set.image_eq_range]
  apply le_antisymm
  · exact csInf_le_csInf hbdd (hDne.image F) (Set.image_mono hDS)
  · refine le_csInf (hSne.image F) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ContinuousWithinAt.closure_le (f := fun _ => sInf (F '' D)) (g := F) (hdense hx)
      continuousWithinAt_const ((hF x hx).mono hDS)
      (fun y hy => csInf_le (hbdd.mono (Set.image_mono hDS)) ⟨y, hy, rfl⟩)

lemma sSup_image_eq_iSup {α : Type*} [TopologicalSpace α] {S D : Set α} {F : α → ℝ}
    (hS : IsCompact S) (hSne : S.Nonempty) (hF : ContinuousOn F S) (hDS : D ⊆ S)
    (hdense : S ⊆ closure D) : sSup (F '' S) = ⨆ d : D, F d := by
  have hbdd : BddAbove (F '' S) := (hS.image_of_continuousOn hF).bddAbove
  have hDne : D.Nonempty := by
    obtain ⟨x, hx⟩ := hSne; exact closure_nonempty_iff.1 ⟨x, hdense hx⟩
  show sSup (F '' S) = sSup (Set.range fun d : D => F d)
  rw [← Set.image_eq_range]
  apply le_antisymm
  · refine csSup_le (hSne.image F) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ContinuousWithinAt.closure_le (g := fun _ => sSup (F '' D)) (f := F) (hdense hx)
      ((hF x hx).mono hDS) continuousWithinAt_const
      (fun y hy => le_csSup (hbdd.mono (Set.image_mono hDS)) ⟨y, hy, rfl⟩)
  · exact csSup_le_csSup hbdd (hDne.image F) (Set.image_mono hDS)

lemma exists_countable_dense {α : Type*} [TopologicalSpace α] [SecondCountableTopology α]
    [TopologicalSpace.PseudoMetrizableSpace α] (S : Set α) :
    ∃ D : Set α, D ⊆ S ∧ D.Countable ∧ S ⊆ closure D :=
  (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset

section Loss
variable {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {X : Set (EuclideanSpace ℝ (Fin d))}
  {ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ} {M : Ξ → ℝ}

lemma loss_contOn (hB : AssumptionB X ℓ M) (w : Ξ) : ContinuousOn (fun x => ℓ x w) X := by
  have : LipschitzOnWith ⟨M w, hB.2.2.1 w⟩ (fun x => ℓ x w) X := by
    refine LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)
    rw [Real.dist_eq, dist_eq_norm]
    exact hB.2.2.2 w x hx y hy
  exact this.continuousOn

lemma wsum_contOn (hB : AssumptionB X ℓ M) {n : ℕ} (z : Fin n → Ξ) (p : Fin n → ℝ) :
    ContinuousOn (fun x => ∑ i, p i * ℓ x (z i)) X :=
  continuousOn_finset_sum _ (fun i _ => continuousOn_const.mul (loss_contOn hB (z i)))

lemma G_lip (hB : AssumptionB X ℓ M) (hX : X.Nonempty) {n : ℕ} (z : Fin n → Ξ) :
    ∃ K : ℝ, ∀ p q : Fin n → ℝ,
      empiricalOptimalValue X ℓ z p ≤ empiricalOptimalValue X ℓ z q + K * dist p q := by
  have hcont : ContinuousOn (fun x => (fun i => ℓ x (z i))) X :=
    continuousOn_pi.2 (fun i => loss_contOn hB (z i))
  obtain ⟨C, hC⟩ := hB.1.exists_bound_of_continuousOn hcont
  have hCi : ∀ x ∈ X, ∀ i, |ℓ x (z i)| ≤ C := fun x hx i =>
    (norm_le_pi_norm (fun i => ℓ x (z i)) i).trans (hC x hx)
  refine ⟨n * C, fun p q => ?_⟩
  have hbdd : ∀ r : Fin n → ℝ, BddBelow ((fun x => ∑ i, r i * ℓ x (z i)) '' X) := fun r =>
    (hB.1.image_of_continuousOn (wsum_contOn hB z r)).bddBelow
  unfold empiricalOptimalValue
  have : sInf ((fun x => ∑ i, p i * ℓ x (z i)) '' X) - n * C * dist p q ≤
      sInf ((fun x => ∑ i, q i * ℓ x (z i)) '' X) := by
    refine le_csInf (hX.image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    have h1 : sInf ((fun x => ∑ i, p i * ℓ x (z i)) '' X) ≤ ∑ i, p i * ℓ x (z i) :=
      csInf_le (hbdd p) ⟨x, hx, rfl⟩
    have h2 : ∑ i, p i * ℓ x (z i) - ∑ i, q i * ℓ x (z i) ≤ n * C * dist p q := by
      rw [← Finset.sum_sub_distrib]
      calc ∑ i, (p i * ℓ x (z i) - q i * ℓ x (z i))
          ≤ ∑ _i : Fin n, C * dist p q := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            have hd : |p i - q i| ≤ dist p q := by
              rw [← Real.dist_eq]; exact dist_le_pi_dist p q i
            calc p i * ℓ x (z i) - q i * ℓ x (z i) = (p i - q i) * ℓ x (z i) := by ring
              _ ≤ |(p i - q i) * ℓ x (z i)| := le_abs_self _
              _ = |p i - q i| * |ℓ x (z i)| := abs_mul _ _
              _ ≤ dist p q * C := mul_le_mul hd (hCi x hx i) (abs_nonneg _) dist_nonneg
              _ = C * dist p q := mul_comm _ _
        _ = n * C * dist p q := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    linarith
  linarith

lemma G_cont (hB : AssumptionB X ℓ M) (hX : X.Nonempty) {n : ℕ} (z : Fin n → Ξ) :
    Continuous (fun p => empiricalOptimalValue X ℓ z p) := by
  obtain ⟨K, hK⟩ := G_lip hB hX z
  exact (LipschitzWith.of_le_add_mul' K hK).continuous

end Loss


lemma assumptionA_conv (f : ℝ → EReal) (hA : AssumptionA f) : GenEmpLik.Expansion.AssumptionA f := by
  obtain ⟨hφ, hlsc, a, b, ha0, ha1, hb1, hcd, hd1, hd2⟩ := hA
  have hU : IsOpen (Set.Ioo a b) := isOpen_Ioo
  have h1 : ContDiffOn ℝ 2 (deriv (fun t : ℝ => (f t).toReal)) (Set.Ioo a b) :=
    hcd.deriv_of_isOpen hU (by norm_num)
  have h2 : ContDiffOn ℝ 1 (deriv (deriv (fun t : ℝ => (f t).toReal))) (Set.Ioo a b) :=
    h1.deriv_of_isOpen hU (by norm_num)
  refine ⟨hφ, hlsc, a, b, ha0, ha1, hb1, hcd.differentiableOn (by norm_num),
    h1.differentiableOn (by norm_num), h2.differentiableOn (by norm_num), hd1, ?_⟩
  rw [← hd2, iteratedDeriv_succ, iteratedDeriv_one]

lemma linear_cont {n : ℕ} (c : Fin n → ℝ) : Continuous (fun p : Fin n → ℝ => ∑ i, p i * c i) :=
  continuous_finset_sum _ (fun i _ => (continuous_apply i).mul continuous_const)

lemma robustMean_measurable {Ω : Type*} [MeasurableSpace Ω] (f : ℝ → EReal) (hA : AssumptionA f)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (Z : ℕ → Ω → ℝ) (hZ : ∀ i, Measurable (Z i)) (n : ℕ) :
    Measurable (fun ω => GenEmpLik.Expansion.robustMean f ρ (fun i : Fin n => Z i ω)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : (fun ω => GenEmpLik.Expansion.robustMean f ρ (fun i : Fin 0 => Z i ω)) =
        fun _ => GenEmpLik.Expansion.robustMean f ρ (fun _ : Fin 0 => (0:ℝ)) := by
      funext ω; congr 1; funext i; exact i.elim0
    rw [this]; exact measurable_const
  have hBc := ball_isCompact f hA ρ n hn
  have hBne : (divergenceBall f ρ n).Nonempty := ⟨_, ball_nonempty f hA ρ hρ n hn⟩
  obtain ⟨E, hEB, hEc, hEdense⟩ := exists_countable_dense (divergenceBall f ρ n)
  have : Countable E := hEc.to_subtype
  have : (fun ω => GenEmpLik.Expansion.robustMean f ρ (fun i : Fin n => Z i ω)) =
      fun ω => ⨆ e : E, ∑ i, (e : Fin n → ℝ) i * Z i ω := by
    funext ω
    exact sSup_image_eq_iSup hBc hBne (linear_cont _).continuousOn hEB hEdense
  rw [this]
  exact Measurable.iSup (fun e => Finset.measurable_sum _ (fun i _ => (hZ i).const_mul _))

/-- Deterministic sandwich: the robust optimal value differs from `T0` plus the robust mean of the
influence values by at most the supremum of the linearization remainder. -/
lemma sup_sandwich {d n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {X : Set (EuclideanSpace ℝ (Fin d))}
    {ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ} {M : Ξ → ℝ} (hB : AssumptionB X ℓ M) (hX : X.Nonempty)
    (f : ℝ → EReal) (hA : AssumptionA f) (ρ : ℝ) (hρ : 0 ≤ ρ) (hn : 0 < n)
    (P₀ : Measure Ξ) (xs : EuclideanSpace ℝ (Fin d)) (z : Fin n → Ξ) :
    |robustUpper X ℓ f ρ z - optimalValue X ℓ P₀ -
      GenEmpLik.Expansion.robustMean f ρ (fun i => influence ℓ xs P₀ (z i))| ≤
      sSup ((fun p => |remainder X ℓ P₀ xs z p|) '' divergenceBall f ρ n) := by
  set B := divergenceBall f ρ n
  have hBc := ball_isCompact f hA ρ n hn
  have hBne : B.Nonempty := ⟨_, ball_nonempty f hA ρ hρ n hn⟩
  set c : Fin n → ℝ := fun i => influence ℓ xs P₀ (z i)
  set G := fun p => empiricalOptimalValue X ℓ z p
  set L := fun p : Fin n → ℝ => ∑ i, p i * c i
  set T0 := optimalValue X ℓ P₀
  have hG : Continuous G := G_cont hB hX z
  have hL : Continuous L := linear_cont c
  have hk : ∀ p, remainder X ℓ P₀ xs z p = G p - T0 - L p := fun p => rfl
  have hK : Continuous (fun p => |remainder X ℓ P₀ xs z p|) := by
    simp only [hk]; exact ((hG.sub continuous_const).sub hL).abs
  have bG : BddAbove (G '' B) := (hBc.image hG).bddAbove
  have bL : BddAbove (L '' B) := (hBc.image hL).bddAbove
  have bK : BddAbove ((fun p => |remainder X ℓ P₀ xs z p|) '' B) := (hBc.image hK).bddAbove
  set K := sSup ((fun p => |remainder X ℓ P₀ xs z p|) '' B)
  have hKp : ∀ p ∈ B, |G p - T0 - L p| ≤ K := fun p hp => by
    rw [← hk]; exact le_csSup bK ⟨p, hp, rfl⟩
  have hu : robustUpper X ℓ f ρ z = sSup (G '' B) := rfl
  have hr : GenEmpLik.Expansion.robustMean f ρ c = sSup (L '' B) := rfl
  rw [hu, hr, abs_le]
  constructor
  · -- sSup L ≤ sSup G - T0 + K
    have : sSup (L '' B) ≤ sSup (G '' B) - T0 + K := by
      refine csSup_le (hBne.image L) ?_
      rintro _ ⟨p, hp, rfl⟩
      have h1 := hKp p hp
      have h2 : G p ≤ sSup (G '' B) := le_csSup bG ⟨p, hp, rfl⟩
      rw [abs_le] at h1
      linarith [h1.1]
    linarith
  · have : sSup (G '' B) ≤ T0 + sSup (L '' B) + K := by
      refine csSup_le (hBne.image G) ?_
      rintro _ ⟨p, hp, rfl⟩
      have h1 := hKp p hp
      have h2 : L p ≤ sSup (L '' B) := le_csSup bL ⟨p, hp, rfl⟩
      rw [abs_le] at h1
      linarith [h1.2]
    linarith

end GEL3

namespace GEL3c
open GenEmpLik.Expansion

lemma seqShift_iterate (n : ℕ) (s : ℕ → ℝ) : seqShift^[n] s = fun k => s (k + n) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    funext k; simp only [seqShift]; congr 1

lemma iid_isStationaryErgodic {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ) (hm : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (hid : ∀ i, IdentDistrib (Z i) (Z 0) P P) :
    IsStationaryErgodic Z P := by
  refine ⟨hm, ?_⟩
  have hpath : Measurable (fun ω k => Z k ω) := measurable_pi_lambda _ hm
  have hshift : Measurable seqShift := measurable_pi_lambda _ (fun k => measurable_pi_apply (k + 1))
  have hlaw : P.map (fun ω k => Z k ω) = Measure.infinitePi (fun _ : ℕ => P.map (Z 0)) := by
    rw [hind.map_fun_eq_infinitePi_map₀ hpath.aemeasurable]
    congr 1; funext i; exact (hid i).map_eq
  refine ⟨⟨hshift, ?_⟩, ⟨?_⟩⟩
  · have hind' : iIndepFun (fun k => Z (k + 1)) P :=
      hind.precomp (g := fun k => k + 1) (fun a b h => by simpa using h)
    have hpath' : Measurable (fun ω k => Z (k + 1) ω) := measurable_pi_lambda _ (fun k => hm _)
    rw [Measure.map_map hshift hpath]
    have : seqShift ∘ (fun ω k => Z k ω) = fun ω k => Z (k + 1) ω := rfl
    rw [this, hind'.map_fun_eq_infinitePi_map₀ hpath'.aemeasurable, hlaw]
    congr 1; funext i; exact (hid (i + 1)).map_eq
  · intro S hS hinv
    rw [eventuallyConst_set]
    set s : ℕ → MeasurableSpace Ω := fun n => MeasurableSpace.comap (Z n) inferInstance
    have h_le : ∀ n, s n ≤ ‹MeasurableSpace Ω› := fun n => (hm n).comap_le
    have h_indep : iIndep s P := (iIndepFun_iff_iIndep _ Z P).1 hind
    have htail : MeasurableSet[limsup s atTop] ((fun ω k => Z k ω) ⁻¹' S) := by
      rw [limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
      intro n
      have hfix : seqShift^[n] ⁻¹' S = S := Function.IsFixedPt.preimage_iterate hinv n
      have heq : (fun ω k => Z k ω) ⁻¹' S = (fun ω k => Z (k + n) ω) ⁻¹' S := by
        conv_lhs => rw [← hfix]
        ext ω
        simp only [Set.mem_preimage, seqShift_iterate]
      rw [heq]
      have hmeas : Measurable[⨆ i ≥ n, s i] (fun ω k => Z (k + n) ω) := by
        refine @measurable_pi_lambda Ω ℕ (fun _ => ℝ) (⨆ i ≥ n, s i) _ _ (fun k => ?_)
        have h1 : Measurable[s (k + n)] (Z (k + n)) := comap_measurable (Z (k + n))
        exact h1.mono (le_iSup₂ (f := fun i (_ : i ≥ n) => s i) (k + n) (by omega)) le_rfl
      exact hmeas hS
    have h01 := measure_zero_or_one_of_measurableSet_limsup_atTop h_le h_indep htail
    have hmap : (P.map (fun ω k => Z k ω)) S = P ((fun ω k => Z k ω) ⁻¹' S) :=
      Measure.map_apply hpath hS
    have : IsProbabilityMeasure (P.map (fun ω k => Z k ω)) :=
      Measure.isProbabilityMeasure_map hpath.aemeasurable
    rcases h01 with h0 | h1
    · right
      rw [← hmap] at h0
      exact measure_eq_zero_iff_ae_notMem.1 h0
    · left
      rw [← hmap] at h1
      rw [ae_iff]
      have := prob_compl_eq_zero_iff hS |>.2 h1
      simpa [Set.compl_def] using this

end GEL3c

open GenEmpLik.Coverage GEL3 GEL3c VarianceRegularization.Expansion

theorem solution
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Ξ) (d : ℕ)
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (M : Ξ → ℝ) (f : ℝ → EReal) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hA : AssumptionA f)
    (hX : X.Nonempty) (hB : AssumptionB X ℓ M)
    (hℓmeas : ∀ x, Measurable (ℓ x))
    (hM2 : Integrable (fun z => M z ^ 2) (μ.map (ξ 0)))
    (hℓ2 : ∃ x0 ∈ X, Integrable (fun z => ℓ x0 z ^ 2) (μ.map (ξ 0)))
    (hξmeas : ∀ i, Measurable (ξ i))
    (hξindep : iIndepFun ξ μ)
    (hξident : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ)
    (hunique : HasUniqueOptimizer X ℓ (μ.map (ξ 0)))
    (hvar : 0 < variance (ℓ (uniqueOptimizer X ℓ (μ.map (ξ 0)) hunique))
      (μ.map (ξ 0))) :
    ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n : ℕ => μ {ω |
        δ < |Real.sqrt (n : ℝ) *
            (robustUpper X ℓ f ρ (fun i : Fin n => ξ i ω) -
              optimalValue X ℓ (μ.map (ξ 0))) -
          Real.sqrt (n : ℝ) *
            VarianceRegularization.Expansion.empMean
              (fun i : Fin n => influence ℓ
                (uniqueOptimizer X ℓ (μ.map (ξ 0)) hunique)
                (μ.map (ξ 0)) (ξ i ω)) -
          Real.sqrt (ρ * VarianceRegularization.Expansion.empVar
              (fun i : Fin n => influence ℓ
                (uniqueOptimizer X ℓ (μ.map (ξ 0)) hunique)
                (μ.map (ξ 0)) (ξ i ω)))|}) atTop (𝓝 0) := by
  intro δ hδ
  have h16 := lemma_16 μ ξ d X ℓ M f ρ hρ hA hX hB hℓmeas hM2 hℓ2 hξmeas hξindep
    hξident hunique hvar (δ / 2) (by positivity)
  set xs := uniqueOptimizer X ℓ (μ.map (ξ 0)) hunique with hxs
  set T0 := optimalValue X ℓ (μ.map (ξ 0)) with hT0
  set Z : ℕ → Ω → ℝ := fun k ω => influence ℓ xs (μ.map (ξ 0)) (ξ k ω) with hZ
  have hZm : ∀ k, Measurable (Z k) := fun k =>
    ((hℓmeas xs).comp (hξmeas k)).sub_const _
  have hgm : Measurable (fun z => influence ℓ xs (μ.map (ξ 0)) z) := (hℓmeas xs).sub_const _
  have hZindep : iIndepFun Z μ := hξindep.comp (fun _ => _) (fun _ => hgm)
  have hZident : ∀ k, IdentDistrib (Z k) (Z 0) μ μ := fun k => (hξident k).comp hgm
  have hSE := iid_isStationaryErgodic μ Z hZm hZindep hZident
  have hmem : MemLp (ℓ xs) 2 (μ.map (ξ 0)) :=
    memLp_two_of_variance_ne_zero (hℓmeas xs).aestronglyMeasurable hvar.ne'
  have hmem' : MemLp (ℓ xs ∘ ξ 0) 2 μ :=
    (memLp_map_measure_iff (hℓmeas xs).aestronglyMeasurable (hξmeas 0).aemeasurable).1 hmem
  have hZ2 : Integrable (fun ω => Z 0 ω ^ 2) μ := by
    have := (hmem'.sub (memLp_const (∫ z', ℓ xs z' ∂(μ.map (ξ 0))))).integrable_sq
    simpa [hZ, influence] using this
  have h1 := GenEmpLik.Expansion.lemma_1 (P := μ) f (assumptionA_conv f hA) hρ Z hSE hZ2
  -- the a.s. term, in measure
  set Bn : ℕ → Ω → ℝ := fun n ω => Real.sqrt n *
      |GenEmpLik.Expansion.robustMean f ρ (fun i : Fin n => Z i ω) -
        empMean (fun i : Fin n => Z i ω) - Real.sqrt (ρ / n * empVar (fun i : Fin n => Z i ω))|
    with hBn
  have hBnm : ∀ n, Measurable (Bn n) := by
    intro n
    have hmean : Measurable (fun ω => empMean (fun i : Fin n => Z i ω)) :=
      measurable_const.mul (Finset.measurable_sum _ fun i _ => hZm i)
    have hsq : Measurable (fun ω => ∑ i : Fin n, Z i ω ^ 2) :=
      Finset.measurable_sum _ fun i _ => (hZm i).pow_const 2
    have hv : Measurable (fun ω => empVar (fun i : Fin n => Z i ω)) := by
      unfold empVar
      exact (hsq.const_mul _).sub (hmean.pow_const 2)
    exact measurable_const.mul
      ((((robustMean_measurable f hA ρ hρ Z hZm n).sub hmean).sub
        (measurable_const.mul hv).sqrt).abs)
  have hBnlim : TendstoInMeasure μ Bn atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hBnm n).aestronglyMeasurable) h1
  have hT2 : Tendsto (fun n : ℕ => μ {ω | δ / 2 ≤ Bn n ω}) atTop (𝓝 0) := by
    have := (tendstoInMeasure_iff_dist.1 hBnlim) (δ / 2) (by positivity)
    refine this.congr (fun n => ?_)
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero]
    rw [abs_of_nonneg (show 0 ≤ Bn n ω from mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))]
  have hT1 : Tendsto (fun n : ℕ => μ {ω | δ / 2 / Real.sqrt n ≤
      sSup ((fun p => |remainder X ℓ (μ.map (ξ 0)) xs (fun i : Fin n => ξ i ω) p|) ''
        divergenceBall f ρ n)}) atTop (𝓝 0) :=
    tendsto_of_le_liminf_of_limsup_le bot_le h16.le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by
      simpa using hT1.add hT2) (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hsand := sup_sandwich hB hX f hA ρ hρ hn (μ.map (ξ 0)) xs (fun i : Fin n => ξ i ω)
  set K := sSup ((fun p => |remainder X ℓ (μ.map (ξ 0)) xs (fun i : Fin n => ξ i ω) p|) ''
        divergenceBall f ρ n)
  set rm := GenEmpLik.Expansion.robustMean f ρ (fun i : Fin n => Z i ω)
  set u := robustUpper X ℓ f ρ (fun i : Fin n => ξ i ω)
  set mn := empMean (fun i : Fin n => Z i ω)
  set vn := empVar (fun i : Fin n => Z i ω)
  have hsq : Real.sqrt n * Real.sqrt (ρ / n * vn) = Real.sqrt (ρ * vn) := by
    rw [← Real.sqrt_mul hnR.le]; congr 1; field_simp
  have hdecomp : Real.sqrt n * (u - T0) - Real.sqrt n * mn - Real.sqrt (ρ * vn) =
      Real.sqrt n * (u - T0 - rm) + Real.sqrt n * (rm - mn - Real.sqrt (ρ / n * vn)) := by
    rw [← hsq]; ring
  change δ < |Real.sqrt n * (u - T0) - Real.sqrt n * mn - Real.sqrt (ρ * vn)| at hω
  rw [hdecomp] at hω
  by_contra hcon
  push Not at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  have hc1' : Real.sqrt n * K < δ / 2 := by
    rw [lt_div_iff₀ hs] at hc1; linarith
  have e1 : |Real.sqrt n * (u - T0 - rm)| ≤ Real.sqrt n * K := by
    rw [abs_mul, abs_of_pos hs]; exact mul_le_mul_of_nonneg_left hsand hs.le
  have e2 : |Real.sqrt n * (rm - mn - Real.sqrt (ρ / n * vn))| = Bn n ω := by
    rw [abs_mul, abs_of_pos hs]
  have := abs_add_le (Real.sqrt n * (u - T0 - rm)) (Real.sqrt n * (rm - mn - Real.sqrt (ρ / n * vn)))
  linarith
