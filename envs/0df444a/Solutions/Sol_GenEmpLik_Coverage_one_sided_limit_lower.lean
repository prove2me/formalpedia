-- Prove2me | solution 1 for GenEmpLik.Coverage.one_sided_limit_lower
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:03:18.861278+00:00
-- url     : https://prove2.me/submissions/e3b9ea4e-8e29-43cd-96be-6ee21e6c9a30
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
import Theorems.Thm_GenEmpLik_Coverage_expansion_after_37_lower

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


lemma robustLower_measurable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (ξ : ℕ → Ω → Ξ) {d : ℕ} {X : Set (EuclideanSpace ℝ (Fin d))}
    {ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ} {M : Ξ → ℝ} (f : ℝ → EReal) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hA : AssumptionA f) (hX : X.Nonempty) (hB : AssumptionB X ℓ M)
    (hℓmeas : ∀ x, Measurable (ℓ x)) (hξmeas : ∀ i, Measurable (ξ i)) (n : ℕ) :
    Measurable (fun ω => sInf (empiricalOptimalValue X ℓ (fun i : Fin n => ξ i ω) '' divergenceBall f ρ n)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hempty : divergenceBall f ρ 0 = ∅ := by
      ext p
      simp [divergenceBall, PhiDivRobust.Counterpart.probUncertaintySet]
    have : (fun ω => sInf (empiricalOptimalValue X ℓ (fun i : Fin 0 => ξ i ω) ''
        divergenceBall f ρ 0)) = fun _ => sInf ∅ := by
      funext ω; simp [hempty]
    rw [this]; exact measurable_const
  obtain ⟨D, hDX, hDc, hDdense⟩ := exists_countable_dense X
  have : Countable D := hDc.to_subtype
  have hGmeas : ∀ (p : Fin n → ℝ),
      Measurable (fun ω => empiricalOptimalValue X ℓ (fun i : Fin n => ξ i ω) p) := by
    intro p
    have : (fun ω => empiricalOptimalValue X ℓ (fun i : Fin n => ξ i ω) p) =
        fun ω => ⨅ x : D, ∑ i, p i * ℓ (x : EuclideanSpace ℝ (Fin d)) (ξ i ω) := by
      funext ω
      exact sInf_image_eq_iInf hB.1 hX (wsum_contOn hB _ p) hDX hDdense
    rw [this]
    exact Measurable.iInf (fun x => Finset.measurable_sum _
      (fun i _ => ((hℓmeas x).comp (hξmeas i)).const_mul _))
  have hBc := ball_isCompact f hA ρ n hn
  have hBne : (divergenceBall f ρ n).Nonempty := ⟨_, ball_nonempty f hA ρ hρ n hn⟩
  obtain ⟨E, hEB, hEc, hEdense⟩ := exists_countable_dense (divergenceBall f ρ n)
  have : Countable E := hEc.to_subtype
  have : (fun ω => sInf (empiricalOptimalValue X ℓ (fun i : Fin n => ξ i ω) ''
      divergenceBall f ρ n)) =
      fun ω => ⨅ e : E, empiricalOptimalValue X ℓ (fun i : Fin n => ξ i ω) e := by
    funext ω
    exact sInf_image_eq_iInf hBc hBne (G_cont hB hX _).continuousOn hEB hEdense
  rw [this]; exact Measurable.iInf (fun e => hGmeas e)

end GEL3

namespace GEL3b
open VarianceRegularization.Expansion

lemma gauss_shift (ρ : ℝ) (v : NNReal) (hv : v ≠ 0) (r : ℝ) (hr : r = Real.sqrt ρ * Real.sqrt v) :
    (gaussianReal 0 v).map (fun x => x + r) (Set.Ici 0) =
      gaussianReal 0 1 (Set.Ici (-(Real.sqrt ρ))) := by
  have hvpos : 0 < Real.sqrt v := Real.sqrt_pos.2 (by
    have : (0:NNReal) < v := pos_iff_ne_zero.2 hv
    exact_mod_cast this)
  have hg : gaussianReal 0 v = (gaussianReal 0 1).map (fun x => Real.sqrt v * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · ext
      simp [Real.sq_sqrt (NNReal.coe_nonneg v)]
  rw [hg, Measure.map_map (measurable_add_const r) (measurable_const_mul _)]
  rw [Measure.map_apply ((measurable_add_const r).comp (measurable_const_mul _)) measurableSet_Ici]
  congr 1
  ext x
  simp only [Set.mem_preimage, Function.comp, Set.mem_Ici, hr]
  constructor
  · intro h
    have : Real.sqrt v * (-(Real.sqrt ρ)) ≤ Real.sqrt v * x := by nlinarith
    exact le_of_mul_le_mul_left this hvpos
  · intro h
    nlinarith

lemma limit_of_expansion {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hXm : ∀ k, Measurable (X k)) (hindep : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ) (hvar : 0 < Var[X 0; μ]) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (W : ℕ → Ω → ℝ) (hWm : ∀ n, Measurable (W n))
    (hexp : ∀ δ : ℝ, 0 < δ → Tendsto (fun n : ℕ => μ {ω | δ < |W n ω -
        Real.sqrt n * empMean (fun i : Fin n => X i ω - μ[X 0]) -
        Real.sqrt (ρ * empVar (fun i : Fin n => X i ω - μ[X 0]))|}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {ω | 0 ≤ W n ω}) atTop (𝓝 (gaussianReal 0 1 (Set.Ici (-(Real.sqrt ρ))))) := by
  set m := μ[X 0]
  set v := Var[X 0; μ]
  have hv0 : v ≠ 0 := hvar.ne'
  have hmem : MemLp (X 0) 2 μ := memLp_two_of_variance_ne_zero (hXm 0).aestronglyMeasurable hv0
  -- CLT
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub (P' := gaussianReal 0 v.toNNReal)
    (Y := id) HasLaw.id hmem hindep hident
  set S : ℕ → Ω → ℝ := fun n ω => (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * m) with hS
  -- centred variables
  set Y : ℕ → Ω → ℝ := fun k ω => X k ω - m with hY
  have hYm : ∀ k, Measurable (Y k) := fun k => (hXm k).sub_const m
  have hpair : ∀ (g : ℝ → ℝ), Measurable g →
      Pairwise (Function.onFun (fun x1 x2 => x1 ⟂ᵢ[μ] x2) (fun k => g ∘ X k)) := by
    intro g hg i j hij
    exact (hindep.indepFun hij).comp hg hg
  have hidentg : ∀ (g : ℝ → ℝ), Measurable g → ∀ k, IdentDistrib (g ∘ X k) (g ∘ X 0) μ μ :=
    fun g hg k => (hident k).comp hg
  have hint1 : Integrable ((fun x => x - m) ∘ X 0) μ :=
    (hmem.integrable one_le_two).sub (integrable_const m)
  have hint2 : Integrable ((fun x => (x - m) ^ 2) ∘ X 0) μ := by
    have := (hmem.sub (memLp_const m)).integrable_sq
    exact this
  have hslln1 := strong_law_ae (fun k => (fun x => x - m) ∘ X k) hint1
    (hpair _ (measurable_id.sub_const m)) (hidentg _ (measurable_id.sub_const m))
  have hslln2 := strong_law_ae (fun k => (fun x => (x - m) ^ 2) ∘ X k) hint2
    (hpair _ ((measurable_id.sub_const m).pow_const 2))
    (hidentg _ ((measurable_id.sub_const m).pow_const 2))
  have hE1 : ∫ ω, ((fun x => x - m) ∘ X 0) ω ∂μ = 0 := by
    simp only [Function.comp]
    rw [integral_sub (hmem.integrable one_le_two) (integrable_const m)]
    simp [m]
  have hE2 : ∫ ω, ((fun x => (x - m) ^ 2) ∘ X 0) ω ∂μ = v := by
    simp only [Function.comp, v]
    rw [variance_eq_integral (hXm 0).aemeasurable]
  set R : ℕ → Ω → ℝ := fun n ω => Real.sqrt (ρ * empVar (fun i : Fin n => X i ω - m)) with hR
  have hRm : ∀ n, Measurable (R n) := by
    intro n
    refine (measurable_const.mul ?_).sqrt
    unfold empVar empMean
    have h1 : Measurable fun ω => ∑ i : Fin n, (X i ω - m) ^ 2 :=
      Finset.measurable_sum _ fun i _ => ((hXm i).sub_const m).pow_const 2
    have h2 : Measurable fun ω => ∑ i : Fin n, (X i ω - m) :=
      Finset.measurable_sum _ fun i _ => (hXm i).sub_const m
    exact (h1.const_mul _).sub ((h2.const_mul _).pow_const 2)
  have hRlim : TendstoInMeasure μ R atTop (fun _ => Real.sqrt (ρ * v)) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => (hRm n).aestronglyMeasurable) ?_
    filter_upwards [hslln1, hslln2] with ω h1 h2
    rw [hE1] at h1
    rw [hE2] at h2
    have hev : ∀ n : ℕ, empVar (fun i : Fin n => X i ω - m) =
        (n:ℝ)⁻¹ • ∑ i ∈ Finset.range n, ((fun x => (x - m) ^ 2) ∘ X i) ω -
        ((n:ℝ)⁻¹ • ∑ i ∈ Finset.range n, ((fun x => x - m) ∘ X i) ω) ^ 2 := by
      intro n
      simp only [empVar, empMean, smul_eq_mul, Function.comp]
      rw [Fin.sum_univ_eq_sum_range (fun i => (X i ω - m) ^ 2) n,
        Fin.sum_univ_eq_sum_range (fun i => X i ω - m) n]
    simp only [hR, hev]
    have := (h2.sub (h1.pow 2))
    have h3 := (this.const_mul ρ).sqrt
    simpa using h3
  -- Slutsky
  have hZ := hclt.add_of_tendstoInMeasure_const hRlim (fun n => (hRm n).aemeasurable)
  have hSeq : ∀ (n : ℕ) (ω : Ω), (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * m) =
      Real.sqrt n * empMean (fun i : Fin n => X i ω - m) := by
    intro n ω
    simp only [empMean]
    rw [Fin.sum_univ_eq_sum_range (fun i => X i ω - m) n, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hnR : (0:ℝ) < n := by exact_mod_cast hn
      have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hnR).ne'
      field_simp
      rw [Real.sq_sqrt hnR.le]
  have hsub : TendstoInMeasure μ (W - fun n : ℕ => S n + R n) atTop 0 := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    have h := hexp (ε / 2) (by positivity)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
      (fun n => measure_mono ?_)
    intro ω hω
    simp only [Set.mem_setOf_eq, Pi.sub_apply, Pi.add_apply, Pi.zero_apply, Real.dist_eq,
      sub_zero, hS, hSeq] at hω ⊢
    have : |W n ω - (Real.sqrt n * empMean (fun i : Fin n => X i ω - m) + R n ω)| =
        |W n ω - Real.sqrt n * empMean (fun i : Fin n => X i ω - m) -
          Real.sqrt (ρ * empVar (fun i : Fin n => X i ω - m))| := by
      rw [sub_add_eq_sub_sub]
    rw [this] at hω
    linarith
  have hW := tendstoInDistribution_of_tendstoInMeasure_sub W _ hZ hsub
    (fun n => (hWm n).aemeasurable)
  have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hW.tendsto
    (E := Set.Ici 0) ?_
  · have h2 := ENNReal.tendsto_coe.2 hlim
    simp only [ProbabilityMeasure.mk_apply, ne_eq, measure_ne_top, not_false_eq_true,
      ENNReal.coe_toNNReal] at h2
    rw [← gauss_shift ρ v.toNNReal (by simpa using hvar) (Real.sqrt (ρ * v))
      (by rw [Real.sqrt_mul hρ, Real.coe_toNNReal _ hvar.le])]
    have he : ∀ n, μ.map (W n) (Set.Ici 0) = μ {ω | 0 ≤ W n ω} := fun n =>
      Measure.map_apply (hWm n) measurableSet_Ici
    simp only [he] at h2
    simpa [id] using h2
  · rw [frontier_Ici, ProbabilityMeasure.mk_apply, ENNReal.toNNReal_eq_zero_iff]
    left
    have hv' : v.toNNReal ≠ 0 := by simpa using hvar
    have : (gaussianReal 0 v.toNNReal).map (fun ω => id ω + Real.sqrt (ρ * v)) =
        gaussianReal (0 + Real.sqrt (ρ * v)) v.toNNReal := gaussianReal_map_add_const _
    rw [this]
    have := noAtoms_gaussianReal (μ := 0 + Real.sqrt (ρ * v)) hv'
    exact measure_singleton _

end GEL3b

open GenEmpLik.Coverage GEL3 GEL3b VarianceRegularization.Expansion

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
    Tendsto (fun n : ℕ => μ {ω |
      sInf (empiricalOptimalValue X ℓ (fun i : Fin n => ξ i ω) '' divergenceBall f ρ n) ≤
        optimalValue X ℓ (μ.map (ξ 0))})
      atTop (𝓝 (gaussianReal 0 1 (Set.Iic (Real.sqrt ρ)))) := by
  have hexp := expansion_after_37_lower μ ξ d X ℓ M f ρ hρ hA hX hB hℓmeas hM2 hℓ2 hξmeas
    hξindep hξident hunique hvar
  set xs := uniqueOptimizer X ℓ (μ.map (ξ 0)) hunique with hxs
  set T0 := optimalValue X ℓ (μ.map (ξ 0)) with hT0
  set Y : ℕ → Ω → ℝ := fun k ω => -ℓ xs (ξ k ω) with hY
  have hYm : ∀ k, Measurable (Y k) := fun k => ((hℓmeas xs).comp (hξmeas k)).neg
  have hYindep : iIndepFun Y μ :=
    hξindep.comp (fun _ z => -ℓ xs z) (fun _ => (hℓmeas xs).neg)
  have hYident : ∀ k, IdentDistrib (Y k) (Y 0) μ μ := fun k =>
    (hξident k).comp (u := fun z => -ℓ xs z) (hℓmeas xs).neg
  have hYvar : 0 < Var[Y 0; μ] := by
    have := variance_map (X := ℓ xs) (μ := μ) (Y := ξ 0) (hℓmeas xs).aemeasurable
      (hξmeas 0).aemeasurable
    have hneg : Var[Y 0; μ] = Var[ℓ xs ∘ ξ 0; μ] := by
      rw [show Y 0 = fun ω => -((ℓ xs ∘ ξ 0) ω) from rfl, variance_fun_neg]
    rw [hneg, ← this]
    exact hvar
  have hmean : μ[Y 0] = -∫ z, ℓ xs z ∂(μ.map (ξ 0)) := by
    rw [integral_map (hξmeas 0).aemeasurable (hℓmeas xs).aestronglyMeasurable]
    simp only [hY]
    exact integral_neg _
  set L : ℕ → Ω → ℝ := fun n ω =>
    sInf (empiricalOptimalValue X ℓ (fun i : Fin n => ξ i ω) '' divergenceBall f ρ n) with hL
  set W : ℕ → Ω → ℝ := fun n ω => Real.sqrt n * (T0 - L n ω) with hW
  have hWm : ∀ n, Measurable (W n) := fun n =>
    ((robustLower_measurable ξ f ρ hρ hA hX hB hℓmeas hξmeas n).const_sub T0).const_mul _
  have hinf : ∀ (n : ℕ) (ω : Ω), (fun i : Fin n => Y i ω - μ[Y 0]) =
      fun i : Fin n => -influence ℓ xs (μ.map (ξ 0)) (ξ i ω) := by
    intro n ω; funext i; simp only [influence, hY]; rw [hmean]; ring
  have hmean_neg : ∀ {n : ℕ} (z : Fin n → ℝ), empMean (fun i => -z i) = -empMean z := by
    intro n z; simp only [empMean, Finset.sum_neg_distrib, mul_neg]
  have hvar_neg : ∀ {n : ℕ} (z : Fin n → ℝ), empVar (fun i => -z i) = empVar z := by
    intro n z; simp only [empVar, hmean_neg, neg_sq]
  have hexp' : ∀ δ : ℝ, 0 < δ → Tendsto (fun n : ℕ => μ {ω | δ < |W n ω -
        Real.sqrt n * empMean (fun i : Fin n => Y i ω - μ[Y 0]) -
        Real.sqrt (ρ * empVar (fun i : Fin n => Y i ω - μ[Y 0]))|}) atTop (𝓝 0) := by
    intro δ hδ
    have h := hexp δ hδ
    refine h.congr (fun n => ?_)
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq, hinf, hmean_neg, hvar_neg, hW, hL]
    rw [← abs_neg]
    ring_nf
  have hlim := limit_of_expansion μ Y hYm hYindep hYident hYvar ρ hρ W hWm hexp'
  have hsym : gaussianReal 0 1 (Set.Ici (-(Real.sqrt ρ))) =
      gaussianReal 0 1 (Set.Iic (Real.sqrt ρ)) := by
    have h := gaussianReal_map_neg (μ := 0) (v := 1)
    rw [neg_zero] at h
    conv_rhs => rw [← h]
    rw [Measure.map_apply measurable_neg measurableSet_Iic]
    congr 1
    ext x
    simp [neg_le]
  rw [← hsym]
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, hW]
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  constructor
  · intro h
    have := (mul_nonneg_iff_of_pos_left hs).1 h
    linarith
  · intro h
    exact mul_nonneg hs.le (by linarith)
