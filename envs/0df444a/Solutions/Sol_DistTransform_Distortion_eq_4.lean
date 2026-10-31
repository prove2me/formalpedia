-- Prove2me | solution 1 for DistTransform.Distortion.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:48:29.006037+00:00
-- url     : https://prove2.me/submissions/38a5ffa5-b1d3-4f4c-a423-4b0ce62aec69

import Mathlib
import Definitions.Def_DistTransform_Distortion_Model
import Theorems.Thm_DistTransform_Distortion_claims_i_ii
import Theorems.Thm_DistTransform_Distortion_chambers_quantile

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

namespace Aux_DTDeq4
open DistTransform.Distortion

noncomputable def clamp (c : ℝ) : ℝ := max 0 (min c 1)

lemma clamp_nonneg (c : ℝ) : 0 ≤ clamp c := le_max_left _ _
lemma clamp_le_one (c : ℝ) : clamp c ≤ 1 := max_le zero_le_one (min_le_right _ _)
lemma clamp_of_mem {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) : clamp c = c := by
  unfold clamp; rw [min_eq_left h1, max_eq_right h0]
lemma continuous_clamp : Continuous clamp :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The two-point distribution with mass `c` at `0` and `1 - c` at `1`
(a scaled Bernoulli law), for `c ∈ [0, 1]`. -/
noncomputable def twoPtM (c : ℝ) : Measure ℝ :=
  ENNReal.ofReal (clamp c) • Measure.dirac 0 + ENNReal.ofReal (1 - clamp c) • Measure.dirac 1

instance (c : ℝ) : IsProbabilityMeasure (twoPtM c) := by
  constructor
  simp only [twoPtM, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (clamp_nonneg c) (by linarith [clamp_le_one c])]
  simp

noncomputable def twoPt (c : ℝ) : ProbabilityMeasure ℝ := ⟨twoPtM c, inferInstance⟩

lemma cdf_twoPt (c x : ℝ) :
    cdf (twoPt c : Measure ℝ) x =
      (if 0 ≤ x then clamp c else 0) + (if 1 ≤ x then 1 - clamp c else 0) := by
  rw [cdf_eq_real, measureReal_def]
  show (twoPtM c (Set.Iic x)).toReal = _
  simp only [twoPtM, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ measurableSet_Iic, Set.indicator, Set.mem_Iic, Pi.one_apply]
  have h1 := clamp_nonneg c
  have h2 := clamp_le_one c
  split_ifs <;> simp [ENNReal.toReal_add, ENNReal.ofReal_ne_top, h1, h2] <;> linarith

lemma cdf_twoPt_neg (c x : ℝ) (hx : x < 0) : cdf (twoPt c : Measure ℝ) x = 0 := by
  rw [cdf_twoPt, if_neg (by linarith), if_neg (by linarith)]; simp

lemma cdf_twoPt_mid (c x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    cdf (twoPt c : Measure ℝ) x = clamp c := by
  rw [cdf_twoPt, if_pos hx0, if_neg (by linarith)]; simp

lemma cdf_twoPt_ge (c x : ℝ) (hx : 1 ≤ x) : cdf (twoPt c : Measure ℝ) x = 1 := by
  rw [cdf_twoPt, if_pos (by linarith), if_pos hx]; ring

lemma twoPt_mem_Minf (c : ℝ) : twoPt c ∈ Minf := by
  refine ⟨0, 1, ?_⟩
  show twoPtM c (Set.Icc 0 1) = 1
  simp only [twoPtM, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ measurableSet_Icc, Set.indicator, Set.mem_Icc, Pi.one_apply]
  simp only [le_refl, zero_le_one, and_self, if_true, mul_one]
  rw [← ENNReal.ofReal_add (clamp_nonneg c) (by linarith [clamp_le_one c])]
  simp

lemma integral_twoPt (c : ℝ) (f : ℝ →ᵇ ℝ) :
    ∫ ω, f ω ∂(twoPt c : Measure ℝ) = clamp c * f 0 + (1 - clamp c) * f 1 := by
  show ∫ ω, f ω ∂(twoPtM c) = _
  have h1 := clamp_nonneg c
  have h2 : 0 ≤ 1 - clamp c := by linarith [clamp_le_one c]
  unfold twoPtM
  rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac, ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2, smul_eq_mul, smul_eq_mul]
  · exact (f.integrable _).smul_measure ENNReal.ofReal_ne_top
  · exact (f.integrable _).smul_measure ENNReal.ofReal_ne_top

lemma tendsto_twoPt {cs : ℕ → ℝ} {c : ℝ} (h : Tendsto cs atTop (𝓝 c)) :
    Tendsto (fun n => twoPt (cs n)) atTop (𝓝 (twoPt c)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  simp only [integral_twoPt]
  have hc : Tendsto (fun n => clamp (cs n)) atTop (𝓝 (clamp c)) :=
    (continuous_clamp.tendsto c).comp h
  exact (hc.mul tendsto_const_nhds).add ((tendsto_const_nhds.sub hc).mul tendsto_const_nhds)


lemma ioi_eq (μ : ProbabilityMeasure ℝ) (x : ℝ) :
    (μ : Measure ℝ) {ω | x < id ω} = ENNReal.ofReal (1 - cdf (μ : Measure ℝ) x) := by
  have h1 : {ω : ℝ | x < id ω} = (Set.Iic x)ᶜ := by ext; simp
  rw [h1, prob_compl_eq_one_sub measurableSet_Iic, cdf_eq_real, measureReal_def,
    ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one, ENNReal.ofReal_toReal
      (measure_ne_top _ _)]

lemma stLE_iff (F G : ProbabilityMeasure ℝ) :
    StLE F G ↔ ∀ x, cdf (G : Measure ℝ) x ≤ cdf (F : Measure ℝ) x := by
  unfold StLE StochasticOrders.Usual.UsualOrder
  refine forall_congr' fun x => ?_
  rw [ioi_eq, ioi_eq, ENNReal.ofReal_le_ofReal_iff]
  · constructor <;> intro h <;> linarith
  · linarith [cdf_le_one (G : Measure ℝ) x]

lemma qset_nonempty (F : ProbabilityMeasure ℝ) {p : ℝ} (hp1 : p < 1) :
    {x : ℝ | p ≤ cdf (F : Measure ℝ) x}.Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop (μ := (F : Measure ℝ))).eventually
    (lt_mem_nhds hp1)).exists
  exact ⟨x, hx.le⟩

lemma qset_bdd (F : ProbabilityMeasure ℝ) {p : ℝ} (hp0 : 0 < p) :
    BddBelow {x : ℝ | p ≤ cdf (F : Measure ℝ) x} := by
  obtain ⟨a, ha⟩ := Filter.eventually_atBot.1 ((tendsto_cdf_atBot (μ := (F : Measure ℝ))).eventually
    (gt_mem_nhds hp0))
  refine ⟨a, fun x hx => ?_⟩
  by_contra hxa
  push Not at hxa
  have := ha x hxa.le
  simp only [Set.mem_setOf_eq] at hx
  linarith

/-- Galois correspondence for the left quantile at a level `u ∈ (0,1)`. -/
lemma galois (F : ProbabilityMeasure ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (x : ℝ) :
    leftQuantile F u ≤ x ↔ u ≤ cdf (F : Measure ℝ) x := by
  have hne := qset_nonempty F hu1
  have hbdd := qset_bdd F hu0
  unfold leftQuantile
  constructor
  · intro hq
    have hmem : u ≤ cdf (F : Measure ℝ) (sInf {y : ℝ | u ≤ cdf (F : Measure ℝ) y}) := by
      rw [← (cdf (F : Measure ℝ)).iInf_Ioi_eq]
      apply le_ciInf
      intro r
      obtain ⟨y, hyS, hyr⟩ := exists_lt_of_csInf_lt hne r.2
      exact hyS.trans (monotone_cdf _ hyr.le)
    exact hmem.trans (monotone_cdf _ hq)
  · intro hx
    exact csInf_le hbdd hx

lemma leftQuantile_level_mono (F : ProbabilityMeasure ℝ) {p p' : ℝ} (hp0 : 0 < p)
    (hpp : p ≤ p') (hp'1 : p' < 1) : leftQuantile F p ≤ leftQuantile F p' := by
  unfold leftQuantile
  exact csInf_le_csInf (qset_bdd F hp0) (qset_nonempty F hp'1)
    (fun x hx => le_trans hpp hx)

lemma lq_twoPt_zero (c β : ℝ) (hβ0 : 0 < β) (hβ : β ≤ clamp c) :
    leftQuantile (twoPt c) β = 0 := by
  apply IsLeast.csInf_eq
  refine ⟨?_, fun x hx => ?_⟩
  · show β ≤ cdf _ 0
    rw [cdf_twoPt_mid c 0 le_rfl zero_lt_one]; exact hβ
  · by_contra hx0
    push Not at hx0
    have : β ≤ cdf (twoPt c : Measure ℝ) x := hx
    rw [cdf_twoPt_neg c x hx0] at this; linarith

lemma lq_twoPt_one (c β : ℝ) (hβ : clamp c < β) (hβ1 : β ≤ 1) :
    leftQuantile (twoPt c) β = 1 := by
  apply IsLeast.csInf_eq
  refine ⟨?_, fun x hx => ?_⟩
  · show β ≤ cdf _ 1
    rw [cdf_twoPt_ge c 1 le_rfl]; exact hβ1
  · by_contra hx1
    push Not at hx1
    have : β ≤ cdf (twoPt c : Measure ℝ) x := hx
    rcases lt_or_ge x 0 with h0 | h0
    · rw [cdf_twoPt_neg c x h0] at this; linarith [clamp_nonneg c]
    · rw [cdf_twoPt_mid c x h0 hx1] at this; linarith

lemma rq_twoPt_zero (c β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < clamp c) :
    rightQuantile (twoPt c) β = 0 := by
  apply IsLeast.csInf_eq
  refine ⟨?_, fun x hx => ?_⟩
  · show β < cdf _ 0
    rw [cdf_twoPt_mid c 0 le_rfl zero_lt_one]; exact hβ
  · by_contra hx0
    push Not at hx0
    have : β < cdf (twoPt c : Measure ℝ) x := hx
    rw [cdf_twoPt_neg c x hx0] at this; linarith

lemma rq_twoPt_one (c β : ℝ) (hβ : clamp c ≤ β) (hβ1 : β < 1) :
    rightQuantile (twoPt c) β = 1 := by
  apply IsLeast.csInf_eq
  refine ⟨?_, fun x hx => ?_⟩
  · show β < cdf _ 1
    rw [cdf_twoPt_ge c 1 le_rfl]; exact hβ1
  · by_contra hx1
    push Not at hx1
    have : β < cdf (twoPt c : Measure ℝ) x := hx
    rcases lt_or_ge x 0 with h0 | h0
    · rw [cdf_twoPt_neg c x h0] at this; linarith [clamp_nonneg c]
    · rw [cdf_twoPt_mid c x h0 hx1] at this; linarith

lemma lq_twoPt_le_one (c β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    leftQuantile (twoPt c) β ≤ 1 := by
  rcases le_or_gt β (clamp c) with h | h
  · rw [lq_twoPt_zero c β hβ0 h]; exact zero_le_one
  · rw [lq_twoPt_one c β h hβ1]

lemma rq_twoPt_le_one (c β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    rightQuantile (twoPt c) β ≤ 1 := by
  rcases lt_or_ge β (clamp c) with h | h
  · rw [rq_twoPt_zero c β hβ0 h]; exact zero_le_one
  · rw [rq_twoPt_one c β h hβ1]

end Aux_DTDeq4

open DistTransform.Distortion Aux_DTDeq4 in
theorem solution (M : Set (ProbabilityMeasure ℝ)) (hM : M = Set.univ ∨ M = Minf)
    (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) (hT : Set.MapsTo T M M)
    (hlsc : IsLSC M T) (hmono : IsMonotoneT M T) (hcomm : CommutesWithShape M T) :
    ∃ h : ℝ → ℝ, MonotoneOn h (Set.Ioo 0 1) ∧
      (∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 < h p ∧ h p ≤ 1) ∧
      ∀ F ∈ Minf, ∀ p ∈ Set.Ioo (0 : ℝ) 1, leftQuantile (T F) p = leftQuantile F (h p) := by
  have hsub : Minf ⊆ M := by
    rcases hM with rfl | rfl
    · exact Set.subset_univ _
    · exact subset_rfl
  -- Chambers (2009): each `q_p^T` is a left or right quantile at a fixed level on `M∞`.
  have chamb : ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∃ α ∈ Set.Icc (0 : ℝ) 1,
      (0 < α ∧ ∀ F ∈ Minf, leftQuantile (T F) p = leftQuantile F α) ∨
        (α < 1 ∧ ∀ F ∈ Minf, leftQuantile (T F) p = rightQuantile F α) := by
    intro p hp
    obtain ⟨hi, hii⟩ := claims_i_ii M hM T hT hmono hcomm p hp.1 hp.2
    exact chambers_quantile (fun F => leftQuantile (T F) p)
      (fun F hF G hG hFG => hi F (hsub hF) G (hsub hG) hFG)
      (fun φ F hF => hii φ F (hsub hF))
  -- all quantiles of `T` of a two-point law on `{0,1}` are at most `1`
  have hle1 : ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ c, leftQuantile (T (twoPt c)) p ≤ 1 := by
    intro p hp c
    obtain ⟨α, hα, hcase⟩ := chamb p hp
    rcases hcase with ⟨hα0, hl⟩ | ⟨hα1, hr⟩
    · rw [hl _ (twoPt_mem_Minf c)]; exact lq_twoPt_le_one c α hα0 hα.2
    · rw [hr _ (twoPt_mem_Minf c)]; exact rq_twoPt_le_one c α hα.1 hα1
  have hcdf1 : ∀ c x, 1 ≤ x → cdf (T (twoPt c) : Measure ℝ) x = 1 := by
    intro c x hx
    apply le_antisymm (cdf_le_one _ _)
    by_contra hlt
    push Not at hlt
    set y := cdf (T (twoPt c) : Measure ℝ) x
    have hy0 : 0 ≤ y := cdf_nonneg _ _
    have hp : (y + 1) / 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have := (galois (T (twoPt c)) hp.1 hp.2 x).1 ((hle1 _ hp c).trans hx)
    linarith
  -- the right-quantile alternative is excluded by lower-semicontinuity (E = (0,1))
  have key : ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      ∀ F ∈ Minf, leftQuantile (T F) p = leftQuantile F α := by
    intro p hp
    obtain ⟨α, hα, hcase⟩ := chamb p hp
    rcases hcase with ⟨hα0, hl⟩ | ⟨hα1, hr⟩
    · exact ⟨α, hα0, hα.2, hl⟩
    exfalso
    set cs : ℕ → ℝ := fun n => α + (1 - α) / ((n : ℝ) + 2) with hcs
    have hcs_gt : ∀ n, α < cs n := by
      intro n
      have : 0 < (1 - α) / ((n : ℝ) + 2) := div_pos (by linarith) (by positivity)
      simp only [hcs]; linarith
    have hcs_le : ∀ n, cs n ≤ 1 := by
      intro n
      have h2 : (1 - α) / ((n : ℝ) + 2) ≤ 1 - α :=
        div_le_self (by linarith) (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
      simp only [hcs]; linarith
    have hcs_lim : Tendsto cs atTop (𝓝 α) := by
      have h1 : Tendsto (fun n : ℕ => (1 - α) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        apply Tendsto.div_atTop tendsto_const_nhds
        exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      simpa using (tendsto_const_nhds (x := α)).add h1
    -- `q_p^T(F_n) = 0` for the approximating two-point laws
    have hqn : ∀ n, leftQuantile (T (twoPt (cs n))) p = 0 := by
      intro n
      rw [hr _ (twoPt_mem_Minf _)]
      apply rq_twoPt_zero _ _ hα.1
      rw [clamp_of_mem (by linarith [hcs_gt n, hα.1]) (hcs_le n)]
      exact hcs_gt n
    have hTn_le : ∀ n, StLE (T (twoPt (cs n))) (twoPt p) := by
      intro n
      rw [stLE_iff]
      intro x
      rcases lt_or_ge x 0 with h0 | h0
      · rw [cdf_twoPt_neg p x h0]; exact cdf_nonneg _ _
      rcases lt_or_ge x 1 with h1 | h1
      · rw [cdf_twoPt_mid p x h0 h1, clamp_of_mem hp.1.le hp.2.le]
        exact (galois _ hp.1 hp.2 x).1 (by rw [hqn n]; exact h0)
      · rw [cdf_twoPt_ge p x h1, hcdf1 _ x h1]
    have hlim := hlsc (fun n => twoPt (cs n)) (twoPt α) (twoPt p)
      (fun n => hsub (twoPt_mem_Minf _)) (hsub (twoPt_mem_Minf _)) (hsub (twoPt_mem_Minf _))
      (tendsto_twoPt hcs_lim) hTn_le
    have h0 := (stLE_iff _ _).1 hlim 0
    rw [cdf_twoPt_mid p 0 le_rfl zero_lt_one, clamp_of_mem hp.1.le hp.2.le] at h0
    have hq0 := (galois _ hp.1 hp.2 0).2 h0
    rw [hr _ (twoPt_mem_Minf _), rq_twoPt_one α α (by rw [clamp_of_mem hα.1 hα.2]) hα1] at hq0
    linarith
  choose! h hh0 hh1 hhq using key
  refine ⟨h, ?_, fun p hp => ⟨hh0 p hp, hh1 p hp⟩, fun F hF p hp => hhq p hp F hF⟩
  -- `h` is increasing
  intro p hp p' hp' hpp'
  by_contra hlt
  push Not at hlt
  have e1 := hhq p' hp' (twoPt (h p')) (twoPt_mem_Minf _)
  have e2 := hhq p hp (twoPt (h p')) (twoPt_mem_Minf _)
  have hc : clamp (h p') = h p' := clamp_of_mem (hh0 p' hp').le (hh1 p' hp')
  rw [lq_twoPt_zero _ _ (hh0 p' hp') hc.ge] at e1
  rw [lq_twoPt_one _ _ (by rw [hc]; exact hlt) (hh1 p hp)] at e2
  have := leftQuantile_level_mono (T (twoPt (h p'))) hp.1 hpp' hp'.2
  linarith
