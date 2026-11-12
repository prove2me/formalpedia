-- Prove2me | solution 1 for GenEmpLik.Expansion.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T04:02:42.987197+00:00
-- url     : https://prove2.me/submissions/f59ac3e3-881d-4f40-af1c-6427d35409ef

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_AssumptionA
import Definitions.Def_GenEmpLik_Expansion_robustMean
import Definitions.Def_GenEmpLik_Expansion_IsStationaryErgodic
import Definitions.Def_VarianceRegularization_Expansion_empMean
import Definitions.Def_VarianceRegularization_Expansion_empVar
import Theorems.Thm_GenEmpLik_Expansion_eq_30
import Theorems.Thm_GenEmpLik_Expansion_lemma_6
import Theorems.Thm_GenEmpLik_Expansion_lemma_7

open MeasureTheory ProbabilityTheory Filter Topology VarianceRegularization.Expansion

private def birSum {α : Type*} (T : α → α) (g : α → ℝ) (n : ℕ) (x : α) : ℝ :=
  ∑ k ∈ Finset.range n, g (T^[k] x)

private lemma birSum_zero {α : Type*} (T : α → α) (g : α → ℝ) (x : α) :
    birSum T g 0 x = 0 := by
  simp [birSum]

private lemma birSum_succ' {α : Type*} (T : α → α) (g : α → ℝ) (n : ℕ) (x : α) :
    birSum T g (n + 1) x = g x + birSum T g n (T x) := by
  unfold birSum
  rw [Finset.sum_range_succ', add_comm]
  rfl

private lemma measurable_birSum {α : Type*} [MeasurableSpace α] {T : α → α} {g : α → ℝ}
    (hT : Measurable T) (hg : Measurable g) (n : ℕ) :
    Measurable (birSum T g n) := by
  unfold birSum
  refine Finset.measurable_sum (Finset.range n) fun k _ => ?_
  exact hg.comp (hT.iterate k)

private def maxPosSum {α : Type*} (T : α → α) (g : α → ℝ) : ℕ → α → ℝ
  | 0, _ => 0
  | N + 1, x => max 0 (g x + maxPosSum T g N (T x))

private lemma maxPosSum_nonneg {α : Type*} (T : α → α) (g : α → ℝ) (N : ℕ) (x : α) :
    0 ≤ maxPosSum T g N x := by
  cases N with
  | zero => exact le_rfl
  | succ N => exact le_max_left 0 _

private lemma maxPosSum_mono_step {α : Type*} (T : α → α) (g : α → ℝ) (N : ℕ) (x : α) :
    maxPosSum T g N x ≤ maxPosSum T g (N + 1) x := by
  induction N generalizing x with
  | zero => exact le_max_left 0 _
  | succ N ih =>
    simp only [maxPosSum]
    exact max_le_max_left 0 (add_le_add_right (ih (T x)) (g x))

private lemma maxPosSum_mono {α : Type*} (T : α → α) (g : α → ℝ) {N₁ N₂ : ℕ}
    (h : N₁ ≤ N₂) (x : α) : maxPosSum T g N₁ x ≤ maxPosSum T g N₂ x := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (maxPosSum_mono_step T g _ x)

private lemma birSum_le_maxPosSum {α : Type*} (T : α → α) (g : α → ℝ) {n N : ℕ}
    (hn : 1 ≤ n) (hN : n ≤ N) (x : α) :
    birSum T g n x ≤ maxPosSum T g N x := by
  induction N generalizing n x with
  | zero => omega
  | succ N ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [birSum_succ']
    simp only [maxPosSum]
    refine le_trans ?_ (le_max_right 0 _)
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [birSum_zero]
      linarith [maxPosSum_nonneg T g N (T x)]
    · exact add_le_add_right (ih hm (by omega) (T x)) (g x)

private lemma exists_birSum_eq_maxPosSum {α : Type*} (T : α → α) (g : α → ℝ) (N : ℕ) (x : α) :
    ∃ n : ℕ, n ≤ N ∧ maxPosSum T g N x = birSum T g n x := by
  induction N generalizing x with
  | zero => exact ⟨0, le_rfl, (birSum_zero T g x).symm⟩
  | succ N ih =>
    rcases ih (T x) with ⟨m, hmN, hm_eq⟩
    simp only [maxPosSum, hm_eq]
    rcases le_total 0 (g x + birSum T g m (T x)) with hnonneg | hneg
    · refine ⟨m + 1, by omega, ?_⟩
      rw [max_eq_right hnonneg, birSum_succ']
    · refine ⟨0, Nat.zero_le _, ?_⟩
      rw [max_eq_left hneg, birSum_zero]

private lemma measurable_maxPosSum {α : Type*} [MeasurableSpace α] {T : α → α} {g : α → ℝ}
    (hT : Measurable T) (hg : Measurable g) (N : ℕ) :
    Measurable (maxPosSum T g N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
    exact measurable_const.max (hg.add (ih.comp hT))

private lemma integrable_maxPosSum {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {T : α → α} {g : α → ℝ} (hT : MeasurePreserving T μ μ) (hg_meas : Measurable g)
    (hg_int : Integrable g μ) (N : ℕ) :
    Integrable (maxPosSum T g N) μ := by
  induction N with
  | zero => exact integrable_zero α ℝ μ
  | succ N ih =>
    have hcomp : Integrable (fun x => maxPosSum T g N (T x)) μ :=
      (hT.integrable_comp (measurable_maxPosSum hT.measurable hg_meas N).aestronglyMeasurable).mpr ih
    have hsum : Integrable (fun x => g x + maxPosSum T g N (T x)) μ := hg_int.add hcomp
    have hmeas : Measurable (maxPosSum T g (N + 1)) :=
      measurable_maxPosSum hT.measurable hg_meas (N + 1)
    refine hsum.mono hmeas.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    simp only [maxPosSum, Real.norm_eq_abs]
    rcases le_total 0 (g x + maxPosSum T g N (T x)) with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h, abs_zero]
      exact abs_nonneg (g x + maxPosSum T g N (T x))

private lemma hopf_maximal_ergodic {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {T : α → α} {g : α → ℝ} (hT : MeasurePreserving T μ μ) (hg_meas : Measurable g)
    (hg_int : Integrable g μ) :
    0 ≤ ∫ x, ({y | ∃ n : ℕ, 1 ≤ n ∧ 0 < birSum T g n y}).indicator g x ∂μ := by
  let E_fin : ℕ → Set α := fun N => {x | 0 < maxPosSum T g (N + 1) x}
  let E : Set α := {x | ∃ n : ℕ, 1 ≤ n ∧ 0 < birSum T g n x}
  have hE_fin_meas : ∀ N, MeasurableSet (E_fin N) := fun N =>
    measurableSet_lt measurable_const (measurable_maxPosSum hT.measurable hg_meas (N + 1))
  have hfin_nonneg : ∀ N : ℕ, 0 ≤ ∫ x, (E_fin N).indicator g x ∂μ := by
    intro N
    have hpt : ∀ x : α, maxPosSum T g N x ≤
        (E_fin N).indicator g x + maxPosSum T g N (T x) := by
      intro x
      refine le_trans (maxPosSum_mono_step T g N x) ?_
      by_cases hx : x ∈ E_fin N
      · have hpos : 0 < maxPosSum T g (N + 1) x := hx
        simp only [maxPosSum] at hpos ⊢
        have hgt : 0 < g x + maxPosSum T g N (T x) := by
          by_contra hle
          rw [max_eq_left (not_lt.mp hle)] at hpos
          exact lt_irrefl 0 hpos
        rw [max_eq_right (le_of_lt hgt), Set.indicator_of_mem hx]
      · have hle : maxPosSum T g (N + 1) x ≤ 0 := not_lt.mp hx
        have heq0 : maxPosSum T g (N + 1) x = 0 :=
          le_antisymm hle (maxPosSum_nonneg T g (N + 1) x)
        rw [heq0, Set.indicator_of_notMem hx, zero_add]
        exact maxPosSum_nonneg T g N (T x)
    have hint_N := integrable_maxPosSum hT hg_meas hg_int N
    have hint_ind : Integrable ((E_fin N).indicator g) μ := hg_int.indicator (hE_fin_meas N)
    have hint_comp : Integrable (fun x => maxPosSum T g N (T x)) μ :=
      (hT.integrable_comp (measurable_maxPosSum hT.measurable hg_meas N).aestronglyMeasurable).mpr
        hint_N
    have hint_le : ∫ x, maxPosSum T g N x ∂μ ≤
        ∫ x, ((E_fin N).indicator g x + maxPosSum T g N (T x)) ∂μ :=
      integral_mono hint_N (hint_ind.add hint_comp) hpt
    rw [integral_add hint_ind hint_comp] at hint_le
    have hinv : ∫ x, maxPosSum T g N (T x) ∂μ = ∫ x, maxPosSum T g N x ∂μ := by
      have hmap : ∫ x, maxPosSum T g N x ∂(μ.map T) = ∫ x, maxPosSum T g N (T x) ∂μ :=
        integral_map hT.measurable.aemeasurable
          (measurable_maxPosSum hT.measurable hg_meas N).aestronglyMeasurable
      rw [hT.map_eq] at hmap
      exact hmap.symm
    linarith
  have hE_iff : ∀ x : α, x ∈ E ↔ ∃ N : ℕ, x ∈ E_fin N := by
    intro x
    constructor
    · rintro ⟨n, hn1, hpos⟩
      refine ⟨n - 1, ?_⟩
      change 0 < maxPosSum T g ((n - 1) + 1) x
      have hn_eq : (n - 1) + 1 = n := by omega
      rw [hn_eq]
      exact lt_of_lt_of_le hpos (birSum_le_maxPosSum T g hn1 le_rfl x)
    · rintro ⟨N, hpos⟩
      change 0 < maxPosSum T g (N + 1) x at hpos
      rcases exists_birSum_eq_maxPosSum T g (N + 1) x with ⟨n, _, h_eq⟩
      rw [h_eq] at hpos
      rcases Nat.eq_zero_or_pos n with rfl | hn_pos
      · rw [birSum_zero] at hpos
        exact absurd hpos (lt_irrefl 0)
      · exact ⟨n, hn_pos, hpos⟩
  have hlim_pt : ∀ x : α,
      Tendsto (fun N : ℕ => (E_fin N).indicator g x) atTop (𝓝 (E.indicator g x)) := by
    intro x
    by_cases hx : x ∈ E
    · rcases (hE_iff x).mp hx with ⟨N₀, hN₀⟩
      rw [Set.indicator_of_mem hx]
      refine tendsto_atTop_of_eventually_const (i₀ := N₀) fun N hN => ?_
      have hxN : x ∈ E_fin N :=
        lt_of_lt_of_le hN₀ (maxPosSum_mono T g (Nat.succ_le_succ hN) x)
      exact Set.indicator_of_mem hxN g
    · rw [Set.indicator_of_notMem hx]
      refine tendsto_atTop_of_eventually_const (i₀ := 0) fun N _ => ?_
      have hxN : x ∉ E_fin N := fun h => hx ((hE_iff x).mpr ⟨N, h⟩)
      exact Set.indicator_of_notMem hxN g
  have hdom : Tendsto (fun N : ℕ => ∫ x, (E_fin N).indicator g x ∂μ) atTop
      (𝓝 (∫ x, E.indicator g x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
      (fun N => (hg_int.indicator (hE_fin_meas N)).aestronglyMeasurable) hg_int.norm
      (fun N => Eventually.of_forall fun x => norm_indicator_le_norm_self g x)
      (Eventually.of_forall hlim_pt)
  exact ge_of_tendsto' hdom hfin_nonneg

private lemma birkhoff_upper_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {T : α → α} (hT : Ergodic T μ) {g : α → ℝ}
    (hg_meas : Measurable g) (hg_int : Integrable g μ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * birSum T g n x < (∫ y, g y ∂μ) + ε := by
  let m : ℝ := ∫ y, g y ∂μ
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := half_pos hε
  let B : Set α := {x | ∃ k : ℕ, ∀ N : ℕ, ∃ n : ℕ,
    N ≤ n ∧ 1 ≤ n ∧ m + δ + ((k : ℝ) + 1)⁻¹ ≤ (n : ℝ)⁻¹ * birSum T g n x}
  have hB_eq : B = ⋃ k : ℕ, ⋂ N : ℕ, ⋃ n : ℕ,
      if N ≤ n ∧ 1 ≤ n then
        {x | m + δ + ((k : ℝ) + 1)⁻¹ ≤ (n : ℝ)⁻¹ * birSum T g n x}
      else ∅ := by
    ext x
    simp only [B, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
    refine exists_congr fun k => forall_congr' fun N => ?_
    constructor
    · rintro ⟨n, hNn, h1n, hineq⟩
      refine ⟨n, ?_⟩
      rw [if_pos ⟨hNn, h1n⟩]
      exact hineq
    · rintro ⟨n, hn⟩
      split_ifs at hn with hcond
      · exact ⟨n, hcond.1, hcond.2, hn⟩
      · exact False.elim hn
  have hB_meas : MeasurableSet B := by
    rw [hB_eq]
    refine MeasurableSet.iUnion fun k => MeasurableSet.iInter fun N =>
      MeasurableSet.iUnion fun n => ?_
    split_ifs
    · exact measurableSet_le measurable_const
        (measurable_const.mul (measurable_birSum hT.measurable hg_meas n))
    · exact MeasurableSet.empty
  have hB_inv : T ⁻¹' B = B := by
    ext x
    simp only [Set.mem_preimage, B, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨2 * k + 1, fun N => ?_⟩
      have hk_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      let η : ℝ := ((2 * k + 1 : ℕ) : ℝ) + 1
      have hη_eq : η⁻¹ = ((k : ℝ) + 1)⁻¹ / 2 := by
        dsimp [η]
        push_cast
        field_simp
        ring
      have hη_pos : 0 < η⁻¹ := by rw [hη_eq]; positivity
      rcases exists_nat_gt ((|g x| + |m + δ + η⁻¹|) / η⁻¹) with ⟨M₀, hM₀⟩
      rcases hk (max N M₀) with ⟨n, hn_max, hn1, hn_ineq⟩
      refine ⟨n + 1, by omega, by omega, ?_⟩
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
      have hsum_ge : (n : ℝ) * (m + δ + ((k : ℝ) + 1)⁻¹) ≤ birSum T g n (T x) :=
        (le_inv_mul_iff₀ hn_pos).mp hn_ineq
      have hM_le : (M₀ : ℝ) ≤ n := Nat.cast_le.mpr (le_trans (le_max_right N M₀) hn_max)
      have hgap : |g x| + |m + δ + η⁻¹| ≤ (n : ℝ) * η⁻¹ := by
        have h1 := (div_lt_iff₀ hη_pos).mp hM₀
        have h2 := mul_le_mul_of_nonneg_right hM_le hη_pos.le
        linarith
      have hgx : -(g x) ≤ |g x| := neg_le_abs _
      have hm_abs : m + δ + η⁻¹ ≤ |m + δ + η⁻¹| := le_abs_self _
      have hstep : ((n + 1 : ℕ) : ℝ) * (m + δ + η⁻¹) ≤ birSum T g (n + 1) x := by
        rw [birSum_succ', Nat.cast_add, Nat.cast_one]
        have h1 : (n : ℝ) * ((k : ℝ) + 1)⁻¹ = (n : ℝ) * η⁻¹ + (n : ℝ) * η⁻¹ := by
          rw [hη_eq]; ring
        nlinarith
      exact (le_inv_mul_iff₀ (by positivity)).mpr hstep
    · rintro ⟨k, hk⟩
      refine ⟨2 * k + 1, fun N => ?_⟩
      let η : ℝ := ((2 * k + 1 : ℕ) : ℝ) + 1
      have hη_eq : η⁻¹ = ((k : ℝ) + 1)⁻¹ / 2 := by
        dsimp [η]
        push_cast
        field_simp
        ring
      have hη_pos : 0 < η⁻¹ := by rw [hη_eq]; positivity
      rcases exists_nat_gt ((|g x| + |m + δ|) / η⁻¹) with ⟨M₀, hM₀⟩
      rcases hk (max (N + 1) (max (M₀ + 1) 2)) with ⟨n, hn_max, _, hn_ineq⟩
      have hn2 : 2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn_max
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hn'1 : 1 ≤ n' := by omega
      have hn'_N : N ≤ n' := by
        have : N + 1 ≤ n' + 1 := le_trans (le_max_left _ _) hn_max
        omega
      have hn'_M : (M₀ : ℝ) ≤ n' := by
        have : M₀ + 1 ≤ n' + 1 :=
          le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn_max
        exact Nat.cast_le.mpr (by omega)
      refine ⟨n', hn'_N, hn'1, ?_⟩
      have hsum_ge : ((n' + 1 : ℕ) : ℝ) * (m + δ + ((k : ℝ) + 1)⁻¹) ≤
          birSum T g (n' + 1) x :=
        (le_inv_mul_iff₀ (by positivity)).mp hn_ineq
      have hgap : |g x| + |m + δ| ≤ (n' : ℝ) * η⁻¹ := by
        have h1 := (div_lt_iff₀ hη_pos).mp hM₀
        have h2 := mul_le_mul_of_nonneg_right hn'_M hη_pos.le
        linarith
      have hgx : g x ≤ |g x| := le_abs_self _
      have hm_neg : -(m + δ) ≤ |m + δ| := neg_le_abs _
      have hstep : (n' : ℝ) * (m + δ + η⁻¹) ≤ birSum T g n' (T x) := by
        rw [birSum_succ', Nat.cast_add, Nat.cast_one] at hsum_ge
        have h1 : (n' : ℝ) * ((k : ℝ) + 1)⁻¹ = (n' : ℝ) * η⁻¹ + (n' : ℝ) * η⁻¹ := by
          rw [hη_eq]; ring
        nlinarith
      exact (le_inv_mul_iff₀ (Nat.cast_pos.mpr hn'1)).mpr hstep
  have hB_zero : μ B = 0 := by
    rcases hT.prob_eq_zero_or_one hB_meas hB_inv with h0 | h1
    · exact h0
    · exfalso
      let h : α → ℝ := fun x => g x - (m + δ)
      have hh_meas : Measurable h := hg_meas.sub measurable_const
      have hh_int : Integrable h μ := hg_int.sub (integrable_const _)
      have hhopf := hopf_maximal_ergodic hT.toMeasurePreserving hh_meas hh_int
      let Eh : Set α := {y | ∃ n : ℕ, 1 ≤ n ∧ 0 < birSum T h n y}
      have hB_sub : B ⊆ Eh := by
        intro x ⟨k, hk⟩
        rcases hk 1 with ⟨n, _, hn1, hn_ineq⟩
        refine ⟨n, hn1, ?_⟩
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
        have hbir_h : birSum T h n x = birSum T g n x - (n : ℝ) * (m + δ) := by
          unfold birSum h
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [hbir_h]
        have hge := (le_inv_mul_iff₀ hn_pos).mp hn_ineq
        have hk_inv : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
        nlinarith
      have hBc_zero : μ Bᶜ = 0 := (prob_compl_eq_zero_iff hB_meas).mpr h1
      have hEhc_zero : μ Ehᶜ = 0 := measure_mono_null (Set.compl_subset_compl.mpr hB_sub) hBc_zero
      have hae_eq : Eh.indicator h =ᵐ[μ] h := by
        change ∀ᵐ x ∂μ, Eh.indicator h x = h x
        rw [ae_iff]
        refine measure_mono_null (fun x hx => ?_) hEhc_zero
        intro hxEh
        exact hx (Set.indicator_of_mem hxEh h)
      have hint_eq : ∫ x, Eh.indicator h x ∂μ = ∫ x, h x ∂μ := integral_congr_ae hae_eq
      have hint_h : ∫ x, h x ∂μ = -δ := by
        dsimp [h]
        rw [integral_sub hg_int (integrable_const _), integral_const, probReal_univ, one_smul]
        dsimp [m]
        ring
      linarith [hhopf, hint_eq, hint_h]
  have hae_notB : ∀ᵐ x ∂μ, x ∉ B := ae_iff.mpr (by simpa using hB_zero)
  rcases exists_nat_gt δ⁻¹ with ⟨k₀, hk₀⟩
  have hk₀_lt : ((k₀ : ℝ) + 1)⁻¹ < δ := by
    refine (inv_lt_comm₀ (by positivity) hδ).mpr ?_
    linarith
  refine hae_notB.mono fun x hx => ?_
  have hnot : ¬ ∀ N : ℕ, ∃ n : ℕ,
      N ≤ n ∧ 1 ≤ n ∧ m + δ + ((k₀ : ℝ) + 1)⁻¹ ≤ (n : ℝ)⁻¹ * birSum T g n x :=
    fun hall => hx ⟨k₀, hall⟩
  rcases not_forall.mp hnot with ⟨N₀, hN₀⟩
  rw [eventually_atTop]
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hlt : (n : ℝ)⁻¹ * birSum T g n x < m + δ + ((k₀ : ℝ) + 1)⁻¹ := by
    by_contra hge
    exact hN₀ ⟨n, le_trans (le_max_left _ _) hn, le_trans (le_max_right _ _) hn, not_lt.mp hge⟩
  dsimp [m, δ] at hlt hk₀_lt ⊢
  linarith

private lemma birkhoff_ergodic {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {T : α → α} (hT : Ergodic T μ) {g : α → ℝ}
    (hg_meas : Measurable g) (hg_int : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * birSum T g n x) atTop (𝓝 (∫ y, g y ∂μ)) := by
  let m : ℝ := ∫ y, g y ∂μ
  have hup_all : ∀ᵐ x ∂μ, ∀ j : ℕ,
      ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * birSum T g n x < m + ((j : ℝ) + 1)⁻¹ :=
    ae_all_iff.mpr fun j => birkhoff_upper_ae hT hg_meas hg_int (by positivity)
  have hlow_all : ∀ᵐ x ∂μ, ∀ j : ℕ,
      ∀ᶠ n : ℕ in atTop, -(m - ((j : ℝ) + 1)⁻¹) > (n : ℝ)⁻¹ * birSum T (-g) n x := by
    have hneg := ae_all_iff.mpr fun j : ℕ =>
      birkhoff_upper_ae hT hg_meas.neg hg_int.neg (ε := ((j : ℝ) + 1)⁻¹) (by positivity)
    refine hneg.mono fun x hx j => (hx j).mono fun n hn => ?_
    have hint_neg : ∫ y, (-g) y ∂μ = -m := integral_neg g
    rw [hint_neg] at hn
    linarith
  refine (hup_all.and hlow_all).mono fun x ⟨hup, hlow⟩ => ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases exists_nat_gt ε⁻¹ with ⟨j, hj⟩
  have hj_lt : ((j : ℝ) + 1)⁻¹ < ε := (inv_lt_comm₀ (by positivity) hε).mpr (by linarith)
  rcases eventually_atTop.mp ((hup j).and (hlow j)) with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  rcases hN n hn with ⟨h1, h2⟩
  have hbir_neg : birSum T (-g) n x = -birSum T g n x := by
    unfold birSum
    simp [Finset.sum_neg_distrib]
  rw [hbir_neg] at h2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

private lemma seqShift_iterate_zero (s : ℕ → ℝ) (k : ℕ) :
    (GenEmpLik.Expansion.seqShift^[k] s) 0 = s k := by
  suffices ∀ m : ℕ, (GenEmpLik.Expansion.seqShift^[k] s) m = s (m + k) by
    simpa using this 0
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    intro m
    rw [Function.iterate_succ_apply, ih]
    unfold GenEmpLik.Expansion.seqShift
    rfl

private lemma ereal_nonneg_mul_nonneg {c : ℝ} (hc : 0 ≤ c) {x : EReal} (hx : 0 ≤ x) :
    (0 : EReal) ≤ (c : EReal) * x := by
  induction x using EReal.rec with
  | bot => exact absurd hx (by simp)
  | coe rx =>
    have hrx : 0 ≤ rx := EReal.coe_le_coe_iff.mp hx
    rw [← EReal.coe_mul]
    exact EReal.coe_le_coe_iff.mpr (mul_nonneg hc hrx)
  | top =>
    rcases eq_or_lt_of_le hc with rfl | hc_pos
    · simp
    · rw [EReal.coe_mul_top_of_pos hc_pos]
      exact le_top

private lemma ereal_pos_mul_pos {c : ℝ} (hc : 0 < c) {x : EReal} (hx : 0 < x) :
    (0 : EReal) < (c : EReal) * x := by
  induction x using EReal.rec with
  | bot => exact absurd hx (by simp)
  | coe rx =>
    have hrx : 0 < rx := EReal.coe_lt_coe_iff.mp hx
    rw [← EReal.coe_mul]
    exact EReal.coe_lt_coe_iff.mpr (mul_pos hc hrx)
  | top =>
    rw [EReal.coe_mul_top_of_pos hc]
    exact EReal.coe_lt_top 0

open GenEmpLik.Expansion in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (f : ℝ → EReal) (hA : AssumptionA f) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (Z : ℕ → Ω → ℝ) (hZ : IsStationaryErgodic Z P)
    (hmom : Integrable (fun ω => Z 0 ω ^ 2) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => Real.sqrt n *
      |robustMean f ρ (fun i : Fin n => Z i ω) - empMean (fun i : Fin n => Z i ω) -
        Real.sqrt (ρ / n * empVar (fun i : Fin n => Z i ω))|) atTop (𝓝 0) := by
  rcases eq_or_lt_of_le hρ with rfl | hρ_pos
  · -- Case ρ = 0
    rcases eq_30 f hA with ⟨c, C, hc_pos, hC_pos, h30⟩
    let ε₀ : ℝ := min c (1 / (2 * C))
    have hε₀_pos : 0 < ε₀ := lt_min hc_pos (by positivity)
    have hε₀_le : ε₀ ≤ c := min_le_left _ _
    have h1Cε₀ : 0 < 2 * (1 - C * ε₀) := by
      have h1 : ε₀ ≤ 1 / (2 * C) := min_le_right _ _
      have h2 : ε₀ * (2 * C) ≤ 1 := (le_div_iff₀ (by positivity)).mp h1
      linarith
    have hlow₀ := (h30 ε₀ hε₀_pos hε₀_le).1
    have hf_nonneg : ∀ s : ℝ, 0 ≤ s → (0 : EReal) ≤ f s := by
      intro s hs
      have h1 := hlow₀ (s - 1) (by linarith)
      rw [sub_add_cancel] at h1
      have hhub_nonneg : 0 ≤ huber ε₀ (s - 1) := by
        unfold huber
        split_ifs with h
        · positivity
        · have h' : ε₀ < |s - 1| := not_le.mp h
          nlinarith
      exact le_trans (EReal.coe_le_coe_iff.mpr (mul_nonneg h1Cε₀.le hhub_nonneg)) h1
    have hf_pos_of_ne_one : ∀ s : ℝ, 0 ≤ s → s ≠ 1 → (0 : EReal) < f s := by
      intro s hs hs1
      have h1 := hlow₀ (s - 1) (by linarith)
      rw [sub_add_cancel] at h1
      have hhub_pos : 0 < huber ε₀ (s - 1) := by
        unfold huber
        split_ifs with h
        · have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
          positivity
        · have h' : ε₀ < |s - 1| := not_le.mp h
          nlinarith
      exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (mul_pos h1Cε₀ hhub_pos)) h1
    refine Eventually.of_forall fun ω => ?_
    refine tendsto_atTop_of_eventually_const (i₀ := 1) fun n hn1 => ?_
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    let z : Fin n → ℝ := fun i => Z i ω
    have hrob_eq : robustMean f 0 z = empMean z := by
      unfold robustMean
      let p₀ : Fin n → ℝ := fun _ => (1 : ℝ) / n
      have hp₀_mem : p₀ ∈ PhiDivRobust.Counterpart.probUncertaintySet f p₀ (0 / n) := by
        refine ⟨fun _ => by positivity, ?_, ?_⟩
        · simp only [p₀, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
        · unfold PhiDivRobust.Counterpart.phiDiv
          have hdiv1 : ∀ i : Fin n, p₀ i / p₀ i = 1 := fun _ => div_self (by positivity)
          simp_rw [hdiv1, hA.1.map_one, mul_zero, Finset.sum_const_zero, zero_div]
          exact le_rfl
      have hp_unique : ∀ p ∈ PhiDivRobust.Counterpart.probUncertaintySet f p₀ (0 / n), p = p₀ := by
        rintro p ⟨hp_nonneg, _, hp_div⟩
        ext i
        by_contra hne
        unfold PhiDivRobust.Counterpart.phiDiv at hp_div
        rw [zero_div] at hp_div
        let term : Fin n → EReal := fun j => (p₀ j : EReal) * f (p j / p₀ j)
        have hterm_nonneg : ∀ j : Fin n, 0 ≤ term j := fun j =>
          ereal_nonneg_mul_nonneg (by positivity) (hf_nonneg _ (div_nonneg (hp_nonneg j) (by positivity)))
        have hi_ne1 : p i / p₀ i ≠ 1 := by
          intro heq
          exact hne ((div_eq_one_iff_eq (by positivity)).mp heq)
        have hi_pos : 0 < term i :=
          ereal_pos_mul_pos (by positivity)
            (hf_pos_of_ne_one _ (div_nonneg (hp_nonneg i) (by positivity)) hi_ne1)
        have hle : term i ≤ ∑ j, term j :=
          Finset.single_le_sum (fun j _ => hterm_nonneg j) (Finset.mem_univ i)
        exact not_lt_of_ge (le_trans hle hp_div) hi_pos
      have himg : ((fun p : Fin n → ℝ => ∑ i, p i * z i) ''
          PhiDivRobust.Counterpart.probUncertaintySet f p₀ (0 / n)) = {empMean z} := by
        ext y
        simp only [Set.mem_image, Set.mem_singleton_iff]
        constructor
        · rintro ⟨p, hp, rfl⟩
          rw [hp_unique p hp]
          dsimp [p₀, empMean]
          rw [← Finset.mul_sum, one_div]
        · rintro rfl
          refine ⟨p₀, hp₀_mem, ?_⟩
          dsimp [p₀, empMean]
          rw [← Finset.mul_sum, one_div]
      rw [himg, csSup_singleton]
    change Real.sqrt n * |robustMean f 0 z - empMean z - Real.sqrt (0 / n * empVar z)| = 0
    rw [hrob_eq, sub_self, zero_div, zero_mul, Real.sqrt_zero, sub_zero, abs_zero, mul_zero]
  · -- Case ρ > 0
    have hZ0_int : Integrable (Z 0) P := by
      refine ((integrable_const (1 : ℝ)).add hmom).mono' (hZ.1 0).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      simp only [Pi.add_apply, Real.norm_eq_abs]
      have hsq : 0 ≤ (|Z 0 ω| - 1) ^ 2 := sq_nonneg _
      have habs2 : |Z 0 ω| ^ 2 = Z 0 ω ^ 2 := sq_abs _
      nlinarith
    let Φ : Ω → (ℕ → ℝ) := fun ω k => Z k ω
    have hΦ_meas : Measurable Φ := measurable_pi_iff.mpr hZ.1
    let μZ : Measure (ℕ → ℝ) := P.map Φ
    have : IsProbabilityMeasure μZ := Measure.isProbabilityMeasure_map hΦ_meas.aemeasurable
    have hident : ∀ i : ℕ, IdentDistrib (Z i) (Z 0) P P := by
      intro i
      refine ⟨(hZ.1 i).aemeasurable, (hZ.1 0).aemeasurable, ?_⟩
      have hZi_eq : Z i = (fun s : ℕ → ℝ => s 0) ∘ (seqShift^[i]) ∘ Φ := by
        ext ω
        simp [Φ, seqShift_iterate_zero]
      have hZ0_eq : Z 0 = (fun s : ℕ → ℝ => s 0) ∘ Φ := rfl
      have hmp_i : μZ.map (seqShift^[i]) = μZ :=
        (hZ.2.toMeasurePreserving.iterate i).map_eq
      rw [hZi_eq, ← Measure.map_map (measurable_pi_apply 0)
          ((hZ.2.measurable.iterate i).comp hΦ_meas),
        ← Measure.map_map (hZ.2.measurable.iterate i) hΦ_meas,
        hmp_i, hZ0_eq, ← Measure.map_map (measurable_pi_apply 0) hΦ_meas]
    let m : ℝ := ∫ ω, Z 0 ω ∂P
    let m2 : ℝ := ∫ ω, Z 0 ω ^ 2 ∂P
    let σ2 : ℝ := m2 - m ^ 2
    have hσ2_eq : σ2 = ∫ ω, (Z 0 ω - m) ^ 2 ∂P := by
      have hexp : ∀ ω, (Z 0 ω - m) ^ 2 = (Z 0 ω ^ 2 - (2 * m) * Z 0 ω) + m ^ 2 := fun ω => by ring
      simp_rw [hexp]
      have h1 : Integrable (fun ω => Z 0 ω ^ 2 - (2 * m) * Z 0 ω) P :=
        hmom.sub (hZ0_int.const_mul (2 * m))
      have h2 : Integrable (fun _ : Ω => m ^ 2) P := integrable_const (m ^ 2)
      have h3 : Integrable (fun ω => (2 * m) * Z 0 ω) P := hZ0_int.const_mul (2 * m)
      rw [integral_add h1 h2, integral_sub hmom h3, integral_const_mul,
        integral_const, probReal_univ, one_smul]
      dsimp [σ2, m2, m]
      ring
    have hσ2_nonneg : 0 ≤ σ2 := by
      rw [hσ2_eq]
      exact integral_nonneg fun ω => sq_nonneg _
    rcases eq_30 f hA with ⟨c, C, hc_pos, hC_pos, h30⟩
    rcases eq_or_lt_of_le hσ2_nonneg with hσ2_zero | hσ2_pos
    · -- Degenerate variance σ² = 0
      have hZ0_ae : ∀ᵐ ω ∂P, Z 0 ω = m := by
        have hint0 : ∫ ω, (Z 0 ω - m) ^ 2 ∂P = 0 := by rw [← hσ2_eq, ← hσ2_zero]
        have hint_dev : Integrable (fun ω => (Z 0 ω - m) ^ 2) P := by
          have hexp : (fun ω => (Z 0 ω - m) ^ 2) =
              fun ω => (Z 0 ω ^ 2 - (2 * m) * Z 0 ω) + m ^ 2 := by ext ω; ring
          rw [hexp]
          exact (hmom.sub (hZ0_int.const_mul _)).add (integrable_const _)
        have hae_sq := (integral_eq_zero_iff_of_nonneg_ae
          (Eventually.of_forall fun ω => sq_nonneg (Z 0 ω - m)) hint_dev).mp hint0
        refine hae_sq.mono fun ω hω => sub_eq_zero.mp (sq_eq_zero_iff.mp hω)
      have hZi_ae : ∀ᵐ ω ∂P, ∀ i : ℕ, Z i ω = m := by
        rw [ae_all_iff]
        intro i
        have hnull0 : P {ω | Z 0 ω ≠ m} = 0 := ae_iff.mp hZ0_ae
        have hmeas_ne : MeasurableSet {x : ℝ | x ≠ m} := (measurableSet_singleton m).compl
        have heq_map : P.map (Z i) {x : ℝ | x ≠ m} = P.map (Z 0) {x : ℝ | x ≠ m} := by
          rw [(hident i).map_eq]
        rw [Measure.map_apply (hZ.1 i) hmeas_ne, Measure.map_apply (hZ.1 0) hmeas_ne] at heq_map
        exact ae_iff.mpr (heq_map.trans hnull0)
      let ε₀ : ℝ := min (min c (1 / 2)) (1 / (2 * C))
      have hε₀_pos : 0 < ε₀ := lt_min (lt_min hc_pos (by norm_num)) (by positivity)
      have hε₀_le_c : ε₀ ≤ c := le_trans (min_le_left _ _) (min_le_left _ _)
      have hε₀_lt1 : ε₀ < 1 := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by norm_num)
      have hCε₀_lt1 : C * ε₀ < 1 := by
        have h1 : ε₀ ≤ 1 / (2 * C) := min_le_right _ _
        have h2 : ε₀ * (2 * C) ≤ 1 := (le_div_iff₀ (by positivity)).mp h1
        linarith
      obtain ⟨hlow₀, hup₀⟩ := h30 ε₀ hε₀_pos hε₀_le_c
      refine hZi_ae.mono fun ω hω => ?_
      refine tendsto_atTop_of_eventually_const (i₀ := 1) fun n hn1 => ?_
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
      let z : Fin n → ℝ := fun i => Z i ω
      have hz_const : ∀ i : Fin n, z i = m := fun i => hω i
      have hemp_m : empMean z = m := by
        dsimp [empMean]
        simp_rw [hz_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      have hemp_v : empVar z = 0 := by
        dsimp [empVar]
        rw [hemp_m]
        simp_rw [hz_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
        ring
      have hsup0 : (⨆ i : Fin n, |z i - empMean z|) / Real.sqrt n ≤
          ε₀ * Real.sqrt (empVar z) * Real.sqrt ((1 - C * ε₀) / ρ) := by
        have : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
        have h0 : (⨆ i : Fin n, |z i - empMean z|) = 0 := by
          simp_rw [hz_const, hemp_m, sub_self, abs_zero, ciSup_const]
        rw [h0, zero_div, hemp_v, Real.sqrt_zero, mul_zero, zero_mul]
      have h6 := lemma_6 f hA hn1 hρ_pos hε₀_pos hε₀_lt1 hC_pos.le hCε₀_lt1 hlow₀ hup₀ z hsup0
      simp only [hemp_m, hemp_v, mul_zero, Real.sqrt_zero, zero_mul, add_zero] at h6
      have hrob_m : robustMean f ρ z = m := le_antisymm h6.2 h6.1
      change Real.sqrt n * |robustMean f ρ z - empMean z - Real.sqrt (ρ / n * empVar z)| = 0
      rw [hrob_m, hemp_m, hemp_v, sub_self, mul_zero, Real.sqrt_zero, sub_zero, abs_zero, mul_zero]
    · -- Nondegenerate variance σ² > 0
      let g1 : (ℕ → ℝ) → ℝ := fun s => s 0
      let g2 : (ℕ → ℝ) → ℝ := fun s => s 0 ^ 2
      have hg1_meas : Measurable g1 := measurable_pi_apply 0
      have hg2_meas : Measurable g2 := (measurable_pi_apply 0).pow_const 2
      have hg1_int : Integrable g1 μZ :=
        (integrable_map_measure hg1_meas.aestronglyMeasurable hΦ_meas.aemeasurable).mpr hZ0_int
      have hg2_int : Integrable g2 μZ :=
        (integrable_map_measure hg2_meas.aestronglyMeasurable hΦ_meas.aemeasurable).mpr hmom
      have hg1_mean : ∫ s, g1 s ∂μZ = m := integral_map hΦ_meas.aemeasurable hg1_meas.aestronglyMeasurable
      have hg2_mean : ∫ s, g2 s ∂μZ = m2 := integral_map hΦ_meas.aemeasurable hg2_meas.aestronglyMeasurable
      have hbir1_μZ := birkhoff_ergodic hZ.2 hg1_meas hg1_int
      have hbir2_μZ := birkhoff_ergodic hZ.2 hg2_meas hg2_int
      rw [hg1_mean] at hbir1_μZ
      rw [hg2_mean] at hbir2_μZ
      have hmeas_t1 : MeasurableSet {s : ℕ → ℝ |
          Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * birSum seqShift g1 n s) atTop (𝓝 m)} :=
        measurableSet_tendsto _ fun n =>
          measurable_const.mul (measurable_birSum hZ.2.measurable hg1_meas n)
      have hmeas_t2 : MeasurableSet {s : ℕ → ℝ |
          Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * birSum seqShift g2 n s) atTop (𝓝 m2)} :=
        measurableSet_tendsto _ fun n =>
          measurable_const.mul (measurable_birSum hZ.2.measurable hg2_meas n)
      have hae_mean : ∀ᵐ ω ∂P,
          Tendsto (fun n : ℕ => empMean (fun i : Fin n => Z i ω)) atTop (𝓝 m) := by
        have h1 := (ae_map_iff hΦ_meas.aemeasurable hmeas_t1).mp hbir1_μZ
        refine h1.mono fun ω hω => hω.congr fun n => ?_
        dsimp [empMean, birSum, g1, Φ]
        congr 1
        rw [← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact seqShift_iterate_zero (fun k => Z k ω) i
      have hae_sq_mean : ∀ᵐ ω ∂P,
          Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, Z i ω ^ 2) atTop (𝓝 m2) := by
        have h2 := (ae_map_iff hΦ_meas.aemeasurable hmeas_t2).mp hbir2_μZ
        refine h2.mono fun ω hω => hω.congr fun n => ?_
        dsimp [birSum, g2, Φ]
        congr 1
        rw [← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [seqShift_iterate_zero (fun k => Z k ω) i]
      have hae_var : ∀ᵐ ω ∂P,
          Tendsto (fun n : ℕ => empVar (fun i : Fin n => Z i ω)) atTop (𝓝 σ2) := by
        refine (hae_sq_mean.and hae_mean).mono fun ω ⟨h2, h1⟩ => ?_
        dsimp [σ2]
        exact h2.sub (h1.pow 2)
      have hmom_abs : Integrable (fun ω => |Z 0 ω| ^ (2 : ℝ)) P := by
        refine hmom.congr (Eventually.of_forall fun ω => ?_)
        dsimp only
        rw [Real.rpow_two, sq_abs]
      have hae_max : ∀ᵐ ω ∂P,
          Tendsto (fun n : ℕ => (⨆ i : Fin n, |Z i ω|) / Real.sqrt n) atTop (𝓝 0) := by
        have h7 := (lemma_7 Z hident (by norm_num : (0 : ℝ) < 2) hmom_abs).2
        refine h7.mono fun ω hω => hω.congr fun n => ?_
        rw [Real.sqrt_eq_rpow]
      refine (hae_mean.and (hae_var.and hae_max)).mono fun ω ⟨hmean_lim, hvar_lim, hmax_lim⟩ => ?_
      have hdev_lim : Tendsto (fun n : ℕ =>
          (⨆ i : Fin n, |Z i ω - empMean (fun j : Fin n => Z j ω)|) / Real.sqrt n) atTop (𝓝 0) := by
        have hinv_sqrt : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) := by
          refine tendsto_inv_atTop_zero.comp ?_
          rw [tendsto_atTop_atTop]
          intro b
          rcases exists_nat_gt (max b 0 ^ 2) with ⟨N, hN⟩
          refine ⟨N, fun n hn => ?_⟩
          have hb_le : max b 0 ≤ Real.sqrt n := by
            rw [← Real.sqrt_sq (le_max_right b 0)]
            exact Real.sqrt_le_sqrt (le_trans hN.le (Nat.cast_le.mpr hn))
          exact le_trans (le_max_left b 0) hb_le
        have hemp_div : Tendsto (fun n : ℕ =>
            |empMean (fun j : Fin n => Z j ω)| / Real.sqrt n) atTop (𝓝 0) := by
          have h := hmean_lim.abs.mul hinv_sqrt
          rw [mul_zero] at h
          exact h.congr fun n => (div_eq_mul_inv _ _).symm
        have hupper_lim : Tendsto (fun n : ℕ =>
            (⨆ i : Fin n, |Z i ω|) / Real.sqrt n +
              |empMean (fun j : Fin n => Z j ω)| / Real.sqrt n) atTop (𝓝 0) := by
          simpa using hmax_lim.add hemp_div
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper_lim
          (eventually_atTop.mpr ⟨1, fun n hn1 => ?_⟩)
          (eventually_atTop.mpr ⟨1, fun n hn1 => ?_⟩)
        · have : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
          exact div_nonneg (le_ciSup_of_le (Set.toFinite _ |>.bddAbove) ⟨0, hn1⟩ (abs_nonneg _))
            (Real.sqrt_nonneg _)
        · have : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
          rw [← add_div]
          refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          refine ciSup_le fun i => ?_
          calc |Z i ω - empMean (fun j : Fin n => Z j ω)|
              ≤ |Z i ω| + |empMean (fun j : Fin n => Z j ω)| := abs_sub _ _
            _ ≤ (⨆ k : Fin n, |Z k ω|) + |empMean (fun j : Fin n => Z j ω)| :=
                add_le_add_left
                  (le_ciSup (f := fun k : Fin n => |Z k ω|) (Set.toFinite _ |>.bddAbove) i) _
      rw [Metric.tendsto_atTop]
      intro δ hδ_pos
      let K_scale : ℝ := Real.sqrt (ρ * (σ2 + 1))
      have hK_pos : 0 < K_scale := Real.sqrt_pos.mpr (by positivity)
      have hcont_err : ContinuousAt (fun x : ℝ =>
          max (1 / Real.sqrt (1 - C * x) - 1) (1 - 1 / Real.sqrt (1 + C * x)) * K_scale) 0 := by
        have h1 : ContinuousAt (fun x : ℝ => 1 / Real.sqrt (1 - C * x) - 1) 0 := by
          refine (continuousAt_const.div ?_ (by simp)).sub continuousAt_const
          exact Real.continuous_sqrt.continuousAt.comp
            (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
        have h2 : ContinuousAt (fun x : ℝ => 1 - 1 / Real.sqrt (1 + C * x)) 0 := by
          refine continuousAt_const.sub (continuousAt_const.div ?_ (by simp))
          exact Real.continuous_sqrt.continuousAt.comp
            (continuousAt_const.add (continuousAt_const.mul continuousAt_id))
        exact (h1.max h2).mul continuousAt_const
      have herr0 : max (1 / Real.sqrt (1 - C * 0) - 1) (1 - 1 / Real.sqrt (1 + C * 0)) *
          K_scale = 0 := by simp
      rcases (Metric.continuousAt_iff.mp hcont_err) δ hδ_pos with ⟨r, hr_pos, hr_spec⟩
      let ε : ℝ := min (min c (1 / 2)) (min (1 / (2 * C)) (r / 2))
      have hε_pos : 0 < ε :=
        lt_min (lt_min hc_pos (by norm_num)) (lt_min (by positivity) (by linarith))
      have hε_le_c : ε ≤ c := le_trans (min_le_left _ _) (min_le_left _ _)
      have hε_lt1 : ε < 1 :=
        lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by norm_num)
      have hCε_lt1 : C * ε < 1 := by
        have h1 : ε ≤ 1 / (2 * C) := le_trans (min_le_right _ _) (min_le_left _ _)
        have h2 : ε * (2 * C) ≤ 1 := (le_div_iff₀ (by positivity)).mp h1
        linarith
      have herr_lt_δ : max (1 / Real.sqrt (1 - C * ε) - 1) (1 - 1 / Real.sqrt (1 + C * ε)) *
          K_scale < δ := by
        have hdist_ε : dist ε 0 < r := by
          rw [Real.dist_eq, sub_zero, abs_of_pos hε_pos]
          have : ε ≤ r / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
          linarith
        have h := hr_spec hdist_ε
        rw [herr0, Real.dist_eq, sub_zero] at h
        exact lt_of_le_of_lt (le_abs_self _) h
      obtain ⟨hlow, hup⟩ := h30 ε hε_pos hε_le_c
      have hev_var : ∀ᶠ n : ℕ in atTop,
          σ2 / 2 ≤ empVar (fun i : Fin n => Z i ω) ∧
            empVar (fun i : Fin n => Z i ω) ≤ σ2 + 1 := by
        have hlt1 : σ2 / 2 < σ2 := by linarith
        have hlt2 : σ2 < σ2 + 1 := by linarith
        exact (hvar_lim.eventually (Ici_mem_nhds hlt1)).and
          (hvar_lim.eventually (Iic_mem_nhds hlt2))
      let thresh : ℝ := ε * Real.sqrt (σ2 / 2) * Real.sqrt ((1 - C * ε) / ρ)
      have hthresh_pos : 0 < thresh := by
        dsimp [thresh]
        have h1 : 0 < 1 - C * ε := by linarith
        positivity
      have hev_dev : ∀ᶠ n : ℕ in atTop,
          (⨆ i : Fin n, |Z i ω - empMean (fun j : Fin n => Z j ω)|) / Real.sqrt n ≤ thresh :=
        hdev_lim.eventually (Iic_mem_nhds hthresh_pos)
      rcases eventually_atTop.mp (hev_var.and hev_dev) with ⟨N₀, hN₀⟩
      refine ⟨max N₀ 1, fun n hn => ?_⟩
      have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
      rcases hN₀ n (le_trans (le_max_left _ _) hn) with ⟨⟨hvar_lo, hvar_hi⟩, hdev_le⟩
      let z : Fin n → ℝ := fun i => Z i ω
      have hE : (⨆ i : Fin n, |z i - empMean z|) / Real.sqrt n ≤
          ε * Real.sqrt (empVar z) * Real.sqrt ((1 - C * ε) / ρ) := by
        refine le_trans hdev_le ?_
        dsimp [thresh]
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvar_lo) hε_pos.le) (Real.sqrt_nonneg _)
      have h6 := lemma_6 f hA hn1 hρ_pos hε_pos hε_lt1 hC_pos.le hCε_lt1 hlow hup z hE
      have hvar_nonneg : 0 ≤ empVar z := by linarith
      have hmul_sqrt : Real.sqrt n * Real.sqrt (ρ / n * empVar z) =
          Real.sqrt (ρ * empVar z) := by
        rw [← Real.sqrt_mul hn_pos.le]
        congr 1
        field_simp
      have hdiff_lo : -(1 - 1 / Real.sqrt (1 + C * ε)) * Real.sqrt (ρ * empVar z) ≤
          Real.sqrt n * (robustMean f ρ z - empMean z - Real.sqrt (ρ / n * empVar z)) := by
        have hsub : Real.sqrt (ρ / n * empVar z) * (1 / Real.sqrt (1 + C * ε) - 1) ≤
            robustMean f ρ z - empMean z - Real.sqrt (ρ / n * empVar z) := by linarith [h6.1]
        have hmul := mul_le_mul_of_nonneg_left hsub (Real.sqrt_nonneg n)
        calc -(1 - 1 / Real.sqrt (1 + C * ε)) * Real.sqrt (ρ * empVar z)
            = Real.sqrt n * (Real.sqrt (ρ / n * empVar z) * (1 / Real.sqrt (1 + C * ε) - 1)) := by
              rw [← hmul_sqrt]; ring
          _ ≤ Real.sqrt n * (robustMean f ρ z - empMean z - Real.sqrt (ρ / n * empVar z)) := hmul
      have hdiff_hi : Real.sqrt n * (robustMean f ρ z - empMean z - Real.sqrt (ρ / n * empVar z)) ≤
          (1 / Real.sqrt (1 - C * ε) - 1) * Real.sqrt (ρ * empVar z) := by
        have hsub : robustMean f ρ z - empMean z - Real.sqrt (ρ / n * empVar z) ≤
            Real.sqrt (ρ / n * empVar z) * (1 / Real.sqrt (1 - C * ε) - 1) := by linarith [h6.2]
        have hmul := mul_le_mul_of_nonneg_left hsub (Real.sqrt_nonneg n)
        calc Real.sqrt n * (robustMean f ρ z - empMean z - Real.sqrt (ρ / n * empVar z))
            ≤ Real.sqrt n * (Real.sqrt (ρ / n * empVar z) * (1 / Real.sqrt (1 - C * ε) - 1)) := hmul
          _ = (1 / Real.sqrt (1 - C * ε) - 1) * Real.sqrt (ρ * empVar z) := by
              rw [← hmul_sqrt]; ring
      let M_err : ℝ := max (1 / Real.sqrt (1 - C * ε) - 1) (1 - 1 / Real.sqrt (1 + C * ε))
      have hM_nonneg : 0 ≤ M_err := by
        refine le_trans ?_ (le_max_right _ _)
        have hle1 : Real.sqrt 1 ≤ Real.sqrt (1 + C * ε) := Real.sqrt_le_sqrt (by nlinarith)
        rw [Real.sqrt_one] at hle1
        have hdiv : 1 / Real.sqrt (1 + C * ε) ≤ 1 := div_le_one_of_le₀ hle1 (Real.sqrt_nonneg _)
        linarith
      have habs_le : |Real.sqrt n * (robustMean f ρ z - empMean z - Real.sqrt (ρ / n * empVar z))| ≤
          M_err * Real.sqrt (ρ * empVar z) := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · have : -(M_err * Real.sqrt (ρ * empVar z)) ≤
              -(1 - 1 / Real.sqrt (1 + C * ε)) * Real.sqrt (ρ * empVar z) := by
            rw [neg_mul]
            exact neg_le_neg (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))
          linarith
        · exact le_trans hdiff_hi
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
      have hscale_le : Real.sqrt (ρ * empVar z) ≤ K_scale :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hvar_hi hρ_pos.le)
      have hdist_eq : dist (Real.sqrt n *
          |robustMean f ρ z - empMean z - Real.sqrt (ρ / n * empVar z)|) 0 =
          |Real.sqrt n * (robustMean f ρ z - empMean z - Real.sqrt (ρ / n * empVar z))| := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)),
          abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      change dist (Real.sqrt n *
        |robustMean f ρ z - empMean z - Real.sqrt (ρ / n * empVar z)|) 0 < δ
      rw [hdist_eq]
      exact lt_of_le_of_lt
        (le_trans habs_le (mul_le_mul_of_nonneg_left hscale_le hM_nonneg)) herr_lt_δ
