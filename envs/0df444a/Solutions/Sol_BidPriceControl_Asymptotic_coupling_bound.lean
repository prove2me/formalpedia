-- Prove2me | solution 1 for BidPriceControl.Asymptotic.coupling_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T10:16:28.343499+00:00
-- url     : https://prove2.me/submissions/aa07b898-4035-4a48-b47a-fc49909df21d

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model

open MeasureTheory ProbabilityTheory Filter

namespace Aux_BPC_cpl
open BidPriceControl.Asymptotic

lemma sum_Icc_one (N : ℕ) (f : ℕ → ℝ) :
    ∑ t ∈ Finset.Icc 1 N, f t = ∑ u ∈ Finset.range N, f (u + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma sum_fin_rev (K : ℕ) (f : ℕ → ℝ) :
    ∑ s : Fin K, f (K - (s : ℕ)) = ∑ t ∈ Finset.Icc 1 K, f t := by
  rw [Fin.sum_univ_eq_sum_range (fun u => f (K - u)) K, sum_Icc_one]
  rw [← Finset.sum_range_reflect (fun u => f (u + 1)) K]
  apply Finset.sum_congr rfl
  intro u hu
  have := Finset.mem_range.mp hu
  congr 1
  omega

/-- Leg-`i` seats of the alternate (uncapacitated) system in one period. -/
noncomputable def phiN {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (i : Fin m)
    (r : Fin n → ℝ) : ℝ :=
  ∑ j, if bidSum A μ j < r j then (A i j : ℝ) else 0

/-- Revenue of the alternate (uncapacitated) system in one period. -/
noncomputable def phiA {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ)
    (r : Fin n → ℝ) : ℝ :=
  ∑ j, if bidSum A μ j < r j then r j else 0

lemma bidSum_nonneg {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (hμ : 0 ≤ μ) (j : Fin n) :
    0 ≤ bidSum A μ j :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hμ i) (Nat.cast_nonneg _)

lemma phiN_nonneg {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (i : Fin m)
    (r : Fin n → ℝ) : 0 ≤ phiN A μ i r :=
  Finset.sum_nonneg fun j _ => by split_ifs <;> simp

lemma phiA_term_nonneg {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (hμ : 0 ≤ μ)
    (r : Fin n → ℝ) (j : Fin n) : 0 ≤ (if bidSum A μ j < r j then r j else 0) := by
  split_ifs with h
  · exact le_trans (bidSum_nonneg A μ hμ j) h.le
  · exact le_rfl

lemma phiA_nonneg {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (hμ : 0 ≤ μ)
    (r : Fin n → ℝ) : 0 ≤ phiA A μ r :=
  Finset.sum_nonneg fun j _ => phiA_term_nonneg A μ hμ r j

/-- On `𝒮` at most one itinerary exceeds its bid price. -/
lemma unique_exceed {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (hμ : 0 ≤ μ)
    (r : Fin n → ℝ) (hr : InS r) (j0 : Fin n) (h0 : bidSum A μ j0 < r j0) :
    ∀ j, j ≠ j0 → ¬ bidSum A μ j < r j := by
  intro j hj hlt
  exact hj (hr.2 j j0 (lt_of_le_of_lt (bidSum_nonneg A μ hμ j) hlt)
    (lt_of_le_of_lt (bidSum_nonneg A μ hμ j0) h0))

lemma sum_single {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (hμ : 0 ≤ μ)
    (r : Fin n → ℝ) (hr : InS r) (j0 : Fin n) (h0 : bidSum A μ j0 < r j0) (f : Fin n → ℝ) :
    (∑ j, if bidSum A μ j < r j then f j else 0) = f j0 := by
  rw [Finset.sum_eq_single j0 (fun j _ hj => by simp [unique_exceed A μ hμ r hr j0 h0 j hj])
    (by simp)]
  simp [h0]

lemma sum_none {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ)
    (r : Fin n → ℝ) (hno : ∀ j, ¬ bidSum A μ j < r j) (f : Fin n → ℝ) :
    (∑ j, if bidSum A μ j < r j then f j else 0) = 0 := by
  simp [hno]

/-- The heuristic never earns more than the alternate system. -/
lemma run_le {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (hμ : 0 ≤ μ) :
    ∀ (l : List (Fin n → ℝ)) (y : Fin m → ℕ),
      heuristicRun A μ l y ≤ (l.map (phiA A μ)).sum := by
  intro l
  induction l with
  | nil => intro y; simp [heuristicRun]
  | cons r rs ih =>
    intro y
    simp only [heuristicRun, List.map_cons, List.sum_cons]
    split_ifs with h
    · have hm : (acceptSet A μ y r).min' h ∈ acceptSet A μ y r := Finset.min'_mem _ h
      generalize (acceptSet A μ y r).min' h = j1 at hm ⊢
      rw [acceptSet, Finset.mem_filter] at hm
      have h1 : r j1 ≤ phiA A μ r := by
        have := Finset.single_le_sum (f := fun j => if bidSum A μ j < r j then r j else 0)
          (fun j _ => phiA_term_nonneg A μ hμ r j) (Finset.mem_univ j1)
        simpa [phiA, hm.2.1] using this
      linarith [ih (y - column A j1)]
    · linarith [ih y, phiA_nonneg A μ hμ r]

lemma heuristicRun_nonneg {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (hμ : 0 ≤ μ) :
    ∀ (l : List (Fin n → ℝ)) (y : Fin m → ℕ), 0 ≤ heuristicRun A μ l y := by
  intro l
  induction l with
  | nil => intro y; simp [heuristicRun]
  | cons r rs ih =>
    intro y
    simp only [heuristicRun]
    split_ifs with h
    · have hm : (acceptSet A μ y r).min' h ∈ acceptSet A μ y r := Finset.min'_mem _ h
      generalize (acceptSet A μ y r).min' h = j at hm ⊢
      rw [acceptSet, Finset.mem_filter] at hm
      have := bidSum_nonneg A μ hμ j
      have := ih (y - column A j)
      linarith [hm.2.1]
    · exact ih y

/-- The pathwise coupling inequality: on request sequences in `𝒮` with revenues `≤ C`, the
alternate system's revenue is at most the heuristic's revenue plus `C` times the total overflow
`∑_i (N^i − y^i)^+`. -/
lemma path_ineq {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (hμ : 0 ≤ μ) (C : ℝ) :
    ∀ (l : List (Fin n → ℝ)), (∀ r ∈ l, InS r ∧ ∀ j, r j ≤ C) → ∀ y : Fin m → ℕ,
      (l.map (phiA A μ)).sum ≤ heuristicRun A μ l y +
        C * ∑ i, max ((l.map (phiN A μ i)).sum - (y i : ℝ)) 0 := by
  intro l
  induction l with
  | nil =>
    intro _ y
    simp only [List.map_nil, List.sum_nil, heuristicRun, zero_sub]
    have : ∀ i, max (-(y i : ℝ)) 0 = 0 := fun i => by
      rw [max_eq_right]; simp
    simp [this]
  | cons r rs ih =>
    intro hgood y
    have hr := hgood r (List.mem_cons_self)
    have ih' := ih (fun r' hr' => hgood r' (List.mem_cons_of_mem _ hr'))
    have hNL0 : ∀ i, 0 ≤ (rs.map (phiN A μ i)).sum := fun i =>
      List.sum_nonneg (fun z hz => by
        obtain ⟨r', _, rfl⟩ := List.mem_map.mp hz
        exact phiN_nonneg A μ i r')
    simp only [heuristicRun, List.map_cons, List.sum_cons]
    split_ifs with hne
    · have hm : (acceptSet A μ y r).min' hne ∈ acceptSet A μ y r := Finset.min'_mem _ hne
      generalize (acceptSet A μ y r).min' hne = j1 at hm ⊢
      rw [acceptSet, Finset.mem_filter] at hm
      have hb1 := hm.2.1
      have hfit := hm.2.2
      have hA : phiA A μ r = r j1 := sum_single A μ hμ r hr.1 j1 hb1 _
      have hN : ∀ i, phiN A μ i r = (A i j1 : ℝ) := fun i => sum_single A μ hμ r hr.1 j1 hb1 _
      have h1 := ih' (y - column A j1)
      have hcol : ∀ i, max ((rs.map (phiN A μ i)).sum - (((y - column A j1) i : ℕ) : ℝ)) 0
          = max ((A i j1 : ℝ) + (rs.map (phiN A μ i)).sum - (y i : ℝ)) 0 := by
        intro i
        simp only [Pi.sub_apply, column]
        rw [Nat.cast_sub (hfit i)]
        ring_nf
      simp only [hcol] at h1
      simp only [hA, hN]
      linarith
    · have hempty : ∀ j, ¬ (bidSum A μ j < r j ∧ Fits A y j) := by
        intro j hj
        exact hne ⟨j, by rw [acceptSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj⟩⟩
      by_cases hex : ∃ j0, bidSum A μ j0 < r j0
      · obtain ⟨j0, hb0⟩ := hex
        have hnf : ¬ Fits A y j0 := fun hf => hempty j0 ⟨hb0, hf⟩
        unfold Fits at hnf
        push Not at hnf
        obtain ⟨i0, hi0⟩ := hnf
        have hA : phiA A μ r = r j0 := sum_single A μ hμ r hr.1 j0 hb0 _
        have hN : ∀ i, phiN A μ i r = (A i j0 : ℝ) := fun i => sum_single A μ hμ r hr.1 j0 hb0 _
        simp only [hA, hN]
        have hC0 : 0 < C := lt_of_lt_of_le (lt_of_le_of_lt (bidSum_nonneg A μ hμ j0) hb0)
          (hr.2 j0)
        have h1 := ih' y
        have hterm : ∀ i, max ((rs.map (phiN A μ i)).sum - (y i : ℝ)) 0
            + (if i = i0 then 1 else 0)
            ≤ max ((A i j0 : ℝ) + (rs.map (phiN A μ i)).sum - (y i : ℝ)) 0 := by
          intro i
          have ha : (0 : ℝ) ≤ A i j0 := Nat.cast_nonneg _
          split_ifs with hi
          · subst hi
            have : (y i : ℝ) + 1 ≤ (A i j0 : ℝ) := by exact_mod_cast hi0
            have := hNL0 i
            rcases le_total ((rs.map (phiN A μ i)).sum - (y i : ℝ)) 0 with h | h
            · rw [max_eq_right h]
              rw [max_eq_left (by linarith)]; linarith
            · rw [max_eq_left h, max_eq_left (by linarith)]; linarith
          · rw [add_zero]
            exact max_le_max (by linarith) le_rfl
        have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq'] at hsum
        simp only [Finset.mem_univ, if_true] at hsum
        have := hr.2 j0
        nlinarith
      · push Not at hex
        have hA : phiA A μ r = 0 := sum_none A μ r (fun j => not_lt.mpr (hex j)) _
        have hN : ∀ i, phiN A μ i r = 0 := fun i => sum_none A μ r (fun j => not_lt.mpr (hex j)) _
        simp only [hA, hN, zero_add]
        exact ih' y

/-- Measurability of the pathwise heuristic revenue. -/
lemma run_meas {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) :
    ∀ (K : ℕ) (y : Fin m → ℕ),
      Measurable (fun ω : Fin K → Fin n → ℝ => heuristicRun A μ (List.ofFn ω) y) := by
  intro K
  induction K with
  | zero =>
    intro y
    simp only [List.ofFn_zero, heuristicRun]
    exact measurable_const
  | succ K ih =>
    intro y
    have htail : Measurable (fun ω : Fin (K + 1) → Fin n → ℝ => fun i : Fin K => ω i.succ) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply _
    let g : Finset (Fin n) → (Fin (K + 1) → Fin n → ℝ) → ℝ := fun T ω =>
      if h : T.Nonempty then
        ω 0 (T.min' h) + heuristicRun A μ (List.ofFn fun i : Fin K => ω i.succ)
          (y - column A (T.min' h))
      else heuristicRun A μ (List.ofFn fun i : Fin K => ω i.succ) y
    have hg : ∀ T, Measurable (g T) := by
      intro T
      by_cases h : T.Nonempty
      · simp only [g, dif_pos h]
        have h1 : Measurable (fun ω : Fin (K + 1) → Fin n → ℝ => heuristicRun A μ
            (List.ofFn fun i : Fin K => ω i.succ) (y - column A (T.min' h))) := (ih _).comp htail
        have h2 : Measurable (fun ω : Fin (K + 1) → Fin n → ℝ => ω 0 (T.min' h)) :=
          (measurable_pi_apply _).comp (measurable_pi_apply 0)
        exact h2.add h1
      · simp only [g, dif_neg h]
        exact (ih _).comp htail
    have hT : ∀ T : Finset (Fin n),
        MeasurableSet {ω : Fin (K + 1) → Fin n → ℝ | acceptSet A μ y (ω 0) = T} := by
      intro T
      have hset : {r : Fin n → ℝ | acceptSet A μ y r = T} =
          {r | ∀ j, (bidSum A μ j < r j ∧ Fits A y j) ↔ j ∈ T} := by
        ext r
        simp only [Set.mem_setOf_eq, Finset.ext_iff, acceptSet, Finset.mem_filter,
          Finset.mem_univ, true_and]
      have hm : MeasurableSet {r : Fin n → ℝ | acceptSet A μ y r = T} := by
        rw [hset]
        refine measurableSet_setOf.mpr (Measurable.forall fun j => Measurable.iff ?_ ?_)
        · exact Measurable.and
            (measurableSet_setOf.mp (measurableSet_lt measurable_const (measurable_pi_apply j)))
            measurable_const
        · exact measurable_const
      have hm0 : Measurable (fun ω : Fin (K + 1) → Fin n → ℝ => ω 0) := measurable_pi_apply 0
      exact hm0 hm
    have hrepr : (fun ω : Fin (K + 1) → Fin n → ℝ => heuristicRun A μ (List.ofFn ω) y) =
        fun ω => ∑ T : Finset (Fin n), if acceptSet A μ y (ω 0) = T then g T ω else 0 := by
      funext ω
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true, g, List.ofFn_succ, heuristicRun]
    rw [hrepr]
    exact Finset.measurable_sum _ fun T _ => Measurable.ite (hT T) (hg T) measurable_const

lemma ite_coord_meas {n : ℕ} (j : Fin n) (b : ℝ) :
    Measurable (fun r : Fin n → ℝ => if b < r j then r j else 0) :=
  Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply j))
    (measurable_pi_apply j) measurable_const

lemma integral_ite_const {n : ℕ} (j : Fin n) (b c : ℝ) (G : Measure (Fin n → ℝ))
    [IsProbabilityMeasure G] :
    ∫ r, (if b < r j then c else 0) ∂G = (G {r | b < r j}).toReal * c := by
  have : (fun r : Fin n → ℝ => if b < r j then c else 0)
      = Set.indicator {r | b < r j} (fun _ => c) := by
    funext r; simp [Set.indicator]
  rw [this, integral_indicator_const _
    (measurableSet_lt measurable_const (measurable_pi_apply j))]
  simp [Measure.real]

/-- One-period expected alternate revenue for one itinerary:
`E[R^j 1{R^j > b}] = E(R^j − b)^+ + P(R^j > b) b`. -/
lemma integral_ite_coord {n : ℕ} (j : Fin n) (b : ℝ) (G : Measure (Fin n → ℝ))
    (hG : IsRequestLaw G) :
    Integrable (fun r : Fin n → ℝ => if b < r j then r j else 0) G ∧
    ∫ r, (if b < r j then r j else 0) ∂G =
      ∫ r, max (r j - b) 0 ∂G + (G {r | b < r j}).toReal * b := by
  haveI := hG.isProbabilityMeasure
  have i1 : Integrable (fun r : Fin n → ℝ => max (r j - b) 0) G :=
    ((hG.integrable_coord j).sub (integrable_const _)).pos_part
  have i2 : Integrable (fun r : Fin n → ℝ => if b < r j then b else 0) G :=
    Integrable.of_bound (Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply j))
      measurable_const measurable_const).aestronglyMeasurable |b|
      (Eventually.of_forall fun r => by split_ifs <;> simp)
  have hpt : (fun r : Fin n → ℝ => if b < r j then r j else 0) =
      fun r => max (r j - b) 0 + (if b < r j then b else 0) := by
    funext r
    split_ifs with h
    · rw [max_eq_left (by linarith)]; ring
    · rw [max_eq_right (by linarith)]; ring
  refine ⟨by rw [hpt]; exact i1.add i2, ?_⟩
  rw [hpt, integral_add i1 i2, integral_ite_const]

end Aux_BPC_cpl

open BidPriceControl.Asymptotic in
theorem solution {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t))
    (C : ℝ) (hC : ∀ t ∈ Finset.Icc 1 k, ∀ᵐ r ∂(F t), ∀ j, r j ≤ C)
    (μstar : Fin m → ℝ) (hmin : IsRelaxedMinimizer A F k x μstar) (θ : ℕ) (hθ : 1 ≤ θ) :
    (∑ t ∈ Finset.Icc 1 (θ * k), ∑ j, ∫ r, max (r j - bidSum A μstar j) 0 ∂(scaledLaw F θ t))
      + (∑ t ∈ Finset.Icc 1 (θ * k), ∑ j, exceedProb A (scaledLaw F θ) μstar t j * bidSum A μstar j)
      - C * ∑ i, ∫ ω, max (seatsCounted A μstar i ω - (θ : ℝ) * (x i : ℝ)) 0
          ∂(pathMeasure (scaledLaw F θ) (θ * k))
      ≤ heuristicValue A (scaledLaw F θ) (θ * k) (θ • x) μstar := by
  have hθ0 : 0 < θ := hθ
  have hμ : 0 ≤ μstar := hmin.1
  set K := θ * k with hK
  have hidx : ∀ s : Fin K, ((K - (s : ℕ)) + θ - 1) / θ ∈ Finset.Icc 1 k := by
    intro s
    have hs := s.isLt
    rw [Finset.mem_Icc]
    constructor
    · rw [Nat.le_div_iff_mul_le hθ0]; omega
    · rw [Nat.div_le_iff_le_mul_add_pred hθ0]
      have : θ * k = k * θ := mul_comm _ _
      omega
  have hRL : ∀ s : Fin K, IsRequestLaw (scaledLaw F θ (K - (s : ℕ))) := fun s => hF _ (hidx s)
  haveI hprob : ∀ s : Fin K, IsProbabilityMeasure (scaledLaw F θ (K - (s : ℕ))) :=
    fun s => (hRL s).isProbabilityMeasure
  set Q : Measure (Fin K → Fin n → ℝ) := Measure.pi fun s : Fin K => scaledLaw F θ (K - (s : ℕ))
    with hQ
  have hPQ : pathMeasure (scaledLaw F θ) K = Q := rfl
  rw [hPQ]
  -- the alternate revenue and seat counts as functions on the path space
  let Alt : (Fin K → Fin n → ℝ) → ℝ := fun ω => ∑ s, Aux_BPC_cpl.phiA A μstar (ω s)
  have hAltL : ∀ ω : Fin K → Fin n → ℝ,
      ((List.ofFn ω).map (Aux_BPC_cpl.phiA A μstar)).sum = Alt ω := by
    intro ω; rw [List.map_ofFn, List.sum_ofFn]; rfl
  have hNL : ∀ i (ω : Fin K → Fin n → ℝ),
      ((List.ofFn ω).map (Aux_BPC_cpl.phiN A μstar i)).sum = seatsCounted A μstar i ω := by
    intro i ω; rw [List.map_ofFn, List.sum_ofFn]; rfl
  -- integrability
  have hphiA_int : ∀ s : Fin K,
      Integrable (Aux_BPC_cpl.phiA A μstar) (scaledLaw F θ (K - (s : ℕ))) := fun s =>
    integrable_finsetSum _ fun j _ =>
      (Aux_BPC_cpl.integral_ite_coord j (bidSum A μstar j) _ (hRL s)).1
  have hAlt_int : Integrable Alt Q :=
    integrable_finsetSum _ fun s _ => integrable_comp_eval (hphiA_int s)
  have hseat_meas : ∀ i, Measurable (seatsCounted A μstar i : (Fin K → Fin n → ℝ) → ℝ) := by
    intro i
    unfold seatsCounted
    refine Finset.measurable_sum _ fun s _ => Finset.measurable_sum _ fun j _ => ?_
    exact Measurable.ite (measurableSet_lt measurable_const
      ((measurable_pi_apply j).comp (measurable_pi_apply s))) measurable_const measurable_const
  have hseat_bd : ∀ i (ω : Fin K → Fin n → ℝ),
      0 ≤ seatsCounted A μstar i ω ∧ seatsCounted A μstar i ω ≤ ∑ s : Fin K, ∑ j, (A i j : ℝ) := by
    intro i ω
    constructor
    · exact Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun j _ => by split_ifs <;> simp
    · exact Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun j _ => by split_ifs <;> simp
  have hover_int : ∀ i, Integrable
      (fun ω => max (seatsCounted A μstar i ω - (θ : ℝ) * (x i : ℝ)) 0) Q := by
    intro i
    refine Integrable.of_bound
      (((hseat_meas i).sub measurable_const).max measurable_const).aestronglyMeasurable
      (∑ s : Fin K, ∑ j, (A i j : ℝ)) (Eventually.of_forall fun ω => ?_)
    have h := hseat_bd i ω
    have hx : (0 : ℝ) ≤ (θ : ℝ) * (x i : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith) (le_trans h.1 h.2)
  have hrun_meas := Aux_BPC_cpl.run_meas A μstar K (θ • x)
  have hrun_int : Integrable (fun ω : Fin K → Fin n → ℝ =>
      heuristicRun A μstar (List.ofFn ω) (θ • x)) Q := by
    refine hAlt_int.mono' hrun_meas.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Aux_BPC_cpl.heuristicRun_nonneg A μstar hμ _ _),
      ← hAltL]
    exact Aux_BPC_cpl.run_le A μstar hμ _ _
  -- the good event: every period's request lies in `𝒮` and is bounded by `C`
  have hgood : ∀ᵐ ω ∂Q, ∀ s : Fin K, InS (ω s) ∧ ∀ j, ω s j ≤ C := by
    rw [ae_all_iff]
    intro s
    have h1 : ∀ᵐ r ∂(scaledLaw F θ (K - (s : ℕ))), InS r ∧ ∀ j, r j ≤ C :=
      (hRL s).ae_inS.and (hC _ (hidx s))
    exact (Measure.tendsto_eval_ae_ae (μ := fun s : Fin K => scaledLaw F θ (K - (s : ℕ)))
      (i := s)).eventually h1
  -- pathwise inequality
  have hpath : ∀ᵐ ω ∂Q, Alt ω - C * ∑ i, max (seatsCounted A μstar i ω - (θ : ℝ) * (x i : ℝ)) 0
      ≤ heuristicRun A μstar (List.ofFn ω) (θ • x) := by
    filter_upwards [hgood] with ω hω
    have hl : ∀ r ∈ List.ofFn ω, InS r ∧ ∀ j, r j ≤ C := by
      intro r hr
      obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hr
      exact hω s
    have := Aux_BPC_cpl.path_ineq A μstar hμ C (List.ofFn ω) hl (θ • x)
    rw [hAltL] at this
    simp only [hNL, Pi.smul_apply, smul_eq_mul, Nat.cast_mul] at this
    linarith
  -- expected alternate revenue
  have hAlt_val : ∫ ω, Alt ω ∂Q =
      (∑ t ∈ Finset.Icc 1 K, ∑ j, ∫ r, max (r j - bidSum A μstar j) 0 ∂(scaledLaw F θ t))
      + (∑ t ∈ Finset.Icc 1 K, ∑ j, exceedProb A (scaledLaw F θ) μstar t j * bidSum A μstar j) := by
    rw [← Finset.sum_add_distrib]
    simp only [Alt]
    rw [integral_finsetSum _ fun s _ => integrable_comp_eval (hphiA_int s)]
    have : ∀ s : Fin K, ∫ ω : Fin K → Fin n → ℝ, Aux_BPC_cpl.phiA A μstar (ω s) ∂Q =
        (fun t => ∑ j, ∫ r, max (r j - bidSum A μstar j) 0 ∂(scaledLaw F θ t) +
          ∑ j, exceedProb A (scaledLaw F θ) μstar t j * bidSum A μstar j) (K - (s : ℕ)) := by
      intro s
      rw [integral_comp_eval (hphiA_int s).aestronglyMeasurable]
      simp only [Aux_BPC_cpl.phiA]
      rw [integral_finsetSum _ fun j _ =>
        (Aux_BPC_cpl.integral_ite_coord j (bidSum A μstar j) _ (hRL s)).1,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [(Aux_BPC_cpl.integral_ite_coord j (bidSum A μstar j) _ (hRL s)).2]
      rfl
    rw [Finset.sum_congr rfl fun s _ => this s]
    exact Aux_BPC_cpl.sum_fin_rev K (fun t => ∑ j, ∫ r, max (r j - bidSum A μstar j) 0
      ∂(scaledLaw F θ t) + ∑ j, exceedProb A (scaledLaw F θ) μstar t j * bidSum A μstar j)
  -- integrate the pathwise inequality
  have hsumint : Integrable (fun ω => ∑ i,
      max (seatsCounted A μstar i ω - (θ : ℝ) * (x i : ℝ)) 0) Q :=
    integrable_finsetSum _ fun i _ => hover_int i
  have hCint : Integrable (fun ω => C * ∑ i,
      max (seatsCounted A μstar i ω - (θ : ℝ) * (x i : ℝ)) 0) Q := hsumint.const_mul C
  have hsubint : Integrable (fun ω => Alt ω - C * ∑ i,
      max (seatsCounted A μstar i ω - (θ : ℝ) * (x i : ℝ)) 0) Q := hAlt_int.sub hCint
  have hint := integral_mono_ae hsubint hrun_int hpath
  rw [integral_sub hAlt_int hCint, integral_const_mul,
    integral_finsetSum _ fun i _ => hover_int i, hAlt_val] at hint
  unfold heuristicValue
  rw [hPQ]
  exact hint
