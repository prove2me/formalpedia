-- Prove2me | solution 1 for ConvStochDual.Existence.pp13_weak_duality_optimality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T03:26:31.772876+00:00
-- url     : https://prove2.me/submissions/ae60050c-6b17-43ca-9191-bd10028099cd

import Mathlib
import Definitions.Def_ConvStochDual_Existence_Setting
import Theorems.Thm_ConvStochDual_Existence_pp13_lemma_22

open MeasureTheory Filter Topology

namespace CSDW

open ConvStochDual.Existence

section Meas

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {n m : ℕ}

theorem epi_closed (g : (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (hg : LowerSemicontinuous (fun q : (Fin n → ℝ) × (Fin m → ℝ) => g q.1 q.2)) :
    IsClosed {q : (Fin n → ℝ) × (Fin m → ℝ) × ℝ | g q.1 q.2.1 ≤ (q.2.2 : EReal)} := by
  have h := hg.isClosed_epigraph
  have hc : Continuous (fun q : (Fin n → ℝ) × (Fin m → ℝ) × ℝ =>
      (((q.1, q.2.1) : (Fin n → ℝ) × (Fin m → ℝ)), ((q.2.2 : ℝ) : EReal))) := by
    refine Continuous.prodMk (by fun_prop) ?_
    exact continuous_coe_real_ereal.comp (by fun_prop)
  exact h.preimage hc

/-- Measurability of `ω ↦ f(a ω, b ω, ω)` for a normal integrand. -/
theorem meas_comp (f : Ω → (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (hf : IsNormalIntegrand f) (a : Ω → Fin n → ℝ) (b : Ω → Fin m → ℝ)
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun ω => f ω (a ω) (b ω)) := by
  obtain ⟨_, hlsc, _, hmeas⟩ := hf
  set d : ℕ → (Fin n → ℝ) × (Fin m → ℝ) := TopologicalSpace.denseSeq _ with hd
  have hdense : DenseRange d := TopologicalSpace.denseRange_denseSeq _
  have hab : Measurable (fun ω => (a ω, b ω)) := ha.prodMk hb
  -- real sublevel sets
  have hreal : ∀ α : ℝ, MeasurableSet {ω | f ω (a ω) (b ω) ≤ (α : EReal)} := by
    intro α
    set E : Ω → Set ((Fin n → ℝ) × (Fin m → ℝ) × ℝ) :=
      fun ω => {q | f ω q.1 q.2.1 ≤ (q.2.2 : EReal)} with hE
    have heq : {ω | f ω (a ω) (b ω) ≤ (α : EReal)} =
        ⋂ k : ℕ, ⋃ j : ℕ, ({ω | dist (a ω, b ω) (d j) < 1 / ((k : ℝ) + 1)} ∩
          {ω | ∃ q ∈ Metric.ball ((d j).1, ((d j).2, α)) (2 / ((k : ℝ) + 1)),
            f ω q.1 q.2.1 ≤ (q.2.2 : EReal)}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h k
        have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        obtain ⟨j, hj⟩ := (Metric.denseRange_iff.1 hdense) (a ω, b ω) _ hk
        refine ⟨j, hj, (a ω, (b ω, α)), ?_, h⟩
        rw [Metric.mem_ball]
        have h1 : dist ((a ω, (b ω, α)) : (Fin n → ℝ) × (Fin m → ℝ) × ℝ)
            ((d j).1, ((d j).2, α)) ≤ dist (a ω, b ω) (d j) := by
          simp only [Prod.dist_eq, dist_self]
          exact max_le (le_max_left _ _) (max_le (le_max_right _ _) (le_max_of_le_left dist_nonneg))
        have h2 : 1 / ((k : ℝ) + 1) ≤ 2 / ((k : ℝ) + 1) := by
          apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
        linarith
      · intro h
        have hcl := epi_closed (f ω) (hlsc ω)
        have hmem : ((a ω, (b ω, α)) : (Fin n → ℝ) × (Fin m → ℝ) × ℝ) ∈
            {q : (Fin n → ℝ) × (Fin m → ℝ) × ℝ | f ω q.1 q.2.1 ≤ (q.2.2 : EReal)} := by
          rw [← hcl.closure_eq, Metric.mem_closure_iff]
          intro ε hε
          obtain ⟨k, hk⟩ := exists_nat_gt (3 / ε)
          obtain ⟨j, hj, q, hq, hqE⟩ := h k
          refine ⟨q, hqE, ?_⟩
          rw [Metric.mem_ball] at hq
          have h1 : dist ((a ω, (b ω, α)) : (Fin n → ℝ) × (Fin m → ℝ) × ℝ)
              ((d j).1, ((d j).2, α)) ≤ dist (a ω, b ω) (d j) := by
            simp only [Prod.dist_eq, dist_self]
            exact max_le (le_max_left _ _) (max_le (le_max_right _ _) (le_max_of_le_left dist_nonneg))
          have h3 := dist_triangle ((a ω, (b ω, α)) : (Fin n → ℝ) × (Fin m → ℝ) × ℝ)
            ((d j).1, ((d j).2, α)) q
          rw [dist_comm ((d j).1, ((d j).2, α)) q] at h3
          have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
          have : 3 / ((k : ℝ) + 1) < ε := by
            rw [div_lt_iff₀ hk1]
            rw [div_lt_iff₀ hε] at hk
            nlinarith
          have e3 : 1 / ((k : ℝ) + 1) + 2 / ((k : ℝ) + 1) = 3 / ((k : ℝ) + 1) := by ring
          linarith
        exact hmem
    rw [heq]
    refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun j => ?_
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_lt (hab.dist measurable_const) measurable_const
    · exact hmeas _ Metric.isOpen_ball
  refine measurable_of_Iic fun c => ?_
  induction c using EReal.rec with
  | bot =>
    have : (fun ω => f ω (a ω) (b ω)) ⁻¹' Set.Iic ⊥ =
        ⋂ k : ℕ, {ω | f ω (a ω) (b ω) ≤ ((-(k : ℝ) : ℝ) : EReal)} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iic, le_bot_iff, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h k; rw [h]; exact bot_le
      · intro h
        by_contra hne
        induction hω : f ω (a ω) (b ω) using EReal.rec with
        | bot => exact hne hω
        | top => have := h 0; rw [hω] at this; simp at this
        | coe r =>
          obtain ⟨k, hk⟩ := exists_nat_gt (-r)
          have := h k; rw [hω, EReal.coe_le_coe_iff] at this; linarith
    rw [this]; exact MeasurableSet.iInter fun k => hreal _
  | top => simp
  | coe r => exact hreal r

theorem lt_iSup_sub_iff {A B : Type*} (g : A → B → EReal) (r : A → B → ℝ) (β : ℝ) :
    (β : EReal) < ⨆ x, ⨆ u, ((r x u : ℝ) : EReal) - g x u ↔
      ∃ x u, ∃ t : ℝ, g x u ≤ (t : EReal) ∧ β < r x u - t := by
  simp only [lt_iSup_iff]
  constructor
  · rintro ⟨x, u, h⟩
    induction hg : g x u using EReal.rec with
    | bot => exact ⟨x, u, r x u - β - 1, by rw [hg]; exact bot_le, by linarith⟩
    | top => rw [hg, EReal.sub_top] at h; exact absurd h (not_lt_bot)
    | coe v =>
      rw [hg, ← EReal.coe_sub, EReal.coe_lt_coe_iff] at h
      exact ⟨x, u, v, hg.le, h⟩
  · rintro ⟨x, u, t, hle, hlt⟩
    refine ⟨x, u, lt_of_lt_of_le ?_ (EReal.sub_le_sub le_rfl hle)⟩
    rw [← EReal.coe_sub]; exact_mod_cast hlt

theorem abs_dot_sub_le {k : ℕ} (a b b' : Fin k → ℝ) :
    |dot a b - dot a b'| ≤ (k : ℝ) * ‖a‖ * ‖b - b'‖ := by
  unfold dot
  rw [← Finset.sum_sub_distrib]
  calc |∑ i, (a i * b i - a i * b' i)| ≤ ∑ i, |a i * b i - a i * b' i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin k, ‖a‖ * ‖b - b'‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← mul_sub, abs_mul]
        have h1 : |a i| ≤ ‖a‖ := by
          have := norm_le_pi_norm a i; rwa [Real.norm_eq_abs] at this
        have h2 : |b i - b' i| ≤ ‖b - b'‖ := by
          have := norm_le_pi_norm (b - b') i; rwa [Real.norm_eq_abs, Pi.sub_apply] at this
        exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    _ = (k : ℝ) * ‖a‖ * ‖b - b'‖ := by simp [mul_assoc]

/-- The linear form `q ↦ x·p + u·y - t` used for the conjugate. -/
noncomputable def phiLin (q : (Fin n → ℝ) × (Fin m → ℝ) × ℝ) (z : (Fin n → ℝ) × (Fin m → ℝ)) : ℝ :=
  dot q.1 z.1 + dot q.2.1 z.2 - q.2.2

theorem phiLin_lip (q : (Fin n → ℝ) × (Fin m → ℝ) × ℝ) (z e : (Fin n → ℝ) × (Fin m → ℝ)) :
    |phiLin q z - phiLin q e| ≤ ((n : ℝ) + m) * ‖q‖ * dist z e := by
  unfold phiLin
  have h1 := abs_dot_sub_le q.1 z.1 e.1
  have h2 := abs_dot_sub_le q.2.1 z.2 e.2
  have hq1 : ‖q.1‖ ≤ ‖q‖ := norm_fst_le q
  have hq2 : ‖q.2.1‖ ≤ ‖q‖ := (norm_fst_le q.2).trans (norm_snd_le q)
  have hz1 : ‖z.1 - e.1‖ ≤ dist z e := by
    rw [Prod.dist_eq, dist_eq_norm]; exact le_max_left _ _
  have hz2 : ‖z.2 - e.2‖ ≤ dist z e := by
    rw [Prod.dist_eq, dist_eq_norm (z.2)]; exact le_max_right _ _
  have e1 : dot q.1 z.1 + dot q.2.1 z.2 - q.2.2 - (dot q.1 e.1 + dot q.2.1 e.2 - q.2.2) =
      (dot q.1 z.1 - dot q.1 e.1) + (dot q.2.1 z.2 - dot q.2.1 e.2) := by ring
  rw [e1]
  have hn : (0 : ℝ) ≤ n := by positivity
  have hm : (0 : ℝ) ≤ m := by positivity
  have hd : 0 ≤ dist z e := dist_nonneg
  calc |(dot q.1 z.1 - dot q.1 e.1) + (dot q.2.1 z.2 - dot q.2.1 e.2)|
      ≤ |dot q.1 z.1 - dot q.1 e.1| + |dot q.2.1 z.2 - dot q.2.1 e.2| := abs_add_le _ _
    _ ≤ (n : ℝ) * ‖q.1‖ * ‖z.1 - e.1‖ + (m : ℝ) * ‖q.2.1‖ * ‖z.2 - e.2‖ := add_le_add h1 h2
    _ ≤ (n : ℝ) * ‖q‖ * dist z e + (m : ℝ) * ‖q‖ * dist z e := by
        gcongr
    _ = ((n : ℝ) + m) * ‖q‖ * dist z e := by ring

theorem continuous_phiLin (z : (Fin n → ℝ) × (Fin m → ℝ)) :
    Continuous (fun q : (Fin n → ℝ) × (Fin m → ℝ) × ℝ => phiLin q z) := by
  unfold phiLin dot
  fun_prop

/-- Measurability of `ω ↦ f^*(p ω, y ω, ω)` for a normal integrand. -/
theorem meas_conj (f : Ω → (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (hf : IsNormalIntegrand f) (p : Ω → Fin n → ℝ) (y : Ω → Fin m → ℝ)
    (hp : Measurable p) (hy : Measurable y) :
    Measurable (fun ω => ⨆ x : Fin n → ℝ, ⨆ u : Fin m → ℝ,
      ((dot x (p ω) + dot u (y ω) : ℝ) : EReal) - f ω x u) := by
  obtain ⟨_, _, _, hmeas⟩ := hf
  set e : ℕ → (Fin n → ℝ) × (Fin m → ℝ) := TopologicalSpace.denseSeq _ with he
  have hdense : DenseRange e := TopologicalSpace.denseRange_denseSeq _
  have hz : Measurable (fun ω => (p ω, y ω)) := hp.prodMk hy
  set L : ℝ := (n : ℝ) + m with hL
  have hL0 : 0 ≤ L := by positivity
  have hreal : ∀ β : ℝ, MeasurableSet {ω | (β : EReal) < ⨆ x : Fin n → ℝ, ⨆ u : Fin m → ℝ,
      ((dot x (p ω) + dot u (y ω) : ℝ) : EReal) - f ω x u} := by
    intro β
    have heq : {ω | (β : EReal) < ⨆ x : Fin n → ℝ, ⨆ u : Fin m → ℝ,
        ((dot x (p ω) + dot u (y ω) : ℝ) : EReal) - f ω x u} =
        ⋃ R : ℕ, ⋃ j : ℕ, ⋃ k : ℕ, ({ω | dist (p ω, y ω) (e j) < 1 / ((k : ℝ) + 1)} ∩
          {ω | ∃ q ∈ {q : (Fin n → ℝ) × (Fin m → ℝ) × ℝ | ‖q‖ < R ∧
              β + 2 * L * R / ((k : ℝ) + 1) < phiLin q (e j)},
            f ω q.1 q.2.1 ≤ (q.2.2 : EReal)}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      rw [lt_iSup_sub_iff (f ω) (fun x u => dot x (p ω) + dot u (y ω)) β]
      constructor
      · rintro ⟨x, u, t, hle, hlt⟩
        set q : (Fin n → ℝ) × (Fin m → ℝ) × ℝ := (x, (u, t)) with hq
        have hφ : phiLin q (p ω, y ω) = dot x (p ω) + dot u (y ω) - t := rfl
        obtain ⟨R, hR⟩ := exists_nat_gt ‖q‖
        set δ := phiLin q (p ω, y ω) - β with hδ
        have hδ0 : 0 < δ := by rw [hδ, hφ]; linarith
        obtain ⟨k, hk⟩ := exists_nat_gt (3 * L * R / δ)
        have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        obtain ⟨j, hj⟩ := (Metric.denseRange_iff.1 hdense) (p ω, y ω) (1 / ((k : ℝ) + 1))
          (by positivity)
        refine ⟨R, j, k, hj, q, ⟨hR, ?_⟩, hle⟩
        have hlip := phiLin_lip q (p ω, y ω) (e j)
        have hRq : L * ‖q‖ * dist (p ω, y ω) (e j) ≤ L * R * (1 / ((k : ℝ) + 1)) := by
          have := mul_le_mul_of_nonneg_left hR.le hL0
          exact mul_le_mul this hj.le dist_nonneg (by positivity)
        have h3 : 3 * L * R / ((k : ℝ) + 1) < δ := by
          rw [div_lt_iff₀ hk1]
          rw [div_lt_iff₀ hδ0] at hk
          nlinarith
        have e1 : L * R * (1 / ((k : ℝ) + 1)) = L * R / ((k : ℝ) + 1) := by ring
        have e2 : 3 * L * R / ((k : ℝ) + 1) = 2 * L * R / ((k : ℝ) + 1) +
            L * R / ((k : ℝ) + 1) := by ring
        have := (abs_le.1 hlip).2
        linarith [(abs_le.1 hlip).1]
      · rintro ⟨R, j, k, hj, q, ⟨hR, hφ⟩, hle⟩
        refine ⟨q.1, q.2.1, q.2.2, hle, ?_⟩
        have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have hlip := phiLin_lip q (p ω, y ω) (e j)
        have hRq : L * ‖q‖ * dist (p ω, y ω) (e j) ≤ L * R * (1 / ((k : ℝ) + 1)) := by
          have := mul_le_mul_of_nonneg_left hR.le hL0
          exact mul_le_mul this hj.le dist_nonneg (by positivity)
        have e1 : L * R * (1 / ((k : ℝ) + 1)) = L * R / ((k : ℝ) + 1) := by ring
        have e2 : 2 * L * R / ((k : ℝ) + 1) = L * R / ((k : ℝ) + 1) +
            L * R / ((k : ℝ) + 1) := by ring
        have hpos : 0 ≤ L * R / ((k : ℝ) + 1) := by positivity
        have hφz : phiLin q (p ω, y ω) = dot q.1 (p ω) + dot q.2.1 (y ω) - q.2.2 := rfl
        linarith [(abs_le.1 hlip).1]
    rw [heq]
    refine MeasurableSet.iUnion fun R => MeasurableSet.iUnion fun j =>
      MeasurableSet.iUnion fun k => MeasurableSet.inter ?_ ?_
    · exact measurableSet_lt (hz.dist measurable_const) measurable_const
    · refine hmeas _ (IsOpen.inter ?_ ?_)
      · exact isOpen_lt continuous_norm continuous_const
      · exact isOpen_lt continuous_const (continuous_phiLin _)
  refine measurable_of_Ioi fun c => ?_
  induction c using EReal.rec with
  | bot =>
    have : (fun ω => ⨆ x : Fin n → ℝ, ⨆ u : Fin m → ℝ,
        ((dot x (p ω) + dot u (y ω) : ℝ) : EReal) - f ω x u) ⁻¹' Set.Ioi ⊥ =
        ⋃ k : ℕ, {ω | ((-(k : ℝ) : ℝ) : EReal) < ⨆ x : Fin n → ℝ, ⨆ u : Fin m → ℝ,
          ((dot x (p ω) + dot u (y ω) : ℝ) : EReal) - f ω x u} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro h
        induction hF : (⨆ x : Fin n → ℝ, ⨆ u : Fin m → ℝ,
            ((dot x (p ω) + dot u (y ω) : ℝ) : EReal) - f ω x u) using EReal.rec with
        | bot => rw [hF] at h; exact absurd h (lt_irrefl _)
        | top => exact ⟨0, by simp⟩
        | coe r =>
          obtain ⟨k, hk⟩ := exists_nat_gt (-r)
          exact ⟨k, by rw [EReal.coe_lt_coe_iff]; linarith⟩
      · rintro ⟨k, hk⟩; exact lt_of_le_of_lt bot_le hk
    rw [this]; exact MeasurableSet.iUnion fun k => hreal _
  | top => simp
  | coe r => exact hreal r

end Meas

section Expect

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem toENNReal_coe_real (r : ℝ) : ((r : EReal)).toENNReal = ENNReal.ofReal r := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top r), EReal.toReal_coe]

theorem integrable_of_lintegral (F : Ω → ℝ) (hF : AEStronglyMeasurable F P)
    (h1 : ∫⁻ ω, ENNReal.ofReal (F ω) ∂P ≠ ⊤) (h2 : ∫⁻ ω, ENNReal.ofReal (-F ω) ∂P ≠ ⊤) :
    Integrable F P := by
  refine ⟨hF, ?_⟩
  unfold HasFiniteIntegral
  have e : (fun ω => ‖F ω‖ₑ) = fun ω => ENNReal.ofReal (F ω) + ENNReal.ofReal (-F ω) := by
    funext ω
    rw [Real.enorm_eq_ofReal_abs]
    rcases le_total (F ω) 0 with h | h
    · rw [abs_of_nonpos h, ENNReal.ofReal_eq_zero.2 h, zero_add]
    · rw [abs_of_nonneg h, ENNReal.ofReal_eq_zero.2 (by linarith : -F ω ≤ 0), add_zero]
  rw [e, lintegral_add_left' hF.aemeasurable.ennreal_ofReal]
  exact ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 h1, lt_top_iff_ne_top.2 h2⟩

theorem expect_eq_of_ae (h : Ω → EReal) (H : Ω → ℝ) (hH : Integrable H P)
    (hae : ∀ᵐ ω ∂P, h ω = (H ω : EReal)) :
    DupacovaWets.Consistency.expect P h = ((∫ ω, H ω ∂P : ℝ) : EReal) := by
  unfold DupacovaWets.Consistency.expect
  have l1 : ∫⁻ ω, (h ω).toENNReal ∂P = ∫⁻ ω, ENNReal.ofReal (H ω) ∂P := by
    refine lintegral_congr_ae (hae.mono fun ω hω => ?_)
    show (h ω).toENNReal = _
    rw [hω, toENNReal_coe_real]
  have l2 : ∫⁻ ω, (-h ω).toENNReal ∂P = ∫⁻ ω, ENNReal.ofReal (-H ω) ∂P := by
    refine lintegral_congr_ae (hae.mono fun ω hω => ?_)
    show (-h ω).toENNReal = _
    rw [hω, ← EReal.coe_neg, toENNReal_coe_real]
  have f1 : ∫⁻ ω, ENNReal.ofReal (H ω) ∂P ≠ ⊤ := hH.lintegral_lt_top.ne
  have f2 : ∫⁻ ω, ENNReal.ofReal (-H ω) ∂P ≠ ⊤ := hH.neg.lintegral_lt_top.ne
  rw [l1, l2, if_neg f1, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hH,
    ← EReal.coe_ennreal_toReal f1, ← EReal.coe_ennreal_toReal f2, EReal.coe_sub]

theorem expect_top_of (h : Ω → EReal) (hh : ∫⁻ ω, (h ω).toENNReal ∂P = ⊤) :
    DupacovaWets.Consistency.expect P h = ⊤ := by
  unfold DupacovaWets.Consistency.expect; rw [if_pos hh]

theorem lint_pos_ne_top (h : Ω → EReal) (hh : DupacovaWets.Consistency.expect P h ≠ ⊤) :
    ∫⁻ ω, (h ω).toENNReal ∂P ≠ ⊤ := fun h' => hh (expect_top_of h h')

theorem lint_neg_ne_top (h : Ω → EReal) (hh : DupacovaWets.Consistency.expect P h ≠ ⊥)
    (hh' : DupacovaWets.Consistency.expect P h ≠ ⊤) :
    ∫⁻ ω, (-h ω).toENNReal ∂P ≠ ⊤ := by
  intro h'
  apply hh
  have h1 := lint_pos_ne_top h hh'
  unfold DupacovaWets.Consistency.expect
  rw [if_neg h1, h', EReal.coe_ennreal_top, EReal.sub_top]

theorem ae_ne_top (h : Ω → EReal) (hm : Measurable h) (hh : ∫⁻ ω, (h ω).toENNReal ∂P ≠ ⊤) :
    ∀ᵐ ω ∂P, h ω ≠ ⊤ := by
  have := ae_lt_top (hm.ereal_toENNReal) hh
  filter_upwards [this] with ω hω
  intro htop
  rw [htop] at hω
  simp at hω

theorem ae_ne_bot (h : Ω → EReal) (hm : Measurable h) (hh : ∫⁻ ω, (-h ω).toENNReal ∂P ≠ ⊤) :
    ∀ᵐ ω ∂P, h ω ≠ ⊥ := by
  have := ae_lt_top (hm.neg.ereal_toENNReal) hh
  filter_upwards [this] with ω hω
  intro hbot
  simp only [Pi.neg_apply] at hω
  rw [hbot] at hω
  simp at hω

end Expect

section Perp

variable {Ω X U : Type*} [MeasurableSpace Ω]
  [AddCommGroup X] [Module ℝ X] [UniformSpace X]
  [IsUniformAddGroup X] [ContinuousSMul ℝ X]
  [AddCommGroup U] [Module ℝ U] [UniformSpace U]
  [IsUniformAddGroup U] [ContinuousSMul ℝ U]
  {T n m : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {τ : Fin n → Fin (T + 1)}
  {𝔽 : Fin (T + 1) → MeasurableSpace Ω}
  {ιX : X →ₗ[ℝ] RV Ω P n} {ιU : U →ₗ[ℝ] RV Ω P m}
  {V : Submodule ℝ (RV Ω P n)} {Y : Submodule ℝ (RV Ω P m)}

theorem dot_single_left {k : ℕ} (i : Fin k) (c : ℝ) (b : Fin k → ℝ) :
    dot (fun j => if j = i then c else 0) b = c * b i := by
  unfold dot
  simp [ite_mul]

theorem perp_props (s : Setting P τ 𝔽 ιX ιU V Y) (hS : Standing s)
    (p : V) (hp : p ∈ XaPerp s) (i : Fin n) :
    Integrable (fun ω => (p : RV Ω P n) ω i) P ∧
      P[fun ω => (p : RV Ω P n) ω i | 𝔽 (τ i)] =ᵐ[P] 0 := by
  -- the test strategies
  have hz : ∀ A : Set Ω, MeasurableSet[𝔽 (τ i)] A →
      ∃ z : X, z ∈ Xa s ∧ ∀ᵐ ω ∂P, ιX z ω = fun j => if j = i then A.indicator (fun _ => (1:ℝ)) ω else 0 := by
    intro A hA
    have hAm : MeasurableSet A := hS.filtration_le _ _ hA
    set wf : Ω → Fin n → ℝ := fun ω j => if j = i then A.indicator (fun _ => (1:ℝ)) ω else 0
      with hwf
    have hwm : Measurable wf := by
      refine measurable_pi_lambda _ fun j => ?_
      by_cases hji : j = i
      · simp only [hwf, hji, if_true]
        exact measurable_const.indicator hAm
      · simp only [hwf, hji, if_false]
        exact measurable_const
    set w : RV Ω P n := AEEqFun.mk wf hwm.aestronglyMeasurable with hw
    have hwb : IsEssentiallyBounded P w := by
      refine ⟨1, zero_le_one, (AEEqFun.coeFn_mk wf hwm.aestronglyMeasurable).mono fun ω hω j => ?_⟩
      rw [hω]
      simp only [hwf]
      split_ifs
      · by_cases hωA : ω ∈ A
        · simp [hωA]
        · simp [hωA]
      · simp
    obtain ⟨z, hzae⟩ := hS.decomposableX 0 w hwb ∅ MeasurableSet.empty
    refine ⟨z, ?_, ?_⟩
    · intro j
      refine ⟨fun ω => if j = i then A.indicator (fun _ => (1:ℝ)) ω else 0, ?_, ?_⟩
      · by_cases hji : j = i
        · subst hji
          simp only [if_true]
          exact stronglyMeasurable_const.indicator hA
        · simp only [hji, if_false]
          exact stronglyMeasurable_const
      · filter_upwards [hzae, AEEqFun.coeFn_mk wf hwm.aestronglyMeasurable] with ω h1 h2
        simp only [Set.mem_empty_iff_false, if_false] at h1
        rw [h1, hw, h2]
    · filter_upwards [hzae, AEEqFun.coeFn_mk wf hwm.aestronglyMeasurable] with ω h1 h2
      simp only [Set.mem_empty_iff_false, if_false] at h1
      rw [h1, hw, h2]
  have hint_set : ∀ A : Set Ω, MeasurableSet[𝔽 (τ i)] A →
      Integrable (fun ω => A.indicator (fun _ => (1:ℝ)) ω * (p : RV Ω P n) ω i) P ∧
      ∫ ω, A.indicator (fun _ => (1:ℝ)) ω * (p : RV Ω P n) ω i ∂P = 0 := by
    intro A hA
    obtain ⟨z, hzXa, hzae⟩ := hz A hA
    have hae : (fun ω => dot (ιX z ω) ((p : RV Ω P n) ω)) =ᵐ[P]
        fun ω => A.indicator (fun _ => (1:ℝ)) ω * (p : RV Ω P n) ω i := by
      filter_upwards [hzae] with ω hω
      rw [hω, dot_single_left]
    refine ⟨(integrable_congr hae).1 (hS.pair_integrableX z p), ?_⟩
    have := hp z hzXa
    unfold pair at this
    rw [← integral_congr_ae hae]
    exact this
  have hint : Integrable (fun ω => (p : RV Ω P n) ω i) P := by
    have := (hint_set Set.univ MeasurableSet.univ).1
    simpa using this
  refine ⟨hint, ?_⟩
  have hle := hS.filtration_le (τ i)
  have := ae_eq_condExp_of_forall_setIntegral_eq (μ := P) (m := 𝔽 (τ i)) hle hint
    (g := fun _ => (0:ℝ)) (fun _ _ _ => integrableOn_zero) (fun A hA _ => by
      rw [integral_zero, ← integral_indicator (hle _ hA)]
      have h2 := (hint_set A hA).2
      have e : A.indicator (fun ω => (p : RV Ω P n) ω i) =
          fun ω => A.indicator (fun _ => (1:ℝ)) ω * (p : RV Ω P n) ω i := by
        funext ω; by_cases hω : ω ∈ A <;> simp [hω]
      rw [e, h2]) stronglyMeasurable_const.aestronglyMeasurable
  exact this.symm

end Perp

section Aux

theorem ereal_aux (r B : ℝ) (F : EReal) (h : (r : EReal) - F ≤ (B : EReal)) :
    ((r - B : ℝ) : EReal) ≤ F := by
  induction F using EReal.rec with
  | bot => rw [EReal.coe_sub_bot] at h; exact absurd h (by simp)
  | top => exact le_top
  | coe v =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h
    rw [EReal.coe_le_coe_iff]; linarith

theorem dot_sub_left {k : ℕ} (a a' b : Fin k → ℝ) : dot (a - a') b = dot a b - dot a' b := by
  unfold dot; simp [sub_mul, Finset.sum_sub_distrib]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem lint_bound3 (F G1 G2 G3 : Ω → ℝ) (h1 : AEMeasurable G1 P) (h2 : AEMeasurable G2 P)
    (hle : ∀ᵐ ω ∂P, F ω ≤ G1 ω + G2 ω + G3 ω) :
    ∫⁻ ω, ENNReal.ofReal (F ω) ∂P ≤ ∫⁻ ω, ENNReal.ofReal (G1 ω) ∂P +
      ∫⁻ ω, ENNReal.ofReal (G2 ω) ∂P + ∫⁻ ω, ENNReal.ofReal (G3 ω) ∂P := by
  calc ∫⁻ ω, ENNReal.ofReal (F ω) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (G1 ω) + ENNReal.ofReal (G2 ω)) + ENNReal.ofReal (G3 ω) ∂P := by
        refine lintegral_mono_ae (hle.mono fun ω hω => ?_)
        calc ENNReal.ofReal (F ω) ≤ ENNReal.ofReal (G1 ω + G2 ω + G3 ω) :=
              ENNReal.ofReal_le_ofReal hω
          _ ≤ ENNReal.ofReal (G1 ω + G2 ω) + ENNReal.ofReal (G3 ω) := ENNReal.ofReal_add_le
          _ ≤ (ENNReal.ofReal (G1 ω) + ENNReal.ofReal (G2 ω)) + ENNReal.ofReal (G3 ω) := by
              gcongr; exact ENNReal.ofReal_add_le
    _ = _ := by
        rw [lintegral_add_left' (f := fun ω => ENNReal.ofReal (G1 ω) + ENNReal.ofReal (G2 ω))
          (by exact h1.ennreal_ofReal.add h2.ennreal_ofReal),
          lintegral_add_left' h1.ennreal_ofReal]

end Aux

section Main

variable {Ω X U : Type*} [MeasurableSpace Ω]
  [AddCommGroup X] [Module ℝ X] [UniformSpace X]
  [IsUniformAddGroup X] [ContinuousSMul ℝ X]
  [AddCommGroup U] [Module ℝ U] [UniformSpace U]
  [IsUniformAddGroup U] [ContinuousSMul ℝ U]
  {T n m : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {τ : Fin n → Fin (T + 1)}
  {𝔽 : Fin (T + 1) → MeasurableSpace Ω}
  {ιX : X →ₗ[ℝ] RV Ω P n} {ιU : U →ₗ[ℝ] RV Ω P m}
  {V : Submodule ℝ (RV Ω P n)} {Y : Submodule ℝ (RV Ω P m)}

theorem main (s : Setting P τ 𝔽 ιX ιU V Y)
    (hS : Standing s) (x : RV Ω P n) (hx : Adapted τ 𝔽 P x)
    (p : V) (hp : p ∈ XaPerp s) (y : Y) :
    dualObj s p y ≤ Ef s x (ιU s.ubar) ∧
    (Ef s x (ιU s.ubar) ≠ ⊤ → Ef s x (ιU s.ubar) ≠ ⊥ →
      dualObj s p y = Ef s x (ιU s.ubar) →
      ∀ᵐ ω ∂P, IsSubgradAt (s.f ω) (x ω) (ιU s.ubar ω) (p.1 ω) (y.1 ω)) ∧
    (Ef s x (ιU s.ubar) < ⊤ →
      (∀ᵐ ω ∂P, IsSubgradAt (s.f ω) (x ω) (ιU s.ubar ω) (p.1 ω) (y.1 ω)) →
      ∀ x' : RV Ω P n, Adapted τ 𝔽 P x' → Ef s x (ιU s.ubar) ≤ Ef s x' (ιU s.ubar)) := by
  set ub : RV Ω P m := ιU s.ubar with hub
  set a : Ω → EReal := fun ω => s.f ω (x ω) (ub ω) with ha
  set b : Ω → EReal := fun ω => fstar s ω (p.1 ω) (y.1 ω) with hb
  set c : Ω → ℝ := fun ω => dot (x ω) (p.1 ω) with hc
  set d : Ω → ℝ := fun ω => dot (ub ω) (y.1 ω) with hd
  have hxm : Measurable (fun ω => x ω) := x.stronglyMeasurable.measurable
  have hpm : Measurable (fun ω => p.1 ω) := p.1.stronglyMeasurable.measurable
  have hym : Measurable (fun ω => y.1 ω) := y.1.stronglyMeasurable.measurable
  have hubm : Measurable (fun ω => ub ω) := ub.stronglyMeasurable.measurable
  have ham : Measurable a := meas_comp s.f hS.normal _ _ hxm hubm
  have hbm : Measurable b := meas_conj s.f hS.normal _ _ hpm hym
  have hdi : Integrable d P := hS.pair_integrableU s.ubar y
  have hcm : Measurable c := by
    simp only [hc, dot]
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp hxm).mul ((measurable_pi_apply i).comp hpm)
  have hEf : Ef s x ub = DupacovaWets.Consistency.expect P a := rfl
  have hdual : dualObj s p y = ((∫ ω, d ω ∂P : ℝ) : EReal) -
      DupacovaWets.Consistency.expect P b := rfl
  have fenchel : ∀ ω, ∀ (x' : Fin n → ℝ) (u' : Fin m → ℝ),
      ((dot x' (p.1 ω) + dot u' (y.1 ω) : ℝ) : EReal) - s.f ω x' u' ≤ b ω := by
    intro ω x' u'
    exact le_iSup₂ (f := fun (x' : Fin n → ℝ) (u' : Fin m → ℝ) =>
      ((dot x' (p.1 ω) + dot u' (y.1 ω) : ℝ) : EReal) - s.f ω x' u') x' u'
  have hperpP := perp_props s hS p hp
  have L22 : ∀ z : Ω → Fin n → ℝ,
      (∀ i, ∃ g : Ω → ℝ, StronglyMeasurable[𝔽 (τ i)] g ∧ (fun ω => z ω i) =ᵐ[P] g) →
      ∫⁻ ω, ENNReal.ofReal (dot (z ω) (p.1 ω)) ∂P ≠ ⊤ →
      Integrable (fun ω => dot (z ω) (p.1 ω)) P ∧ ∫ ω, dot (z ω) (p.1 ω) ∂P = 0 := by
    intro z hz h
    exact pp13_lemma_22 τ 𝔽 hS.filtration_le hS.filtration_mono z (fun ω => p.1 ω) hz
      (fun i => (hperpP i).1) (fun i => (hperpP i).2) h
  -- real representative of an a.e. finite EReal function
  have rep : ∀ h : Ω → EReal, Measurable h → (∀ᵐ ω ∂P, h ω ≠ ⊤) → (∀ᵐ ω ∂P, h ω ≠ ⊥) →
      (∀ᵐ ω ∂P, h ω = (((h ω).toReal : ℝ) : EReal)) ∧
      ∫⁻ ω, ENNReal.ofReal ((h ω).toReal) ∂P = ∫⁻ ω, (h ω).toENNReal ∂P ∧
      ∫⁻ ω, ENNReal.ofReal (-(h ω).toReal) ∂P = ∫⁻ ω, (-h ω).toENNReal ∂P := by
    intro h _ h1 h2
    have e : ∀ᵐ ω ∂P, h ω = (((h ω).toReal : ℝ) : EReal) := by
      filter_upwards [h1, h2] with ω hω1 hω2
      exact (EReal.coe_toReal hω1 hω2).symm
    refine ⟨e, ?_, ?_⟩
    · refine lintegral_congr_ae (e.mono fun ω hω => ?_)
      show ENNReal.ofReal ((h ω).toReal) = (h ω).toENNReal
      conv_rhs => rw [hω]
      rw [toENNReal_coe_real]
    · refine lintegral_congr_ae (e.mono fun ω hω => ?_)
      show ENNReal.ofReal (-(h ω).toReal) = (-h ω).toENNReal
      conv_rhs => rw [hω]
      rw [← EReal.coe_neg, toENNReal_coe_real]
  -- the core: both positive parts integrable
  have core : ∫⁻ ω, (a ω).toENNReal ∂P ≠ ⊤ → ∫⁻ ω, (b ω).toENNReal ∂P ≠ ⊤ →
      (∀ᵐ ω ∂P, a ω = (((a ω).toReal : ℝ) : EReal)) ∧
      (∀ᵐ ω ∂P, b ω = (((b ω).toReal : ℝ) : EReal)) ∧
      Integrable (fun ω => (a ω).toReal) P ∧ Integrable (fun ω => (b ω).toReal) P ∧
      Integrable c P ∧ ∫ ω, c ω ∂P = 0 ∧
      (∀ᵐ ω ∂P, c ω + d ω ≤ (a ω).toReal + (b ω).toReal) := by
    intro hA hB
    have ha_top := ae_ne_top a ham hA
    have hb_top := ae_ne_top b hbm hB
    have ha_bot : ∀ᵐ ω ∂P, a ω ≠ ⊥ := by
      filter_upwards [hb_top] with ω hω hbot
      have := fenchel ω (x ω) (ub ω)
      rw [show s.f ω (x ω) (ub ω) = a ω from rfl, hbot, EReal.coe_sub_bot] at this
      exact hω (top_le_iff.1 this)
    have hb_bot : ∀ᵐ ω ∂P, b ω ≠ ⊥ := by
      filter_upwards [ha_top, ha_bot] with ω h1 h2 hbot
      have := fenchel ω (x ω) (ub ω)
      rw [show s.f ω (x ω) (ub ω) = a ω from rfl, hbot, ← EReal.coe_toReal h1 h2,
        ← EReal.coe_sub] at this
      exact EReal.coe_ne_bot _ (le_bot_iff.1 this)
    obtain ⟨ea, la1, la2⟩ := rep a ham ha_top ha_bot
    obtain ⟨eb, lb1, lb2⟩ := rep b hbm hb_top hb_bot
    have hineq : ∀ᵐ ω ∂P, c ω + d ω ≤ (a ω).toReal + (b ω).toReal := by
      filter_upwards [ea, eb] with ω h1 h2
      have := fenchel ω (x ω) (ub ω)
      rw [show s.f ω (x ω) (ub ω) = a ω from rfl, h1, h2, ← EReal.coe_sub,
        EReal.coe_le_coe_iff] at this
      simp only [hc, hd]; linarith
    have hAm : Measurable (fun ω => (a ω).toReal) := ham.ereal_toReal
    have hBm : Measurable (fun ω => (b ω).toReal) := hbm.ereal_toReal
    -- c has integrable positive part
    have hcpos : ∫⁻ ω, ENNReal.ofReal (c ω) ∂P ≠ ⊤ := by
      have := lint_bound3 c (fun ω => (a ω).toReal) (fun ω => (b ω).toReal) (fun ω => -d ω)
        hAm.aemeasurable hBm.aemeasurable (hineq.mono fun ω hω => by linarith)
      refine ne_top_of_le_ne_top ?_ this
      rw [la1, lb1]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hA, hB⟩,
        hdi.neg.lintegral_lt_top.ne⟩
    obtain ⟨hci, hc0⟩ := L22 (fun ω => x ω) hx hcpos
    have hAi : Integrable (fun ω => (a ω).toReal) P := by
      refine integrable_of_lintegral _ hAm.aestronglyMeasurable (by rw [la1]; exact hA) ?_
      have := lint_bound3 (fun ω => -(a ω).toReal) (fun ω => (b ω).toReal) (fun ω => -c ω)
        (fun ω => -d ω) hBm.aemeasurable hcm.neg.aemeasurable
        (hineq.mono fun ω hω => by linarith)
      refine ne_top_of_le_ne_top ?_ this
      rw [lb1]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hB, hci.neg.lintegral_lt_top.ne⟩,
        hdi.neg.lintegral_lt_top.ne⟩
    have hBi : Integrable (fun ω => (b ω).toReal) P := by
      refine integrable_of_lintegral _ hBm.aestronglyMeasurable (by rw [lb1]; exact hB) ?_
      have := lint_bound3 (fun ω => -(b ω).toReal) (fun ω => (a ω).toReal) (fun ω => -c ω)
        (fun ω => -d ω) hAm.aemeasurable hcm.neg.aemeasurable
        (hineq.mono fun ω hω => by linarith)
      refine ne_top_of_le_ne_top ?_ this
      rw [la1]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hA, hci.neg.lintegral_lt_top.ne⟩,
        hdi.neg.lintegral_lt_top.ne⟩
    exact ⟨ea, eb, hAi, hBi, hci, hc0, hineq⟩
  refine ⟨?_, ?_, ?_⟩
  · -- weak duality
    rw [hdual, hEf]
    by_cases hA : DupacovaWets.Consistency.expect P a = ⊤
    · rw [hA]; exact le_top
    by_cases hB : DupacovaWets.Consistency.expect P b = ⊤
    · rw [hB, EReal.sub_top]; exact bot_le
    obtain ⟨ea, eb, hAi, hBi, hci, hc0, hineq⟩ :=
      core (lint_pos_ne_top a hA) (lint_pos_ne_top b hB)
    rw [expect_eq_of_ae a _ hAi ea, expect_eq_of_ae b _ hBi eb, ← EReal.coe_sub,
      EReal.coe_le_coe_iff]
    have h1 := integral_mono_ae (hci.add hdi) (hAi.add hBi) hineq
    rw [integral_add' hci hdi, integral_add' hAi hBi, hc0] at h1
    linarith
  · -- optimality ⇒ subgradient
    intro hne_top hne_bot heq
    rw [hEf] at hne_top hne_bot heq
    rw [hdual] at heq
    have hB : DupacovaWets.Consistency.expect P b ≠ ⊤ := by
      intro hB
      rw [hB, EReal.sub_top] at heq
      exact hne_bot heq.symm
    obtain ⟨ea, eb, hAi, hBi, hci, hc0, hineq⟩ :=
      core (lint_pos_ne_top a hne_top) (lint_pos_ne_top b hB)
    rw [expect_eq_of_ae a _ hAi ea, expect_eq_of_ae b _ hBi eb, ← EReal.coe_sub,
      EReal.coe_eq_coe_iff] at heq
    -- the nonnegative gap integrates to zero
    set gap : Ω → ℝ := fun ω => (a ω).toReal + (b ω).toReal - (c ω + d ω) with hgap
    have hgi : Integrable gap P := (hAi.add hBi).sub (hci.add hdi)
    have hg0 : ∫ ω, gap ω ∂P = 0 := by
      simp only [hgap]
      rw [integral_sub (f := fun ω => (a ω).toReal + (b ω).toReal) (g := fun ω => c ω + d ω)
        (hAi.add hBi) (hci.add hdi), integral_add hAi hBi,
        integral_add hci hdi, hc0]
      linarith
    have hgnn : 0 ≤ᵐ[P] gap := hineq.mono fun ω hω => by simp only [hgap, Pi.zero_apply]; linarith
    have hgae := (integral_eq_zero_iff_of_nonneg_ae hgnn hgi).1 hg0
    filter_upwards [hgae, ea, eb] with ω hω h1 h2
    simp only [hgap, Pi.zero_apply] at hω
    refine ⟨?_, ?_, ?_⟩
    · show a ω ≠ ⊤
      rw [h1]; exact EReal.coe_ne_top _
    · show a ω ≠ ⊥
      rw [h1]; exact EReal.coe_ne_bot _
    · intro x' u'
      have hf := fenchel ω x' u'
      rw [h2] at hf
      have := ereal_aux _ _ _ hf
      show a ω + _ ≤ _
      rw [h1, ← EReal.coe_add]
      refine le_trans (le_of_eq ?_) this
      congr 1
      rw [dot_sub_left, dot_sub_left]
      simp only [hc, hd] at hω
      linarith
  · -- subgradient ⇒ optimality
    intro hfin hsub x' hx'
    set a' : Ω → EReal := fun ω => s.f ω (x' ω) (ub ω) with ha'
    have hx'm : Measurable (fun ω => x' ω) := x'.stronglyMeasurable.measurable
    have ha'm : Measurable a' := meas_comp s.f hS.normal _ _ hx'm hubm
    show DupacovaWets.Consistency.expect P a ≤ DupacovaWets.Consistency.expect P a'
    by_cases hA' : DupacovaWets.Consistency.expect P a' = ⊤
    · rw [hA']; exact le_top
    by_cases hbot : DupacovaWets.Consistency.expect P a = ⊥
    · rw [hbot]; exact bot_le
    have hpos := lint_pos_ne_top a hfin.ne
    have hneg := lint_neg_ne_top a hbot hfin.ne
    have ha_top : ∀ᵐ ω ∂P, a ω ≠ ⊤ := hsub.mono fun ω h => h.1
    have ha_bot : ∀ᵐ ω ∂P, a ω ≠ ⊥ := hsub.mono fun ω h => h.2.1
    obtain ⟨ea, la1, la2⟩ := rep a ham ha_top ha_bot
    have hAm : Measurable (fun ω => (a ω).toReal) := ham.ereal_toReal
    have hAi : Integrable (fun ω => (a ω).toReal) P :=
      integrable_of_lintegral _ hAm.aestronglyMeasurable (by rw [la1]; exact hpos)
        (by rw [la2]; exact hneg)
    have hpos' := lint_pos_ne_top a' hA'
    have ha'_top := ae_ne_top a' ha'm hpos'
    set e : Ω → ℝ := fun ω => dot (x' ω - x ω) (p.1 ω) with he
    have hsub' : ∀ᵐ ω ∂P, (((a ω).toReal + e ω : ℝ) : EReal) ≤ a' ω := by
      filter_upwards [hsub, ea] with ω hω h1
      have := hω.2.2 (x' ω) (ub ω)
      rw [sub_self] at this
      have hd0 : dot (0 : Fin m → ℝ) (y.1 ω) = 0 := by simp [dot]
      rw [hd0, add_zero] at this
      change a ω + _ ≤ a' ω at this
      rw [h1, ← EReal.coe_add] at this
      exact this
    have ha'_bot : ∀ᵐ ω ∂P, a' ω ≠ ⊥ := by
      filter_upwards [hsub'] with ω hω hb
      rw [hb] at hω
      exact EReal.coe_ne_bot _ (le_bot_iff.1 hω)
    obtain ⟨ea', la1', la2'⟩ := rep a' ha'm ha'_top ha'_bot
    have hA'm : Measurable (fun ω => (a' ω).toReal) := ha'm.ereal_toReal
    have hineq : ∀ᵐ ω ∂P, (a ω).toReal + e ω ≤ (a' ω).toReal := by
      filter_upwards [hsub', ea'] with ω h1 h2
      rw [h2, EReal.coe_le_coe_iff] at h1
      exact h1
    have hem : Measurable e := by
      simp only [he, dot]
      exact Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).comp (hx'm.sub hxm)).mul ((measurable_pi_apply i).comp hpm)
    have hepos : ∫⁻ ω, ENNReal.ofReal (e ω) ∂P ≠ ⊤ := by
      have := lint_bound3 e (fun ω => (a' ω).toReal) (fun ω => -(a ω).toReal) (fun _ => 0)
        hA'm.aemeasurable hAm.neg.aemeasurable (hineq.mono fun ω hω => by linarith)
      refine ne_top_of_le_ne_top ?_ this
      rw [la1']
      simp only [ENNReal.ofReal_zero, lintegral_zero, add_zero]
      exact ENNReal.add_ne_top.2 ⟨hpos', hAi.neg.lintegral_lt_top.ne⟩
    have hadapt : ∀ i, ∃ g : Ω → ℝ, StronglyMeasurable[𝔽 (τ i)] g ∧
        (fun ω => (x' ω - x ω) i) =ᵐ[P] g := by
      intro i
      obtain ⟨g, hg, hxg⟩ := hx i
      obtain ⟨g', hg', hxg'⟩ := hx' i
      refine ⟨fun ω => g' ω - g ω, hg'.sub hg, ?_⟩
      filter_upwards [hxg, hxg'] with ω h1 h2
      simp only [Pi.sub_apply]
      rw [← h1, ← h2]
    obtain ⟨hei, he0⟩ := L22 (fun ω => x' ω - x ω) hadapt hepos
    have hA'i : Integrable (fun ω => (a' ω).toReal) P := by
      refine integrable_of_lintegral _ hA'm.aestronglyMeasurable (by rw [la1']; exact hpos') ?_
      have := lint_bound3 (fun ω => -(a' ω).toReal) (fun ω => -(a ω).toReal) (fun ω => -e ω)
        (fun _ => 0) hAm.neg.aemeasurable hem.neg.aemeasurable
        (hineq.mono fun ω hω => by linarith)
      refine ne_top_of_le_ne_top ?_ this
      simp only [ENNReal.ofReal_zero, lintegral_zero, add_zero]
      exact ENNReal.add_ne_top.2 ⟨hAi.neg.lintegral_lt_top.ne, hei.neg.lintegral_lt_top.ne⟩
    rw [expect_eq_of_ae a _ hAi ea, expect_eq_of_ae a' _ hA'i ea', EReal.coe_le_coe_iff]
    have h1 := integral_mono_ae (hAi.add hei) hA'i hineq
    rw [integral_add' hAi hei, he0] at h1
    linarith

end Main

end CSDW

open ConvStochDual.Existence in
theorem solution {Ω X U : Type*} [MeasurableSpace Ω]
  [AddCommGroup X] [Module ℝ X] [UniformSpace X]
  [IsUniformAddGroup X] [ContinuousSMul ℝ X]
  [AddCommGroup U] [Module ℝ U] [UniformSpace U]
  [IsUniformAddGroup U] [ContinuousSMul ℝ U]
  {T n m : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {τ : Fin n → Fin (T + 1)}
  {𝔽 : Fin (T + 1) → MeasurableSpace Ω}
  {ιX : X →ₗ[ℝ] RV Ω P n} {ιU : U →ₗ[ℝ] RV Ω P m}
  {V : Submodule ℝ (RV Ω P n)} {Y : Submodule ℝ (RV Ω P m)}
    (s : Setting P τ 𝔽 ιX ιU V Y)
    (hS : Standing s) (x : RV Ω P n) (hx : Adapted τ 𝔽 P x)
    (p : V) (hp : p ∈ XaPerp s) (y : Y) :
    dualObj s p y ≤ Ef s x (ιU s.ubar) ∧
    (Ef s x (ιU s.ubar) ≠ ⊤ → Ef s x (ιU s.ubar) ≠ ⊥ →
      dualObj s p y = Ef s x (ιU s.ubar) →
      ∀ᵐ ω ∂P, IsSubgradAt (s.f ω) (x ω) (ιU s.ubar ω) (p.1 ω) (y.1 ω)) ∧
    (Ef s x (ιU s.ubar) < ⊤ →
      (∀ᵐ ω ∂P, IsSubgradAt (s.f ω) (x ω) (ιU s.ubar ω) (p.1 ω) (y.1 ω)) →
      ∀ x' : RV Ω P n, Adapted τ 𝔽 P x' → Ef s x (ιU s.ubar) ≤ Ef s x' (ιU s.ubar)) :=
  CSDW.main s hS x hx p hp y
