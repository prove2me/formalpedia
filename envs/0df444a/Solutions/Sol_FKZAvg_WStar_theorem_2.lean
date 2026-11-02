-- Prove2me | solution 1 for FKZAvg.WStar.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T15:43:40.778776+00:00
-- url     : https://prove2.me/submissions/db9ea844-8ea6-443a-bd50-c8e026d8f00a

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions
import Theorems.Thm_SchalAvg_AvgOpt_lemma_2_3_ii

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter Metric SchalAvg.AvgOpt FKZAvg.WStar

/-- A Kuratowski–Ryll-Nardzewski type selection theorem for compact-valued maps: if every
`F x` is nonempty and compact and `{x | F x ∩ U ≠ ∅}` is measurable for every open `U`, then
`F` has a measurable selector. -/
theorem krn_compact_selector {X A : Type*} [MeasurableSpace X]
    [MetricSpace A] [TopologicalSpace.SeparableSpace A] [MeasurableSpace A] [BorelSpace A]
    (F : X → Set A) (hne : ∀ x, (F x).Nonempty) (hcpt : ∀ x, IsCompact (F x))
    (hmeas : ∀ U : Set A, IsOpen U → MeasurableSet {x | (F x ∩ U).Nonempty}) :
    ∃ f : X → A, Measurable f ∧ ∀ x, f x ∈ F x := by
  classical
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · refine ⟨fun x => isEmptyElim x, fun s _ => ?_, fun x => isEmptyElim x⟩
    convert MeasurableSet.empty
    ext x; exact isEmptyElim x
  have : Nonempty A := ⟨(hne x₀).some⟩
  set d : ℕ → A := TopologicalSpace.denseSeq A with hd
  have hdense : DenseRange d := TopologicalSpace.denseRange_denseSeq A
  set r : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n with hr
  have hrpos : ∀ n, 0 < r n := fun n => by positivity
  -- indices
  let P : ℕ → ℕ → X → ℕ → Prop := fun n i x k =>
    (F x ∩ (ball (d k) (r (n + 1)) ∩ ball (d i) (r n))).Nonempty
  let g : ℕ → X → ℕ := fun n => Nat.rec
    (fun x => if h : ∃ k, (F x ∩ ball (d k) 1).Nonempty then Nat.find h else 0)
    (fun n gn x => if h : ∃ k, P n (gn x) x k then Nat.find h else 0) n
  have g_zero : ∀ x, g 0 x =
      if h : ∃ k, (F x ∩ ball (d k) 1).Nonempty then Nat.find h else 0 := fun x => rfl
  have g_succ : ∀ n x, g (n + 1) x =
      if h : ∃ k, P n (g n x) x k then Nat.find h else 0 := fun n x => rfl
  -- existence of a dense point near any point of `F x`
  have near : ∀ (y : A) (ε : ℝ), 0 < ε → ∃ k, dist y (d k) < ε := by
    intro y ε hε
    obtain ⟨k, hk⟩ := hdense.exists_dist_lt y hε
    exact ⟨k, hk⟩
  -- invariant: `F x` meets the ball of radius `r n` around `d (g n x)`
  have inv : ∀ n x, (F x ∩ ball (d (g n x)) (r n)).Nonempty := by
    intro n
    induction n with
    | zero =>
      intro x
      have h : ∃ k, (F x ∩ ball (d k) 1).Nonempty := by
        obtain ⟨y, hy⟩ := hne x
        obtain ⟨k, hk⟩ := near y 1 one_pos
        exact ⟨k, y, hy, by rw [mem_ball]; exact hk⟩
      rw [g_zero, dif_pos h]
      simpa [hr] using Nat.find_spec h
    | succ n ih =>
      intro x
      have h : ∃ k, P n (g n x) x k := by
        obtain ⟨y, hyF, hyb⟩ := ih x
        obtain ⟨k, hk⟩ := near y (r (n + 1)) (hrpos _)
        exact ⟨k, y, hyF, by rw [mem_ball]; exact hk, hyb⟩
      rw [g_succ, dif_pos h]
      obtain ⟨y, hyF, hy1, -⟩ := Nat.find_spec h
      exact ⟨y, hyF, hy1⟩
  have hP_ex : ∀ n x, ∃ k, P n (g n x) x k := by
    intro n x
    obtain ⟨y, hyF, hyb⟩ := inv n x
    obtain ⟨k, hk⟩ := near y (r (n + 1)) (hrpos _)
    exact ⟨k, y, hyF, by rw [mem_ball]; exact hk, hyb⟩
  -- measurability of the index maps
  have hPm : ∀ n i k, MeasurableSet {x | P n i x k} := fun n i k =>
    hmeas _ (isOpen_ball.inter isOpen_ball)
  have gmeas : ∀ n, Measurable (g n) := by
    intro n
    induction n with
    | zero =>
      refine measurable_to_countable' fun k => ?_
      have h0 : ∀ x, ∃ k, (F x ∩ ball (d k) 1).Nonempty := by
        intro x; obtain ⟨y, hy⟩ := hne x
        obtain ⟨k, hk⟩ := near y 1 one_pos
        exact ⟨k, y, hy, by rw [mem_ball]; exact hk⟩
      have : g 0 ⁻¹' {k} = {x | (F x ∩ ball (d k) 1).Nonempty} ∩
          ⋂ j ∈ Finset.range k, {x | (F x ∩ ball (d j) 1).Nonempty}ᶜ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, g_zero, dif_pos (h0 x),
          Nat.find_eq_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter,
          Finset.mem_range, Set.mem_compl_iff]
      rw [this]
      exact (hmeas _ isOpen_ball).inter (Finset.measurableSet_biInter _ fun j _ =>
        (hmeas _ isOpen_ball).compl)
    | succ n ih =>
      refine measurable_to_countable' fun k => ?_
      have hPx : ∀ j, MeasurableSet {x | P n (g n x) x j} := by
        intro j
        have : {x | P n (g n x) x j} = ⋃ i, (g n ⁻¹' {i} ∩ {x | P n i x j}) := by
          ext x; simp
        rw [this]
        exact MeasurableSet.iUnion fun i => (ih (measurableSet_singleton i)).inter (hPm n i j)
      have : g (n + 1) ⁻¹' {k} = {x | P n (g n x) x k} ∩
          ⋂ j ∈ Finset.range k, {x | P n (g n x) x j}ᶜ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, g_succ, dif_pos (hP_ex n x),
          Nat.find_eq_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter,
          Finset.mem_range, Set.mem_compl_iff]
      rw [this]
      exact (hPx k).inter (Finset.measurableSet_biInter _ fun j _ => (hPx j).compl)
  -- the approximating points
  set p : ℕ → X → A := fun n x => d (g n x) with hp
  have pmeas : ∀ n, Measurable (p n) := fun n =>
    (measurable_from_top (f := d)).comp (gmeas n)
  have pstep : ∀ n x, dist (p n x) (p (n + 1) x) ≤ 4 / 2 / 2 ^ n := by
    intro n x
    have h := hP_ex n x
    have hs : P n (g n x) x (g (n + 1) x) := by
      rw [g_succ, dif_pos h]; exact Nat.find_spec h
    obtain ⟨y, -, hy1, hy2⟩ := hs
    rw [mem_ball] at hy1 hy2
    calc dist (p n x) (p (n + 1) x) ≤ dist y (p n x) + dist y (p (n + 1) x) :=
          dist_triangle_left _ _ _
      _ ≤ r n + r (n + 1) := add_le_add hy2.le hy1.le
      _ ≤ 4 / 2 / 2 ^ n := by
          simp only [hr, one_div, inv_pow, pow_succ]
          have : (0 : ℝ) < 2 ^ n := by positivity
          rw [div_div, mul_inv]
          field_simp
          norm_num
  have hcauchy : ∀ x, CauchySeq (fun n => p n x) := fun x =>
    cauchySeq_of_le_geometric_two (C := 4) (pstep · x)
  have hconv : ∀ x, ∃ a ∈ F x, Tendsto (fun n => p n x) atTop (𝓝 a) := by
    intro x
    choose y hyF hyb using fun n => inv n x
    obtain ⟨a, haF, φ, hφ, hlim⟩ := (hcpt x).tendsto_subseq hyF
    refine ⟨a, haF, tendsto_nhds_of_cauchySeq_of_subseq (hcauchy x) hφ.tendsto_atTop ?_⟩
    have hr0 : Tendsto (fun k => r (φ k)) atTop (𝓝 0) := by
      have : Tendsto r atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      exact this.comp hφ.tendsto_atTop
    refine tendsto_iff_dist_tendsto_zero.2 ?_
    have h1 : Tendsto (fun k => dist (y (φ k)) a) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.1 hlim
    refine squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) (by simpa using hr0.add h1)
    calc dist (p (φ k) x) a ≤ dist (p (φ k) x) (y (φ k)) + dist (y (φ k)) a := dist_triangle _ _ _
      _ ≤ r (φ k) + dist (y (φ k)) a := by
          gcongr
          have := hyb (φ k); rw [mem_ball, dist_comm] at this; exact this.le
  choose a haF hlim using hconv
  refine ⟨a, measurable_of_tendsto_metrizable pmeas (tendsto_pi_nhds.2 hlim), haF⟩

/-- `f ≤ liminf u` and `g ≤ liminf v` give `f + g ≤ liminf (u + v)` in `[0, ∞]`. -/
theorem fkz3_add_le_liminf {f g : ℝ≥0∞} {u v : ℕ → ℝ≥0∞}
    (hf : f ≤ liminf u atTop) (hg : g ≤ liminf v atTop) :
    f + g ≤ liminf (fun n => u n + v n) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun z hz => ?_
  refine le_liminf_of_le (by isBoundedDefault) ?_
  rcases eq_or_ne f 0 with h0 | h0
  · rw [h0, zero_add] at hz
    exact (eventually_lt_of_lt_liminf (lt_of_lt_of_le hz hg)).mono fun n hn =>
      hn.le.trans le_add_self
  rcases eq_or_ne g 0 with h0' | h0'
  · rw [h0', add_zero] at hz
    exact (eventually_lt_of_lt_liminf (lt_of_lt_of_le hz hf)).mono fun n hn =>
      hn.le.trans le_self_add
  obtain ⟨y', hy', z', hz', hl⟩ := ENNReal.exists_lt_add_of_lt_add hz h0 h0'
  exact ((eventually_lt_of_lt_liminf (lt_of_lt_of_le hy' hf)).and
    (eventually_lt_of_lt_liminf (lt_of_lt_of_le hz' hg))).mono fun n hn =>
      hl.le.trans (add_le_add hn.1.le hn.2.le)

theorem fkz3_eta_eq {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (M : Model X A) (u : X → ℝ≥0∞) (x : X) (a : A) :
    eta M u 1 x a = M.toMDP.cost x a + ∫⁻ y, u y ∂(M.toMDP.q (x, a)) := by
  simp [eta]

section Core
variable {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]

/-- Joint sequential lower semicontinuity of `η¹_u` on `Gr(A)` (proof of Lemma 3). -/
theorem fkz3_eta_lsc (M : Model X A) (hW : CondWStar M) (u : X → ℝ≥0∞)
    (hu : LowerSemicontinuous u)
    (xs : ℕ → X) (x : X) (as : ℕ → A) (a : A) (hx : Tendsto xs atTop (𝓝 x))
    (ha : Tendsto as atTop (𝓝 a)) (has : ∀ n, as n ∈ M.Aset (xs n)) (haA : a ∈ M.Aset x) :
    eta M u 1 x a ≤ liminf (fun n => eta M u 1 (xs n) (as n)) atTop := by
  obtain ⟨hi, -, hiii⟩ := hW
  have hgr : Tendsto (fun k => (xs k, as k)) atTop (𝓝[graphA M] (x, a)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hx.prodMk_nhds ha, Eventually.of_forall fun k => has k⟩
  have hc : M.toMDP.cost x a ≤ liminf (fun k => M.toMDP.cost (xs k) (as k)) atTop := by
    refine le_of_forall_lt_imp_le_of_dense fun y hy => ?_
    have hev := hgr.eventually ((hi (x, a) haA) y hy)
    exact le_liminf_of_le (by isBoundedDefault) (hev.mono fun k hk => le_of_lt hk)
  have hum : Measurable u := hu.measurable
  have hI : ∫⁻ y, u y ∂(M.toMDP.q (x, a)) ≤
      liminf (fun k => ∫⁻ y, u y ∂(M.toMDP.q (xs k, as k))) atTop := by
    letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
    let μ : ProbabilityMeasure X := ⟨M.toMDP.q (x, a), inferInstance⟩
    let μs : ℕ → ProbabilityMeasure X := fun n => ⟨M.toMDP.q (xs n, as n), inferInstance⟩
    have hμ : Tendsto μs atTop (𝓝 μ) := by
      rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
      intro f
      exact ((hiii f) (x, a) haA).tendsto.comp hgr
    have h4 := SchalAvg.AvgOpt.lemma_2_3_ii μ μs hμ (fun _ => u) (fun _ => hum)
    refine le_trans (lintegral_mono fun z => ?_) h4
    show u z ≤ liminf (fun p : ℕ × X => u p.2) (atTop ×ˢ 𝓝 z)
    rw [show (fun p : ℕ × X => u p.2) = u ∘ Prod.snd from rfl, liminf_comp, map_snd_prod]
    exact hu.le_liminf z
  simp only [fkz3_eta_eq]
  exact fkz3_add_le_liminf hc hI

/-- The compactness step of the proof of Lemma 3: near-minimizers over `A(xₙ) ∩ C` along
`xₙ → x` cluster at a point of `A(x) ∩ C`. -/
theorem fkz3_cluster (M : Model X A) (hW : CondWStar M) (u : X → ℝ≥0∞)
    (hu : LowerSemicontinuous u) (C : Set A) (hC : IsClosed C)
    (xs : ℕ → X) (x : X) (hx : Tendsto xs atTop (𝓝 x)) (as : ℕ → A)
    (has : ∀ n, as n ∈ M.Aset (xs n) ∩ C) (B : ℝ≥0)
    (hB : ∀ n, eta M u 1 (xs n) (as n) ≤ B) (t : ℝ≥0∞)
    (ht : ∀ n, eta M u 1 (xs n) (as n) ≤ t + ((n : ℝ≥0∞) + 1)⁻¹) :
    ∃ a ∈ M.Aset x ∩ C, eta M u 1 x a ≤ t ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (as ∘ ψ) atTop (𝓝 a) := by
  have hc : ∀ n, M.toMDP.cost (xs n) (as n) ≤ B := fun n =>
    le_trans (by rw [fkz3_eta_eq]; exact le_self_add) (hB n)
  obtain ⟨a, haA, hcl⟩ := hW.2.1 xs x as hx (fun n => (has n).1) ⟨B, hc⟩
  obtain ⟨ψ, hψ, hlim⟩ := hcl.tendsto_subseq
  have haC : a ∈ C := hC.mem_of_tendsto hlim (Eventually.of_forall fun k => (has (ψ k)).2)
  refine ⟨a, ⟨haA, haC⟩, ?_, ψ, hψ, hlim⟩
  have h1 := fkz3_eta_lsc M hW u hu (xs ∘ ψ) x (as ∘ ψ) a (hx.comp hψ.tendsto_atTop) hlim
    (fun k => (has (ψ k)).1) haA
  refine h1.trans ?_
  have hε : Tendsto (fun k => t + ((ψ k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 t) := by
    have h0 : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def] using this
    simpa using tendsto_const_nhds.add (h0.comp hψ.tendsto_atTop)
  calc liminf (fun k => eta M u 1 ((xs ∘ ψ) k) ((as ∘ ψ) k)) atTop
      ≤ liminf (fun k => t + ((ψ k : ℝ≥0∞) + 1)⁻¹) atTop :=
        liminf_le_liminf (Eventually.of_forall fun k => ht (ψ k))
    _ = t := hε.liminf_eq

/-- `G_C(x) = inf_{a ∈ A(x) ∩ C} η¹_u(x, a)`. -/
noncomputable def fkz3G (M : Model X A) (u : X → ℝ≥0∞) (C : Set A) (x : X) : ℝ≥0∞ :=
  ⨅ a ∈ M.Aset x ∩ C, eta M u 1 x a

theorem fkz3_exists_lt (M : Model X A) (u : X → ℝ≥0∞) (C : Set A) (x : X) {t : ℝ≥0∞}
    (h : fkz3G M u C x < t) : ∃ a ∈ M.Aset x ∩ C, eta M u 1 x a < t := by
  unfold fkz3G at h
  obtain ⟨a, ha⟩ := iInf_lt_iff.1 h
  obtain ⟨hmem, ha'⟩ := iInf_lt_iff.1 ha
  exact ⟨a, hmem, ha'⟩

theorem fkz3_attain (M : Model X A) (hW : CondWStar M) (u : X → ℝ≥0∞)
    (hu : LowerSemicontinuous u) (C : Set A) (hC : IsClosed C) (x : X)
    (hG : fkz3G M u C x ≠ ⊤) : ∃ a ∈ M.Aset x ∩ C, eta M u 1 x a = fkz3G M u C x := by
  set G := fkz3G M u C x
  have hlt : ∀ n : ℕ, G < G + ((n : ℝ≥0∞) + 1)⁻¹ := fun n =>
    ENNReal.lt_add_right hG (by simp)
  choose as has hlt' using fun n => fkz3_exists_lt M u C x (hlt n)
  have hB : ∀ n, eta M u 1 x (as n) ≤ ((G + 1).toNNReal : ℝ≥0∞) := by
    intro n
    rw [ENNReal.coe_toNNReal (by simpa using hG)]
    refine (hlt' n).le.trans (add_le_add le_rfl ?_)
    exact ENNReal.inv_le_one.2 (by simp)
  obtain ⟨a, haS, ha, -⟩ := fkz3_cluster M hW u hu C hC (fun _ => x) x tendsto_const_nhds as has
    _ hB G (fun n => (hlt' n).le)
  exact ⟨a, haS, le_antisymm ha (biInf_le _ haS)⟩

theorem fkz3_lsc (M : Model X A) (hW : CondWStar M) (u : X → ℝ≥0∞)
    (hu : LowerSemicontinuous u) (C : Set A) (hC : IsClosed C) :
    LowerSemicontinuous (fkz3G M u C) := by
  intro x y hy
  by_contra hne
  rw [Filter.not_eventually] at hne
  obtain ⟨xs, hxs, hle⟩ := exists_seq_forall_of_frequently hne
  have hyt : y ≠ ⊤ := ne_top_of_lt hy
  have hlt : ∀ n : ℕ, fkz3G M u C (xs n) < y + ((n : ℝ≥0∞) + 1)⁻¹ := fun n =>
    lt_of_le_of_lt (not_lt.1 (hle n)) (ENNReal.lt_add_right hyt (by simp))
  choose as has hlt' using fun n => fkz3_exists_lt M u C (xs n) (hlt n)
  have hB : ∀ n, eta M u 1 (xs n) (as n) ≤ ((y + 1).toNNReal : ℝ≥0∞) := by
    intro n
    rw [ENNReal.coe_toNNReal (by simpa using hyt)]
    refine (hlt' n).le.trans (add_le_add le_rfl ?_)
    exact ENNReal.inv_le_one.2 (by simp)
  obtain ⟨a, haS, ha, -⟩ := fkz3_cluster M hW u hu C hC xs x hxs as has _ hB y
    (fun n => (hlt' n).le)
  exact absurd (lt_of_lt_of_le hy ((biInf_le _ haS).trans ha)) (lt_irrefl _)

/-- Level sets of `η¹_u(x, ·)` on `A(x)` are compact (Lemma 2(b) for lower semicontinuous `u`). -/
theorem fkz3_level_compact (M : Model X A) (hW : CondWStar M) (u : X → ℝ≥0∞)
    (hu : LowerSemicontinuous u) (x : X) (l : ℝ≥0) :
    IsCompact {a | a ∈ M.Aset x ∧ eta M u 1 x a ≤ l} := by
  apply IsSeqCompact.isCompact
  intro as has
  obtain ⟨a, haS, ha, ψ, hψ, hlim⟩ := fkz3_cluster M hW u hu Set.univ isClosed_univ
    (fun _ => x) x tendsto_const_nhds as (fun n => ⟨(has n).1, trivial⟩) l (fun n => (has n).2)
    l (fun n => (has n).2.trans le_self_add)
  exact ⟨a, ⟨haS.1, ha⟩, ψ, hψ, hlim⟩

end Core


theorem fkz3_lemma3 {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (M : Model X A) (hsel : HasSelector M)
    (hW : CondWStar M) (u : X → ℝ≥0∞) (hul : LowerSemicontinuous u) :
    LowerSemicontinuous (uStar M u) ∧
    (∃ f : X → A, IsStationary M f ∧ ∀ x, uStar M u x = eta M u 1 x (f x)) ∧
    (∀ x, (AsubStar M u x).Nonempty) ∧
    MeasurableSet {p : X × A | p.2 ∈ AsubStar M u p.1} ∧
    ∀ x, (uStar M u x = ⊤ → AsubStar M u x = M.Aset x) ∧
      (uStar M u x ≠ ⊤ → IsCompact (AsubStar M u x)) := by
  classical
  have hG : uStar M u = fkz3G M u Set.univ := by
    funext x; simp [uStar, fkz3G]
  have hlsc : LowerSemicontinuous (uStar M u) := hG ▸ fkz3_lsc M hW u hul _ isClosed_univ
  have hum : Measurable (uStar M u) := hlsc.measurable
  have hle : ∀ x a, a ∈ M.Aset x → uStar M u x ≤ eta M u 1 x a := fun x a ha =>
    biInf_le (fun a => eta M u 1 x a) ha
  have hmemiff : ∀ x a, a ∈ AsubStar M u x ↔ a ∈ M.Aset x ∧ eta M u 1 x a ≤ uStar M u x :=
    fun x a => ⟨fun h => ⟨h.1, h.2.ge⟩, fun h => ⟨h.1, le_antisymm (hle x a h.1) h.2⟩⟩
  have htop : ∀ x, uStar M u x = ⊤ → AsubStar M u x = M.Aset x := by
    intro x hx; ext a
    rw [hmemiff, hx]; simp
  have hattain : ∀ x, uStar M u x ≠ ⊤ → ∃ a ∈ M.Aset x, eta M u 1 x a = uStar M u x := by
    intro x hx
    rw [hG] at hx ⊢
    obtain ⟨a, ha, he⟩ := fkz3_attain M hW u hul _ isClosed_univ x hx
    exact ⟨a, ha.1, he⟩
  have hne : ∀ x, (AsubStar M u x).Nonempty := by
    intro x
    by_cases hx : uStar M u x = ⊤
    · rw [htop x hx]; exact M.Aset_nonempty x
    · obtain ⟨a, ha, he⟩ := hattain x hx
      exact ⟨a, ha, he.symm⟩
  have hcpt : ∀ x, uStar M u x ≠ ⊤ → IsCompact (AsubStar M u x) := by
    intro x hx
    have hc := fkz3_level_compact M hW u hul x (uStar M u x).toNNReal
    convert hc using 1
    ext a
    rw [hmemiff, ENNReal.coe_toNNReal hx]
    rfl
  have hetam : Measurable (fun p : X × A => eta M u 1 p.1 p.2) := by
    simp only [fkz3_eta_eq]
    refine M.cost_meas.add ?_
    simpa using (hul.measurable.lintegral_kernel (κ := M.toMDP.q))
  have hgraph : MeasurableSet {p : X × A | p.2 ∈ AsubStar M u p.1} :=
    M.graph_meas.inter (measurableSet_eq_fun (hum.comp measurable_fst) hetam)
  refine ⟨hlsc, ?_, hne, hgraph, fun x => ⟨htop x, hcpt x⟩⟩
  -- the selector
  obtain ⟨φ₀, hφ₀m, hφ₀A⟩ := hsel
  let F : X → Set A := fun x => if uStar M u x = ⊤ then {φ₀ x} else AsubStar M u x
  letI : MetricSpace A := TopologicalSpace.metrizableSpaceMetric A
  have hFne : ∀ x, (F x).Nonempty := by
    intro x; by_cases hx : uStar M u x = ⊤
    · simp [F, hx]
    · simp only [F, hx, if_false]; exact hne x
  have hFc : ∀ x, IsCompact (F x) := by
    intro x; by_cases hx : uStar M u x = ⊤
    · simp [F, hx]
    · simp only [F, hx, if_false]; exact hcpt x hx
  have hFm : ∀ U : Set A, IsOpen U → MeasurableSet {x | (F x ∩ U).Nonempty} := by
    intro U hU
    obtain ⟨Cs, hCc, hCsub, hCU, -⟩ := hU.exists_iUnion_isClosed
    have hGm : ∀ m, Measurable (fkz3G M u (Cs m)) := fun m =>
      (fkz3_lsc M hW u hul (Cs m) (hCc m)).measurable
    have : {x | (F x ∩ U).Nonempty} =
        ({x | uStar M u x = ⊤} ∩ φ₀ ⁻¹' U) ∪
          ({x | uStar M u x = ⊤}ᶜ ∩ ⋃ m, {x | fkz3G M u (Cs m) x ≤ uStar M u x}) := by
      ext x
      by_cases hx : uStar M u x = ⊤
      · simp [F, hx]
      · simp only [F, hx, if_false, Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff,
          Set.mem_compl_iff, false_and, false_or, not_false_eq_true,
          true_and, Set.mem_iUnion]
        constructor
        · rintro ⟨a, haS, haU⟩
          rw [← hCU] at haU
          obtain ⟨m, hm⟩ := Set.mem_iUnion.1 haU
          exact ⟨m, (show fkz3G M u (Cs m) x ≤ eta M u 1 x a from
            biInf_le _ (show a ∈ M.Aset x ∩ Cs m from ⟨haS.1, hm⟩)).trans haS.2.ge⟩
        · rintro ⟨m, hm⟩
          obtain ⟨a, ha, he⟩ := fkz3_attain M hW u hul (Cs m) (hCc m) x
            (ne_top_of_le_ne_top hx hm)
          refine ⟨a, (hmemiff x a).2 ⟨ha.1, he ▸ hm⟩, hCsub m ha.2⟩
    rw [this]
    refine ((hum (measurableSet_singleton ⊤)).inter (hφ₀m hU.measurableSet)).union
      (((hum (measurableSet_singleton ⊤)).compl).inter
        (MeasurableSet.iUnion fun m => measurableSet_le (hGm m) hum))
  obtain ⟨f, hfm, hfF⟩ := krn_compact_selector F hFne hFc hFm
  refine ⟨f, ⟨hfm, fun x => ?_⟩, fun x => ?_⟩
  · have := hfF x
    by_cases hx : uStar M u x = ⊤
    · simp only [F, hx, if_true, Set.mem_singleton_iff] at this; rw [this]; exact hφ₀A x
    · simp only [F, hx, if_false] at this; exact this.1
  · have := hfF x
    by_cases hx : uStar M u x = ⊤
    · simp only [F, hx, if_true, Set.mem_singleton_iff] at this
      rw [hx, this]
      exact (top_le_iff.1 (hx ▸ hle x _ (hφ₀A x))).symm
    · simp only [F, hx, if_false] at this; exact this.2

/-! ### Path-measure lemmas -/

namespace FKZT2

open FeinbergLiang.ACOE

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

instance initP (π : Policy X A) (x : X) : IsProbabilityMeasure (initMeasure π x) := by
  unfold initMeasure; exact Measure.isProbabilityMeasure_map (by fun_prop)

instance pathP (M : MDP X A) (π : Policy X A) (x : X) :
    IsProbabilityMeasure (pathMeasure M π x) := by
  unfold pathMeasure; infer_instance

lemma path_zero (M : MDP X A) (π : Policy X A) (x : X) {F : X × A → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ω, F (ω 0) ∂(pathMeasure M π x) = ∫⁻ p, F p ∂(initMeasure π x) := by
  unfold pathMeasure Kernel.trajMeasure
  rw [Measure.lintegral_bind (f := fun ω : ℕ → X × A => F (ω 0)) (Kernel.aemeasurable _) (hF.comp (measurable_pi_apply 0)).aemeasurable]
  have hz : ∀ x₀ : (Π _ : Finset.Iic 0, X × A),
      ∫⁻ ω, F (ω 0) ∂(Kernel.traj (X := fun _ => X × A) (stepKernel M π) 0 x₀) = F (x₀ ⟨0, by simp⟩) := by
    intro x₀
    have hm : Measurable (fun y : (Π _ : Finset.Iic 0, X × A) => F (y ⟨0, by simp⟩)) :=
      hF.comp (measurable_pi_apply _)
    have : ∫⁻ ω, F (ω 0) ∂(Kernel.traj (X := fun _ => X × A) (stepKernel M π) 0 x₀) =
        ∫⁻ y, F (y ⟨0, by simp⟩) ∂((Kernel.traj (X := fun _ => X × A) (stepKernel M π) 0 x₀).map
          (Preorder.frestrictLe 0)) := by
      rw [lintegral_map hm (by fun_prop)]; rfl
    rw [this, ← Kernel.map_apply _ (by fun_prop),
      Kernel.traj_map_frestrictLe_of_le (le_refl 0), Kernel.lintegral_deterministic' _ hm]
    rfl
  simp_rw [hz]
  rw [lintegral_map (f := fun y : (Π _ : Finset.Iic 0, X × A) => F (y ⟨0, by simp⟩))
    (hF.comp (measurable_pi_apply _)) (by fun_prop)]
  rfl

lemma path_succ (M : MDP X A) (π : Policy X A) (x : X) (t : ℕ) {F : X × A → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ω, F (ω (t + 1)) ∂(pathMeasure M π x) =
      ∫⁻ ω, ∫⁻ p, F p ∂(stepKernel M π t (Preorder.frestrictLe t ω)) ∂(pathMeasure M π x) := by
  have h1 : ∫⁻ ω, F (ω (t + 1)) ∂(pathMeasure M π x) =
      ∫⁻ z, F z.2 ∂((pathMeasure M π x).map (fun ω => (Preorder.frestrictLe t ω, ω (t + 1)))) := by
    rw [lintegral_map (f := fun z : (Π _ : Finset.Iic t, X × A) × (X × A) => F z.2)
      (hF.comp measurable_snd) (by fun_prop)]
  rw [h1]
  unfold pathMeasure
  rw [← Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    Measure.lintegral_compProd (f := fun z : (Π _ : Finset.Iic t, X × A) × (X × A) => F z.2)
      (hF.comp measurable_snd),
    lintegral_map (hF.lintegral_kernel) (by fun_prop)]

/-- A deterministic Markov policy `a_t = f_t(x_t)`. -/
noncomputable def markovPolicy (fs : ℕ → X → A) (hfs : ∀ t, Measurable (fs t)) : Policy X A where
  rule t := Kernel.deterministic (fun h => fs t h.2) ((hfs t).comp measurable_snd)

lemma step_markov (M : MDP X A) (fs : ℕ → X → A) (hfs : ∀ t, Measurable (fs t)) (t : ℕ)
    (h : Π _ : Finset.Iic t, X × A) {F : X × A → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂(stepKernel M (markovPolicy fs hfs) t h) =
      ∫⁻ y, F (y, fs (t + 1) y) ∂(M.q (lastPair t h)) := by
  have : IsMarkovKernel (M.q.comap (lastPair (X := X) (A := A) t) (measurable_pi_apply _)) :=
    Kernel.IsMarkovKernel.comap _ _
  unfold stepKernel
  rw [Kernel.lintegral_compProd _ _ _ hF]
  simp only [Kernel.comap_apply, markovPolicy]
  congr 1; ext y
  rw [Kernel.lintegral_deterministic' (f := fun c => F (y, c)) _ (hF.comp measurable_prodMk_left)]

lemma init_markov (fs : ℕ → X → A) (hfs : ∀ t, Measurable (fs t)) (x : X) {F : X × A → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ p, F p ∂(initMeasure (markovPolicy fs hfs) x) = F (x, fs 0 x) := by
  unfold initMeasure
  rw [lintegral_map hF (by fun_prop)]
  simp only [markovPolicy]
  rw [Kernel.lintegral_deterministic' (f := fun c => F (x, c)) _ (hF.comp measurable_prodMk_left)]

lemma law_markov (M : MDP X A) (fs : ℕ → X → A) (hfs : ∀ t, Measurable (fs t)) (x : X) (t : ℕ)
    {F : X × A → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (ω t) ∂(pathMeasure M (markovPolicy fs hfs) x) =
      ∫⁻ ω, F ((ω t).1, fs t (ω t).1) ∂(pathMeasure M (markovPolicy fs hfs) x) := by
  have hF' : Measurable (fun p : X × A => F (p.1, fs t p.1)) :=
    hF.comp (measurable_fst.prodMk ((hfs t).comp measurable_fst))
  cases t with
  | zero =>
    rw [path_zero _ _ _ hF, path_zero _ _ _ hF', init_markov _ _ _ hF, init_markov _ _ _ hF']
  | succ t =>
    rw [path_succ _ _ _ _ hF, path_succ _ _ _ _ hF']
    simp_rw [step_markov _ _ _ _ _ hF, step_markov _ _ _ _ _ hF']

lemma step_marg (M : MDP X A) (π : Policy X A) (t : ℕ) (h : Π _ : Finset.Iic t, X × A)
    {G : X → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ p, G p.1 ∂(stepKernel M π t h) = ∫⁻ y, G y ∂(M.q (lastPair t h)) := by
  have : IsMarkovKernel (M.q.comap (lastPair (X := X) (A := A) t) (measurable_pi_apply _)) :=
    Kernel.IsMarkovKernel.comap _ _
  unfold stepKernel
  have hF : Measurable (fun p : X × A => G p.1) := hG.comp measurable_fst
  rw [Kernel.lintegral_compProd _ _ _ hF]
  simp only [lintegral_const, measure_univ, mul_one]
  rfl

lemma state_zero (M : MDP X A) (π : Policy X A) (x : X) {G : X → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ ω, G (ω 0).1 ∂(pathMeasure M π x) = G x := by
  rw [path_zero (F := fun p : X × A => G p.1) _ _ _ (hG.comp measurable_fst)]
  unfold initMeasure
  have hF : Measurable (fun p : X × A => G p.1) := hG.comp measurable_fst
  rw [lintegral_map hF (by fun_prop)]
  simp

lemma state_succ (M : MDP X A) (π : Policy X A) (x : X) (t : ℕ) {G : X → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ ω, G (ω (t + 1)).1 ∂(pathMeasure M π x) =
      ∫⁻ ω, ∫⁻ y, G y ∂(M.q (ω t)) ∂(pathMeasure M π x) := by
  rw [path_succ (F := fun p : X × A => G p.1) _ _ _ _ (hG.comp measurable_fst)]
  simp_rw [step_marg _ _ _ _ hG]
  rfl

lemma vN_eq (M : MDP X A) (hc : Measurable (fun p : X × A => M.cost p.1 p.2))
    (π : Policy X A) (n : ℕ) (α : ℝ) (x : X) :
    vN M π n α x = ∑ t ∈ Finset.range n, ENNReal.ofReal (α ^ t) *
      ∫⁻ ω, M.cost (ω t).1 (ω t).2 ∂(pathMeasure M π x) := by
  unfold vN
  rw [lintegral_finsetSum]
  · congr 1; ext t
    rw [lintegral_const_mul (f := fun ω : ℕ → X × A => M.cost (ω t).1 (ω t).2) _ (hc.comp (measurable_pi_apply t))]
  · intro t _
    exact (hc.comp (measurable_pi_apply t)).const_mul _

lemma vDisc_eq (M : MDP X A) (hc : Measurable (fun p : X × A => M.cost p.1 p.2))
    (π : Policy X A) (β : ℝ) (x : X) :
    vDisc M π β x = ∑' t, ENNReal.ofReal (β ^ t) *
      ∫⁻ ω, M.cost (ω t).1 (ω t).2 ∂(pathMeasure M π x) := by
  unfold vDisc
  rw [lintegral_tsum]
  · congr 1; ext t
    rw [lintegral_const_mul (f := fun ω : ℕ → X × A => M.cost (ω t).1 (ω t).2) _ (hc.comp (measurable_pi_apply t))]
  · intro t
    exact ((hc.comp (measurable_pi_apply t)).const_mul _).aemeasurable

/-- Telescoping (≤): one-step inequalities for value-to-go functions `U m` give
`U 0 x ≤ v^π_{n,α}(x) + α^n E U_n(x_n)`. -/
lemma tel_le (M : MDP X A) (hc : Measurable (fun p : X × A => M.cost p.1 p.2))
    (π : Policy X A) (x : X) (α : ℝ) (hα : 0 ≤ α) (n : ℕ) (U : ℕ → X → ℝ≥0∞)
    (hU : ∀ m, Measurable (U m))
    (H : ∀ m < n, ∫⁻ ω, U m (ω m).1 ∂(pathMeasure M π x) ≤
      ∫⁻ ω, M.cost (ω m).1 (ω m).2 ∂(pathMeasure M π x) +
        ENNReal.ofReal α * ∫⁻ ω, U (m + 1) (ω (m + 1)).1 ∂(pathMeasure M π x)) :
    U 0 x ≤ vN M π n α x + ENNReal.ofReal (α ^ n) *
      ∫⁻ ω, U n (ω n).1 ∂(pathMeasure M π x) := by
  rw [vN_eq M hc]
  have key : ∀ m ≤ n, U 0 x ≤ ∑ t ∈ Finset.range m, ENNReal.ofReal (α ^ t) *
      ∫⁻ ω, M.cost (ω t).1 (ω t).2 ∂(pathMeasure M π x) + ENNReal.ofReal (α ^ m) *
      ∫⁻ ω, U m (ω m).1 ∂(pathMeasure M π x) := by
    intro m
    induction m with
    | zero => intro _; simp [state_zero M π x (hU 0)]
    | succ m ih =>
      intro hm
      refine (ih (by omega)).trans ?_
      rw [Finset.sum_range_succ, add_assoc]
      gcongr
      rw [pow_succ, ENNReal.ofReal_mul (pow_nonneg hα _), mul_assoc, ← mul_add]
      gcongr
      exact H m (by omega)
  exact key n le_rfl

/-- Telescoping (≥). -/
lemma tel_ge (M : MDP X A) (hc : Measurable (fun p : X × A => M.cost p.1 p.2))
    (π : Policy X A) (x : X) (α : ℝ) (hα : 0 ≤ α) (n : ℕ) (U : ℕ → X → ℝ≥0∞)
    (hU : ∀ m, Measurable (U m))
    (H : ∀ m < n, ∫⁻ ω, M.cost (ω m).1 (ω m).2 ∂(pathMeasure M π x) +
        ENNReal.ofReal α * ∫⁻ ω, U (m + 1) (ω (m + 1)).1 ∂(pathMeasure M π x) ≤
        ∫⁻ ω, U m (ω m).1 ∂(pathMeasure M π x)) :
    vN M π n α x + ENNReal.ofReal (α ^ n) *
      ∫⁻ ω, U n (ω n).1 ∂(pathMeasure M π x) ≤ U 0 x := by
  rw [vN_eq M hc]
  have key : ∀ m ≤ n, ∑ t ∈ Finset.range m, ENNReal.ofReal (α ^ t) *
      ∫⁻ ω, M.cost (ω t).1 (ω t).2 ∂(pathMeasure M π x) + ENNReal.ofReal (α ^ m) *
      ∫⁻ ω, U m (ω m).1 ∂(pathMeasure M π x) ≤ U 0 x := by
    intro m
    induction m with
    | zero => intro _; simp [state_zero M π x (hU 0)]
    | succ m ih =>
      intro hm
      refine le_trans ?_ (ih (by omega))
      rw [Finset.sum_range_succ, add_assoc]
      gcongr
      rw [pow_succ, ENNReal.ofReal_mul (pow_nonneg hα _), mul_assoc, ← mul_add]
      gcongr
      exact H m (by omega)
  exact key n le_rfl

/-- Under an admissible policy, `a_t ∈ A(x_t)` almost surely. -/
lemma adm_ae (M : Model X A) (π : Policy X A) (hπ : Admissible M π) (x : X) (t : ℕ) :
    ∀ᵐ ω ∂(pathMeasure M.toMDP π x), (ω t).2 ∈ M.Aset (ω t).1 := by
  set B : Set (X × A) := {p | p.2 ∈ M.Aset p.1}ᶜ with hB
  have hBm : MeasurableSet B := M.graph_meas.compl
  have hsec : ∀ y : X, MeasurableSet (M.Aset y) := fun y =>
    M.graph_meas.preimage (measurable_prodMk_left (x := y))
  have hzero : ∫⁻ ω, B.indicator 1 (ω t) ∂(pathMeasure M.toMDP π x) = 0 := by
    have hF : Measurable (B.indicator (1 : X × A → ℝ≥0∞)) := measurable_one.indicator hBm
    cases t with
    | zero =>
      rw [path_zero _ _ _ hF, lintegral_indicator_one hBm]
      unfold initMeasure
      rw [Measure.map_apply (by fun_prop) hBm]
      have : (fun a => (x, a)) ⁻¹' B = (M.Aset x)ᶜ := by ext a; simp [hB]
      rw [this]
      exact hπ 0 (fun j => j.elim0, x)
    | succ t =>
      rw [path_succ _ _ _ _ hF]
      refine (lintegral_congr fun ω => ?_).trans (lintegral_zero)
      rw [lintegral_indicator_one hBm]
      have : IsMarkovKernel (M.toMDP.q.comap (lastPair (X := X) (A := A) t)
        (measurable_pi_apply _)) := Kernel.IsMarkovKernel.comap _ _
      unfold stepKernel
      rw [Kernel.compProd_apply hBm]
      refine (lintegral_congr fun y => ?_).trans lintegral_zero
      rw [Kernel.comap_apply]
      have : Prod.mk y ⁻¹' B = (M.Aset y)ᶜ := by ext a; simp [hB]
      rw [this]
      exact hπ (t + 1) _
  have hm : Measurable (fun ω : ℕ → X × A => B.indicator (1 : X × A → ℝ≥0∞) (ω t)) :=
    (measurable_one.indicator hBm).comp (measurable_pi_apply t)
  have := (lintegral_eq_zero_iff hm).1 hzero
  filter_upwards [this] with ω hω
  by_contra hc
  have : ω t ∈ B := hc
  simp [Set.indicator_of_mem this] at hω

lemma markov_adm (M : Model X A) (fs : ℕ → X → A) (hfs : ∀ t, IsStationary M (fs t)) :
    Admissible M (markovPolicy fs (fun t => (hfs t).1)) := by
  intro t h
  have hm : MeasurableSet (M.Aset h.2) :=
    M.graph_meas.preimage (measurable_prodMk_left (x := h.2))
  simp only [markovPolicy]
  rw [Kernel.deterministic_apply' _ _ hm.compl]
  simp [(hfs t).2 h.2]

lemma statPolicy_adm (M : Model X A) (φ : X → A) (hφ : IsStationary M φ) :
    Admissible M (statPolicy hφ) := by
  intro t h
  have hm : MeasurableSet (M.Aset h.2) :=
    M.graph_meas.preimage (measurable_prodMk_left (x := h.2))
  have hφm : Measurable φ := hφ.1
  show (Policy.ofStationary φ hφm).rule t h (M.Aset h.2)ᶜ = 0
  simp only [Policy.ofStationary]
  rw [Kernel.deterministic_apply' _ _ hm.compl]
  simp [hφ.2 h.2]

lemma statPolicy_eq (M : Model X A) (φ : X → A) (hφ : IsStationary M φ) :
    statPolicy hφ = markovPolicy (fun _ => φ) (fun _ => hφ.1) := rfl

/-! ### Dynamic programming operators -/

/-- The Bellman operator `T u (x) = inf_{a ∈ A(x)} η^α_u(x, a)`. -/
noncomputable def Top (M : Model X A) (α : ℝ) (u : X → ℝ≥0∞) : X → ℝ≥0∞ :=
  fun x => ⨅ a ∈ M.Aset x, eta M u α x a

/-- Value iteration `W 0 = 0`, `W (n+1) = T (W n)`. -/
noncomputable def W (M : Model X A) (α : ℝ) : ℕ → X → ℝ≥0∞
  | 0 => 0
  | n + 1 => Top M α (W M α n)

lemma eta_mono (M : Model X A) (α : ℝ) {u v : X → ℝ≥0∞} (h : u ≤ v) (x : X) (a : A) :
    eta M u α x a ≤ eta M v α x a := by
  unfold eta; gcongr; exact h _

lemma Top_mono (M : Model X A) (α : ℝ) {u v : X → ℝ≥0∞} (h : u ≤ v) : Top M α u ≤ Top M α v :=
  fun x => iInf₂_mono fun a _ => eta_mono M α h x a

lemma Top_le (M : Model X A) (α : ℝ) (u : X → ℝ≥0∞) (x : X) (a : A) (ha : a ∈ M.Aset x) :
    Top M α u x ≤ eta M u α x a := biInf_le (fun a => eta M u α x a) ha

lemma W_mono_succ (M : Model X A) (α : ℝ) : ∀ n, W M α n ≤ W M α (n + 1)
  | 0 => fun _ => zero_le
  | n + 1 => Top_mono M α (W_mono_succ M α n)

lemma W_mono (M : Model X A) (α : ℝ) : Monotone (W M α) :=
  monotone_nat_of_le_succ (W_mono_succ M α)

lemma eta_scale (M : Model X A) (α : ℝ) {u : X → ℝ≥0∞} (hu : Measurable u) (x : X) (a : A) :
    eta M u α x a = eta M (fun y => ENNReal.ofReal α * u y) 1 x a := by
  simp only [eta, ENNReal.ofReal_one, one_mul]
  rw [lintegral_const_mul _ hu]

/-- D1: every admissible policy costs at least `W n` over `n` stages. -/
lemma W_le_vN (M : Model X A) (α : ℝ) (hα : 0 ≤ α) (hWm : ∀ n, Measurable (W M α n))
    (π : Policy X A) (hπ : Admissible M π) (x : X) (n : ℕ) :
    W M α n x ≤ vN M.toMDP π n α x := by
  have hc := M.cost_meas
  have h := tel_le M.toMDP hc π x α hα n (fun m => W M α (n - m)) (fun m => hWm _) ?_
  · simpa [W] using h
  intro m hm
  obtain ⟨k, hk⟩ : ∃ k, n - m = k + 1 := ⟨n - m - 1, by omega⟩
  have hk' : n - (m + 1) = k := by omega
  simp only [hk, hk']
  have hI : Measurable (fun ω : ℕ → X × A => ∫⁻ y, W M α k y ∂(M.toMDP.q (ω m))) :=
    (hWm k).lintegral_kernel.comp (measurable_pi_apply m)
  have hcm : Measurable (fun ω : ℕ → X × A => M.toMDP.cost (ω m).1 (ω m).2) :=
    hc.comp (measurable_pi_apply m)
  rw [state_succ M.toMDP π x m (hWm k), ← lintegral_const_mul (ENNReal.ofReal α) hI,
    ← lintegral_add_left hcm]
  refine lintegral_mono_ae ?_
  filter_upwards [adm_ae M π hπ x m] with ω hω
  exact Top_le M α (W M α k) _ _ hω

end FKZT2

namespace FKZT2

open FeinbergLiang.ACOE

section Topo

variable {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]

lemma lsc_scale (α : ℝ) {u : X → ℝ≥0∞} (hu : LowerSemicontinuous u) :
    LowerSemicontinuous (fun y => ENNReal.ofReal α * u y) :=
  Continuous.comp_lowerSemicontinuous (g := fun t => ENNReal.ofReal α * t)
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top) hu
    (fun _ _ h => mul_le_mul_right h _)

lemma Top_eq_uStar (M : Model X A) (α : ℝ) {u : X → ℝ≥0∞} (hu : Measurable u) :
    Top M α u = uStar M (fun y => ENNReal.ofReal α * u y) := by
  funext x
  simp only [Top, uStar, eta_scale M α hu]

lemma Top_lsc (M : Model X A) (hsel : HasSelector M) (hW : CondWStar M) (α : ℝ)
    {u : X → ℝ≥0∞} (hu : LowerSemicontinuous u) : LowerSemicontinuous (Top M α u) := by
  rw [Top_eq_uStar M α hu.measurable]
  exact (fkz3_lemma3 M hsel hW _ (lsc_scale α hu)).1

lemma Top_selector (M : Model X A) (hsel : HasSelector M) (hW : CondWStar M) (α : ℝ)
    {u : X → ℝ≥0∞} (hu : LowerSemicontinuous u) :
    ∃ f : X → A, IsStationary M f ∧ ∀ x, Top M α u x = eta M u α x (f x) := by
  obtain ⟨f, hf, hfe⟩ := (fkz3_lemma3 M hsel hW _ (lsc_scale α hu)).2.1
  refine ⟨f, hf, fun x => ?_⟩
  rw [Top_eq_uStar M α hu.measurable, hfe x, eta_scale M α hu.measurable]

lemma W_lsc (M : Model X A) (hsel : HasSelector M) (hW : CondWStar M) (α : ℝ) :
    ∀ n, LowerSemicontinuous (W M α n)
  | 0 => lowerSemicontinuous_const
  | n + 1 => Top_lsc M hsel hW α (W_lsc M hsel hW α n)

/-- D2: a Markov policy built from minimizing selectors attains `W n`. -/
lemma vNOpt_eq (M : Model X A) (hsel : HasSelector M) (hW : CondWStar M) (α : ℝ) (hα : 0 ≤ α)
    (n : ℕ) (x : X) : vNOpt M n α x = W M α n x := by
  have hWm : ∀ k, Measurable (W M α k) := fun k => (W_lsc M hsel hW α k).measurable
  refine le_antisymm ?_ (le_iInf fun π => W_le_vN M α hα hWm π.1 π.2 x n)
  choose f hf hfe using fun k => Top_selector M hsel hW α (W_lsc M hsel hW α k)
  set fs : ℕ → X → A := fun t => f (n - 1 - t)
  have hfs : ∀ t, IsStationary M (fs t) := fun t => hf _
  set π := markovPolicy fs (fun t => (hfs t).1)
  refine (iInf_le (fun π : {π : Policy X A // Admissible M π} => vN M.toMDP π.1 n α x)
    ⟨π, markov_adm M fs hfs⟩).trans ?_
  have hc := M.cost_meas
  have h := tel_ge M.toMDP hc π x α hα n (fun m => W M α (n - m)) (fun m => hWm _) ?_
  · exact le_trans le_self_add h
  intro m hm
  obtain ⟨k, hk⟩ : ∃ k, n - m = k + 1 := ⟨n - m - 1, by omega⟩
  have hk' : n - (m + 1) = k := by omega
  have hfk : fs m = f k := by simp only [fs]; congr 1; omega
  simp only [hk, hk']
  have hI : Measurable (fun ω : ℕ → X × A => ∫⁻ y, W M α k y ∂(M.toMDP.q (ω m))) :=
    (hWm k).lintegral_kernel.comp (measurable_pi_apply m)
  have hcm : Measurable (fun ω : ℕ → X × A => M.toMDP.cost (ω m).1 (ω m).2) :=
    hc.comp (measurable_pi_apply m)
  rw [state_succ M.toMDP π x m (hWm k), ← lintegral_const_mul (ENNReal.ofReal α) hI,
    ← lintegral_add_left hcm]
  have hF : Measurable (fun p : X × A => M.toMDP.cost p.1 p.2 +
      ENNReal.ofReal α * ∫⁻ y, W M α k y ∂(M.toMDP.q p)) :=
    hc.add ((hWm k).lintegral_kernel.const_mul _)
  have := law_markov M.toMDP fs (fun t => (hfs t).1) x m hF
  simp only at this
  rw [this]
  refine le_of_eq (lintegral_congr fun ω => ?_)
  show eta M (W M α k) α (ω m).1 (fs m (ω m).1) = Top M α (W M α k) (ω m).1
  rw [hfk, hfe k]

/-- `V = sup_n W n`, the limit of value iteration. -/
noncomputable def V (M : Model X A) (α : ℝ) : X → ℝ≥0∞ := fun x => ⨆ n, W M α n x

lemma V_lsc (M : Model X A) (hsel : HasSelector M) (hW : CondWStar M) (α : ℝ) :
    LowerSemicontinuous (V M α) :=
  lowerSemicontinuous_iSup fun n => W_lsc M hsel hW α n

lemma W_le_V (M : Model X A) (α : ℝ) (n : ℕ) : W M α n ≤ V M α := fun x =>
  le_iSup (fun n => W M α n x) n

lemma V_le_TopV (M : Model X A) (α : ℝ) : V M α ≤ Top M α (V M α) := by
  intro x
  refine iSup_le fun n => ?_
  cases n with
  | zero => exact zero_le
  | succ n => exact Top_mono M α (W_le_V M α n) x

lemma eta_V (M : Model X A) (hsel : HasSelector M) (hW : CondWStar M) (α : ℝ) (x : X) (a : A) :
    eta M (V M α) α x a = ⨆ n, eta M (W M α n) α x a := by
  unfold eta V
  rw [lintegral_iSup (fun n => (W_lsc M hsel hW α n).measurable)
    (fun i j h y => W_mono M α h y), ENNReal.mul_iSup, ENNReal.add_iSup]

lemma TopV_le_V (M : Model X A) (hsel : HasSelector M) (hW : CondWStar M) (α : ℝ)
    (hα : 0 ≤ α) : Top M α (V M α) ≤ V M α := by
  intro x
  by_cases hx : V M α x = ⊤
  · rw [hx]; exact le_top
  have hWm : ∀ k, Measurable (W M α k) := fun k => (W_lsc M hsel hW α k).measurable
  choose f hf hfe using fun k => Top_selector M hsel hW α (W_lsc M hsel hW α k)
  set as : ℕ → A := fun n => f n x
  have has : ∀ n, as n ∈ M.Aset x := fun n => (hf n).2 x
  have hb : ∀ n, eta M (W M α n) α x (as n) ≤ V M α x := fun n => by
    rw [← hfe n x]; exact W_le_V M α (n + 1) x
  have hcb : ∀ n, M.toMDP.cost x (as n) ≤ ((V M α x).toNNReal : ℝ≥0∞) := fun n => by
    rw [ENNReal.coe_toNNReal hx]
    exact le_trans (by unfold eta; exact le_self_add) (hb n)
  obtain ⟨a, haA, hcl⟩ := hW.2.1 (fun _ => x) x as tendsto_const_nhds has ⟨_, hcb⟩
  obtain ⟨ψ, hψ, hlim⟩ := hcl.tendsto_subseq
  have hm : ∀ m, eta M (W M α m) α x a ≤ V M α x := by
    intro m
    have hl := fkz3_eta_lsc M hW (fun y => ENNReal.ofReal α * W M α m y)
      (lsc_scale α (W_lsc M hsel hW α m)) (fun _ => x) x (as ∘ ψ) a tendsto_const_nhds hlim
      (fun k => has _) haA
    simp only [← eta_scale M α (hWm m)] at hl
    refine hl.trans (liminf_le_of_frequently_le' ?_)
    refine Eventually.frequently ?_
    filter_upwards [eventually_ge_atTop m] with k hk
    have hk' : m ≤ ψ k := hk.trans (hψ.id_le k)
    exact (eta_mono M α (W_mono M α hk') x _).trans (hb (ψ k))
  calc Top M α (V M α) x ≤ eta M (V M α) α x a := Top_le M α _ x a haA
    _ = ⨆ m, eta M (W M α m) α x a := eta_V M hsel hW α x a
    _ ≤ V M α x := iSup_le hm

lemma V_fixed (M : Model X A) (hsel : HasSelector M) (hW : CondWStar M) (α : ℝ)
    (hα : 0 ≤ α) : Top M α (V M α) = V M α :=
  le_antisymm (TopV_le_V M hsel hW α hα) (V_le_TopV M α)

end Topo

section Stat

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-- The transition operator of a stationary policy: `Q g (y) = ∫ g dq(· | y, φ y)`. -/
noncomputable def Qop (M : Model X A) (φ : X → A) (g : X → ℝ≥0∞) : X → ℝ≥0∞ :=
  fun y => ∫⁻ z, g z ∂(M.toMDP.q (y, φ y))

lemma Qop_meas (M : Model X A) {φ : X → A} (hφ : Measurable φ) {g : X → ℝ≥0∞}
    (hg : Measurable g) : Measurable (Qop M φ g) :=
  hg.lintegral_kernel.comp (measurable_id.prodMk hφ)

lemma Qit_meas (M : Model X A) {φ : X → A} (hφ : Measurable φ) :
    ∀ (t : ℕ) {g : X → ℝ≥0∞}, Measurable g → Measurable ((Qop M φ)^[t] g)
  | 0, _, hg => hg
  | t + 1, _, hg => by
    rw [Function.iterate_succ_apply]; exact Qit_meas M hφ t (Qop_meas M hφ hg)

lemma Qop_mono (M : Model X A) (φ : X → A) {f g : X → ℝ≥0∞} (h : f ≤ g) :
    Qop M φ f ≤ Qop M φ g := fun y => lintegral_mono fun z => h z

lemma Qit_mono (M : Model X A) (φ : X → A) :
    ∀ (t : ℕ) {f g : X → ℝ≥0∞}, f ≤ g → (Qop M φ)^[t] f ≤ (Qop M φ)^[t] g
  | 0, _, _, h => h
  | t + 1, _, _, h => by
    simp only [Function.iterate_succ_apply]; exact Qit_mono M φ t (Qop_mono M φ h)

lemma Qop_add (M : Model X A) (φ : X → A) {f g : X → ℝ≥0∞} (hf : Measurable f) :
    Qop M φ (fun y => f y + g y) = fun y => Qop M φ f y + Qop M φ g y := by
  funext y; unfold Qop; rw [lintegral_add_left hf]

lemma Qop_const_mul (M : Model X A) (φ : X → A) (r : ℝ≥0∞) {f : X → ℝ≥0∞}
    (hf : Measurable f) : Qop M φ (fun y => r * f y) = fun y => r * Qop M φ f y := by
  funext y; unfold Qop; rw [lintegral_const_mul _ hf]

lemma Qit_add (M : Model X A) {φ : X → A} (hφ : Measurable φ) :
    ∀ (t : ℕ) {f g : X → ℝ≥0∞}, Measurable f → Measurable g →
      (Qop M φ)^[t] (fun y => f y + g y) = fun y => (Qop M φ)^[t] f y + (Qop M φ)^[t] g y
  | 0, _, _, _, _ => rfl
  | t + 1, f, g, hf, hg => by
    simp only [Function.iterate_succ_apply]
    rw [Qop_add M φ hf]
    exact Qit_add M hφ t (Qop_meas M hφ hf) (Qop_meas M hφ hg)

lemma Qit_const_mul (M : Model X A) {φ : X → A} (hφ : Measurable φ) (r : ℝ≥0∞) :
    ∀ (t : ℕ) {f : X → ℝ≥0∞}, Measurable f →
      (Qop M φ)^[t] (fun y => r * f y) = fun y => r * (Qop M φ)^[t] f y
  | 0, _, _ => rfl
  | t + 1, f, hf => by
    simp only [Function.iterate_succ_apply]
    rw [Qop_const_mul M φ r hf]
    exact Qit_const_mul M hφ r t (Qop_meas M hφ hf)

lemma law_state_stat (M : Model X A) (φ : X → A) (hφ : IsStationary M φ) (x : X) :
    ∀ (t : ℕ) {g : X → ℝ≥0∞}, Measurable g →
      ∫⁻ ω, g (ω t).1 ∂(pathMeasure M.toMDP (statPolicy hφ) x) = (Qop M φ)^[t] g x
  | 0, g, hg => state_zero M.toMDP _ x hg
  | t + 1, g, hg => by
    rw [state_succ M.toMDP _ x t hg, Function.iterate_succ_apply,
      ← law_state_stat M φ hφ x t (Qop_meas M hφ.1 hg)]
    rw [statPolicy_eq]
    have hF : Measurable (fun p : X × A => ∫⁻ y, g y ∂(M.toMDP.q p)) := hg.lintegral_kernel
    rw [law_markov M.toMDP (fun _ => φ) (fun _ => hφ.1) x t hF]
    rfl

/-- The cost of a stationary policy: `cφ(y) = c(y, φ y)`. -/
noncomputable def cφ (M : Model X A) (φ : X → A) : X → ℝ≥0∞ := fun y => M.toMDP.cost y (φ y)

lemma cφ_meas (M : Model X A) {φ : X → A} (hφ : Measurable φ) : Measurable (cφ M φ) :=
  M.cost_meas.comp (measurable_id.prodMk hφ)

lemma cost_stat (M : Model X A) (φ : X → A) (hφ : IsStationary M φ) (x : X) (t : ℕ) :
    ∫⁻ ω, M.toMDP.cost (ω t).1 (ω t).2 ∂(pathMeasure M.toMDP (statPolicy hφ) x) =
      (Qop M φ)^[t] (cφ M φ) x := by
  rw [← law_state_stat M φ hφ x t (cφ_meas M hφ.1), statPolicy_eq,
    law_markov M.toMDP (fun _ => φ) (fun _ => hφ.1) x t M.cost_meas]
  rfl

lemma Jstat_eq (M : Model X A) (φ : X → A) (hφ : IsStationary M φ) (α : ℝ) (x : X) :
    vDisc M.toMDP (statPolicy hφ) α x =
      ∑' t, ENNReal.ofReal (α ^ t) * (Qop M φ)^[t] (cφ M φ) x := by
  rw [vDisc_eq M.toMDP M.cost_meas]
  simp_rw [cost_stat M φ hφ x]

/-- A stationary policy whose one-step cost is dominated by `U` costs at most `U`. -/
lemma Jstat_le (M : Model X A) (φ : X → A) (hφ : IsStationary M φ) (α : ℝ) (hα : 0 ≤ α)
    (U : X → ℝ≥0∞) (hU : Measurable U)
    (h : ∀ y, cφ M φ y + ENNReal.ofReal α * Qop M φ U y ≤ U y) (x : X) :
    vDisc M.toMDP (statPolicy hφ) α x ≤ U x := by
  rw [Jstat_eq M φ hφ α x]
  have hc := cφ_meas M hφ.1
  have key : ∀ N : ℕ, (∑ t ∈ Finset.range N, ENNReal.ofReal (α ^ t) * (Qop M φ)^[t] (cφ M φ) x)
      + ENNReal.ofReal (α ^ N) * (Qop M φ)^[N] U x ≤ U x := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      refine le_trans ?_ ih
      rw [Finset.sum_range_succ, add_assoc]
      gcongr
      have hstep : (Qop M φ)^[N] (fun y => cφ M φ y + ENNReal.ofReal α * Qop M φ U y) x ≤
          (Qop M φ)^[N] U x := Qit_mono M φ N h x
      rw [Qit_add M hφ.1 N hc ((Qop_meas M hφ.1 hU).const_mul _),
        Qit_const_mul M hφ.1 _ N (Qop_meas M hφ.1 hU)] at hstep
      rw [pow_succ, ENNReal.ofReal_mul (pow_nonneg hα _), mul_assoc, ← mul_add,
        Function.iterate_succ_apply]
      gcongr
  exact ENNReal.tsum_le_of_sum_range_le fun N => le_trans le_self_add (key N)

/-- The one-step identity `J_φ = cφ + α Q J_φ`. -/
lemma Jstat_fixed (M : Model X A) (φ : X → A) (hφ : IsStationary M φ) (α : ℝ) (hα : 0 ≤ α)
    (x : X) :
    vDisc M.toMDP (statPolicy hφ) α x = cφ M φ x +
      ENNReal.ofReal α * Qop M φ (fun y => vDisc M.toMDP (statPolicy hφ) α y) x := by
  have hc := cφ_meas M hφ.1
  simp_rw [Jstat_eq M φ hφ α]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [pow_zero, ENNReal.ofReal_one, one_mul, Function.iterate_zero, id]
  congr 1
  show _ = ENNReal.ofReal α * ∫⁻ z, (∑' t, ENNReal.ofReal (α ^ t) * (Qop M φ)^[t] (cφ M φ) z)
    ∂(M.toMDP.q (x, φ x))
  rw [lintegral_tsum (fun t => ((Qit_meas M hφ.1 t hc).const_mul _).aemeasurable),
    ← ENNReal.tsum_mul_left]
  congr 1; funext t
  rw [lintegral_const_mul _ (Qit_meas M hφ.1 t hc), pow_succ, ENNReal.ofReal_mul (pow_nonneg hα _),
    Function.iterate_succ_apply']
  simp only [Qop]
  ring

end Stat

end FKZT2

namespace FKZT2

open FeinbergLiang.ACOE

section Main

variable {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]

lemma W_le_vDisc (M : Model X A) (hsel : HasSelector M) (hW : CondWStar M) (α : ℝ)
    (hα : 0 ≤ α) (π : Policy X A) (hπ : Admissible M π) (x : X) (n : ℕ) :
    W M α n x ≤ vDisc M.toMDP π α x := by
  refine (W_le_vN M α hα (fun k => (W_lsc M hsel hW α k).measurable) π hπ x n).trans ?_
  unfold vN vDisc
  exact lintegral_mono fun ω => ENNReal.sum_le_tsum _

lemma V_le_vβ (M : Model X A) (hsel : HasSelector M) (hW : CondWStar M) (α : ℝ)
    (hα : 0 ≤ α) (x : X) : V M α x ≤ vβ M α x :=
  le_iInf fun π => iSup_le fun n => W_le_vDisc M hsel hW α hα π.1 π.2 x n

/-- A stationary policy that is greedy for `V` costs at most `V`. -/
lemma greedy_le (M : Model X A) (hsel : HasSelector M) (hW : CondWStar M) (α : ℝ)
    (hα : 0 ≤ α) (φ : X → A) (hφ : IsStationary M φ)
    (hg : ∀ y, V M α y = eta M (V M α) α y (φ y)) (x : X) :
    vDisc M.toMDP (statPolicy hφ) α x ≤ V M α x :=
  Jstat_le M φ hφ α hα (V M α) (V_lsc M hsel hW α).measurable
    (fun y => by rw [hg y]; rfl) x

lemma vβ_eq (M : Model X A) (hsel : HasSelector M) (hW : CondWStar M) (α : ℝ)
    (hα : 0 ≤ α) : vβ M α = V M α := by
  funext x
  obtain ⟨φ, hφ, hφe⟩ := Top_selector M hsel hW α (V_lsc M hsel hW α)
  have hg : ∀ y, V M α y = eta M (V M α) α y (φ y) := fun y => by
    rw [← hφe y, V_fixed M hsel hW α hα]
  refine le_antisymm ?_ (V_le_vβ M hsel hW α hα x)
  exact (iInf_le (fun π : {π : FeinbergLiang.ACOE.Policy X A // Admissible M π} => Jbeta M π.1 α x)
    ⟨statPolicy hφ, statPolicy_adm M φ hφ⟩).trans (greedy_le M hsel hW α hα φ hφ hg x)

lemma infCompact_of_ge_W1 (M : Model X A) (hsel : HasSelector M) (hW : CondWStar M) (α : ℝ)
    (hWu : CondWu M) (f : X → ℝ≥0∞) (hf : LowerSemicontinuous f) (hle : W M α 1 ≤ f) :
    InfCompactOn f Set.univ := by
  intro l
  have hK : IsCompact (Prod.fst '' {p : X × A | p ∈ graphA M ∧ M.toMDP.cost p.1 p.2 ≤ l}) :=
    (hWu.1 l).image continuous_fst
  refine hK.of_isClosed_subset ?_ ?_
  · have := hf.isClosed_preimage (l : ℝ≥0∞)
    convert this using 1
    ext y; simp
  · rintro y ⟨-, hy⟩
    have h1 : W M α 1 y ≤ l := (hle y).trans hy
    obtain ⟨g, hg, hge⟩ := Top_selector M hsel hW α (W_lsc M hsel hW α 0)
    refine ⟨(y, g y), ⟨(hg.2 y), ?_⟩, rfl⟩
    have : W M α 1 y = M.toMDP.cost y (g y) := by
      show Top M α (W M α 0) y = _
      rw [hge y]; simp [eta, W]
    rw [← this]; exact h1

end Main

end FKZT2

open FKZT2 in
theorem solution {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model X A) (hsel : HasSelector M)
    (hW : CondWStar M) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    -- (i)
    ((∀ n : ℕ, LowerSemicontinuous (vNOpt M n α)) ∧ LowerSemicontinuous (vβ M α) ∧
      ∀ x, Tendsto (fun n : ℕ => vNOpt M n α x) atTop (𝓝 (vβ M α x))) ∧
    -- (iv)
    ((∀ x, vβ M α x = ⨅ a ∈ M.Aset x, eta M (vβ M α) α x a) ∧
      (∀ x, (AAlpha M α x).Nonempty) ∧
      MeasurableSet {p : X × A | p.2 ∈ AAlpha M α p.1} ∧
      ∀ x, (vβ M α x = ⊤ → AAlpha M α x = M.Aset x) ∧
        (vβ M α x ≠ ⊤ → IsCompact (AAlpha M α x))) ∧
    -- (v)
    ((∃ φ : X → A, IsStationary M φ ∧ IsDiscOptimal M α φ) ∧
      ∀ φ : X → A, IsStationary M φ → (IsDiscOptimal M α φ ↔ ∀ x, φ x ∈ AAlpha M α x)) ∧
    -- (vi)
    (CondWu M → (∀ n : ℕ, 1 ≤ n → InfCompactOn (vNOpt M n α) Set.univ) ∧
      InfCompactOn (vβ M α) Set.univ) := by
  have hvN : ∀ n, vNOpt M n α = W M α n := fun n => funext (vNOpt_eq M hsel hW α hα0 n)
  have hvb : vβ M α = V M α := vβ_eq M hsel hW α hα0
  have hVm : Measurable (V M α) := (V_lsc M hsel hW α).measurable
  set sV : X → ℝ≥0∞ := fun y => ENNReal.ofReal α * V M α y
  have L3 := fkz3_lemma3 M hsel hW sV (lsc_scale α (V_lsc M hsel hW α))
  have hus : uStar M sV = V M α := by
    rw [← Top_eq_uStar M α hVm, V_fixed M hsel hW α hα0]
  have hAA : ∀ x, AAlpha M α x = AsubStar M sV x := by
    intro x; ext a
    simp only [AAlpha, AsubStar, Set.mem_ofPred_eq, hvb, hus, eta_scale M α hVm]
    rfl
  refine ⟨⟨fun n => hvN n ▸ W_lsc M hsel hW α n, hvb ▸ V_lsc M hsel hW α, fun x => ?_⟩,
    ⟨fun x => ?_, fun x => ?_, ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hvb]; simp only [hvN]
    exact tendsto_atTop_iSup fun i j h => W_mono M α h x
  · rw [hvb]; exact (congrFun (V_fixed M hsel hW α hα0) x).symm
  · rw [hAA]; exact L3.2.2.1 x
  · simp only [hAA]; exact L3.2.2.2.1
  · rw [hvb] at hx; rw [hAA]; exact (L3.2.2.2.2 x).1 (by rw [hus]; exact hx)
  · rw [hvb] at hx; rw [hAA]; exact (L3.2.2.2.2 x).2 (by rw [hus]; exact hx)
  · obtain ⟨φ, hφ, hφe⟩ := Top_selector M hsel hW α (V_lsc M hsel hW α)
    have hg : ∀ y, V M α y = eta M (V M α) α y (φ y) := fun y => by
      rw [← hφe y, V_fixed M hsel hW α hα0]
    refine ⟨φ, hφ, hφ, fun x => le_antisymm ?_ ?_⟩
    · rw [hvb]; exact greedy_le M hsel hW α hα0 φ hφ hg x
    · exact iInf_le (fun π : {π : FeinbergLiang.ACOE.Policy X A // Admissible M π} => Jbeta M π.1 α x)
        ⟨statPolicy hφ, statPolicy_adm M φ hφ⟩
  · intro φ hφ
    constructor
    · rintro ⟨hf, hJ⟩ x
      refine ⟨hφ.2 x, ?_⟩
      have hJV : (fun y => FeinbergLiang.ACOE.vDisc M.toMDP (statPolicy hf) α y) = V M α := by
        funext y; rw [← hvb]; exact hJ y
      have := Jstat_fixed M φ hf α hα0 x
      rw [hJV] at this
      rw [hvb]
      have hx := hJ x
      unfold Jbeta at hx
      rw [hx, hvb] at this
      rw [this]; rfl
    · intro hmem
      have hg : ∀ y, V M α y = eta M (V M α) α y (φ y) := fun y => by
        have := (hmem y).2; rw [hvb] at this; exact this
      refine ⟨hφ, fun x => le_antisymm ?_ ?_⟩
      · rw [hvb]; exact greedy_le M hsel hW α hα0 φ hφ hg x
      · exact iInf_le (fun π : {π : FeinbergLiang.ACOE.Policy X A // Admissible M π} => Jbeta M π.1 α x)
          ⟨statPolicy hφ, statPolicy_adm M φ hφ⟩
  · intro hWu
    refine ⟨fun n hn => ?_, ?_⟩
    · rw [hvN n]
      exact infCompact_of_ge_W1 M hsel hW α hWu _ (W_lsc M hsel hW α n) (W_mono M α hn)
    · rw [hvb]
      exact infCompact_of_ge_W1 M hsel hW α hWu _ (V_lsc M hsel hW α) (W_le_V M α 1)
