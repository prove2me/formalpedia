-- Prove2me | solution 1 for FKZAvg.WStar.lemma_3_lsc
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T15:29:32.028947+00:00
-- url     : https://prove2.me/submissions/81c4190b-8e56-4507-8483-8ec7e8f1345a

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions
import Theorems.Thm_SchalAvg_AvgOpt_lemma_2_3_ii
import Theorems.Thm_FKZAvg_WStar_lemma_2_fullW

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
    ∃ a ∈ M.Aset x ∩ C, eta M u 1 x a ≤ t := by
  have hc : ∀ n, M.toMDP.cost (xs n) (as n) ≤ B := fun n =>
    le_trans (by rw [fkz3_eta_eq]; exact le_self_add) (hB n)
  obtain ⟨a, haA, hcl⟩ := hW.2.1 xs x as hx (fun n => (has n).1) ⟨B, hc⟩
  obtain ⟨ψ, hψ, hlim⟩ := hcl.tendsto_subseq
  have haC : a ∈ C := hC.mem_of_tendsto hlim (Eventually.of_forall fun k => (has (ψ k)).2)
  refine ⟨a, ⟨haA, haC⟩, ?_⟩
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
  obtain ⟨a, haS, ha⟩ := fkz3_cluster M hW u hu C hC (fun _ => x) x tendsto_const_nhds as has
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
  obtain ⟨a, haS, ha⟩ := fkz3_cluster M hW u hu C hC xs x hxs as has _ hB y
    (fun n => (hlt' n).le)
  exact absurd (lt_of_lt_of_le hy ((biInf_le _ haS).trans ha)) (lt_irrefl _)

end Core

theorem solution {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model X A) (hsel : HasSelector M)
    (hW : CondWStar M) (u : X → ℝ≥0∞) (hu : InL u) :
    LowerSemicontinuous (uStar M u) ∧
    (∃ f : X → A, IsStationary M f ∧ ∀ x, uStar M u x = eta M u 1 x (f x)) ∧
    (∀ x, (AsubStar M u x).Nonempty) ∧
    MeasurableSet {p : X × A | p.2 ∈ AsubStar M u p.1} ∧
    ∀ x, (uStar M u x = ⊤ → AsubStar M u x = M.Aset x) ∧
      (uStar M u x ≠ ⊤ → IsCompact (AsubStar M u x)) := by
  classical
  have hul : LowerSemicontinuous u := hu.1
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
    have hc := (FKZAvg.WStar.lemma_2_fullW M hsel x).2 hW u hu 1 zero_le_one
      (uStar M u x).toNNReal
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
