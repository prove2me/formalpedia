-- Prove2me | solution 1 for EF104Compactness__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T16:42:20.877947+00:00
-- url     : https://prove2.me/submissions/f8f35e29-dacd-4373-9443-3991aa308359

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Definitions.Def_EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1

open EnvyFreeCake104.Divide
open Filter Topology

namespace CPAux

theorem toSet_cons (I : Interval) (rest : Piece) :
    Piece.toSet (I :: rest) = I.toSet ∪ Piece.toSet rest := by
  ext x; simp [Piece.toSet]

theorem interval_measurable (I : Interval) : MeasurableSet I.toSet := by
  unfold Interval.toSet; split_ifs
  · exact measurableSet_Icc
  · exact measurableSet_Ico

theorem piece_measurable (P : Piece) : MeasurableSet P.toSet := by
  have : P.toSet = ⋃ I ∈ P, I.toSet := by ext x; simp [Piece.toSet]
  rw [this]
  exact MeasurableSet.biUnion P.finite_toSet.countable (fun I _ => interval_measurable I)

theorem ivl_empty (b : ℝ) : Interval.toSet ⟨b, b⟩ = ∅ := by
  simp [Interval.toSet]

theorem ivl_mono {x x' b : ℝ} (h : x' ≤ x) :
    Interval.toSet ⟨x, b⟩ ⊆ Interval.toSet ⟨x', b⟩ := by
  intro y hy
  simp only [Interval.toSet] at hy ⊢
  split_ifs at hy with h1 <;> split_ifs with h2
  · exact ⟨le_trans h hy.1, hy.2⟩
  · exact absurd ⟨h1.1, lt_of_le_of_lt h h1.2⟩ h2
  · exact ⟨le_trans h hy.1, hy.2.le⟩
  · exact ⟨le_trans h hy.1, hy.2⟩

theorem value_mono (v : Valuation) {A B : Set ℝ} (h : A ⊆ B) (hB : MeasurableSet B) :
    v.value A ≤ v.value B := by
  unfold Valuation.value
  apply MeasureTheory.setIntegral_mono_set (v.integrable.mono_set Set.inter_subset_right)
  · exact MeasureTheory.ae_restrict_of_forall_mem (hB.inter measurableSet_Icc)
      (fun x hx => v.nonneg x hx.2)
  · exact (Set.inter_subset_inter_left _ h).eventuallyLE

theorem value_union (v : Valuation) {A B : Set ℝ} (hB : MeasurableSet B) (hd : Disjoint A B) :
    v.value (A ∪ B) = v.value A + v.value B := by
  unfold Valuation.value
  rw [Set.union_inter_distrib_right]
  apply MeasureTheory.setIntegral_union
  · exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left hd
  · exact hB.inter measurableSet_Icc
  · exact v.integrable.mono_set Set.inter_subset_right
  · exact v.integrable.mono_set Set.inter_subset_right

theorem value_empty (v : Valuation) : v.value ∅ = 0 := by simp [Valuation.value]

/-- The value of `[x, b)` (or `[x, b]`) as an interval integral of the truncated density. -/
theorem value_ivl (v : Valuation) {x b : ℝ} (hxb : x ≤ b) :
    v.value (Interval.toSet ⟨x, b⟩) =
      ∫ y in x..b, (Set.Icc (0 : ℝ) 1).indicator v.density y := by
  rw [intervalIntegral.integral_of_le hxb]
  unfold Valuation.value
  rw [← MeasureTheory.setIntegral_indicator measurableSet_Icc]
  simp only [Interval.toSet]
  split_ifs
  · exact MeasureTheory.integral_Icc_eq_integral_Ioc
  · exact MeasureTheory.integral_Ico_eq_integral_Ioc

theorem guess_facts {ι : Type} [DecidableEq ι] (N : Finset ι) (g : List ι × List ι)
    (hg : g ∈ guesses N) :
    g.1.Nodup ∧ (∀ q ∈ g.1.zip g.2, q.1 ∈ N ∧ q.2 ∈ N) ∧
      ∀ i ∈ N, ∃ q ∈ g.1.zip g.2, q.1 = i := by
  obtain ⟨l1, l2⟩ := g
  unfold guesses at hg
  rw [List.pair_mem_product, List.mem_permutations, List.mem_permutations] at hg
  obtain ⟨h1, h2⟩ := hg
  refine ⟨h1.nodup_iff.mpr (Finset.nodup_toList N), fun q hq => ?_, fun i hi => ?_⟩
  · have := List.of_mem_zip hq
    exact ⟨by rw [← Finset.mem_toList, ← h1.mem_iff]; exact this.1,
      by rw [← Finset.mem_toList, ← h2.mem_iff]; exact this.2⟩
  · have hi1 : i ∈ l1 := by rw [h1.mem_iff, Finset.mem_toList]; exact hi
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi1
    have hk2 : k < l2.length := by rw [h2.length_eq, ← h1.length_eq]; exact hk
    have hkz : k < (l1.zip l2).length := by simp [List.length_zip]; omega
    exact ⟨(l1.zip l2)[k], List.getElem_mem hkz, by simp [List.getElem_zip]⟩


theorem suffix_measurable {X : Set ℝ} {Q : Piece} (h : IsSuffix X Q) : MeasurableSet X := by
  rcases h with rfl | ⟨p, -, rfl⟩
  · exact MeasurableSet.empty
  · exact piece_measurable _

/-- Value of the suffix after a valid position, as a function of the cut point. -/
theorem suffix_value (Q : Piece) (hQ : Q.WF) (k : ℕ) (x : ℝ) (hp : Q.ValidPos (k, x))
    (v : Valuation) :
    v.value (suffixList Q (k, x)).toSet =
      (∫ y in x..(Q.getD k default).b, (Set.Icc (0 : ℝ) 1).indicator v.density y) +
        v.value (Piece.toSet (Q.drop (k + 1))) := by
  obtain ⟨hk, hxa, hxb⟩ := hp
  simp only at hk hxa hxb
  have hsl : suffixList Q (k, x) = ⟨x, (Q.getD k default).b⟩ :: Q.drop (k + 1) := by
    simp [suffixList, hk]
  have hget : Q.getD k default = Q[k] := by simp [List.getD_eq_getElem?_getD, hk]
  have hdisj : Disjoint (Interval.toSet ⟨x, (Q.getD k default).b⟩) (Piece.toSet (Q.drop (k + 1))) := by
    have hsub : Interval.toSet ⟨x, (Q.getD k default).b⟩ ⊆ (Q.getD k default).toSet := by
      have := ivl_mono (b := (Q.getD k default).b) hxa
      simpa using this
    apply Disjoint.mono_left hsub
    rw [Set.disjoint_left]
    intro y hy hy'
    obtain ⟨J, hJ, hyJ⟩ := hy'
    obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp hJ
    have := (List.pairwise_iff_getElem.mp hQ.2) k (k + 1 + j) hk (by omega) (by omega)
    rw [hget] at hy
    exact Set.disjoint_left.mp this hy hyJ
  rw [hsl, toSet_cons, value_union v (piece_measurable _) hdisj, value_ivl v hxb]

/-- Sequential compactness of the suffixes of a piece, in the values of all valuations. -/
theorem seq_compact (Q : Piece) (hQ : Q.WF) (S : ℕ → Set ℝ) (hS : ∀ n, IsSuffix (S n) Q) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ T : Set ℝ, IsSuffix T Q ∧
      ∀ v : Valuation, Tendsto (fun n => v.value (S (φ n))) atTop (𝓝 (v.value T)) := by
  classical
  by_cases hfreq : ∃ᶠ n in atTop, S n = ∅
  · obtain ⟨φ, hφ, hφS⟩ := extraction_of_frequently_atTop hfreq
    refine ⟨φ, hφ, ∅, Or.inl rfl, fun v => ?_⟩
    simp only [hφS]; exact tendsto_const_nhds
  rw [not_frequently] at hfreq
  have hpos : ∀ n, S n ≠ ∅ → ∃ p : Pos, Q.ValidPos p ∧ S n = (suffixList Q p).toSet :=
    fun n hn => (hS n).resolve_left hn
  let p : ℕ → Pos := fun n => if h : S n ≠ ∅ then Classical.choose (hpos n h) else (0, 0)
  have hp : ∀ n, S n ≠ ∅ → Q.ValidPos (p n) ∧ S n = (suffixList Q (p n)).toSet := by
    intro n hn; simp only [p, dif_pos hn]; exact Classical.choose_spec (hpos n hn)
  have hk : ∃ k < Q.length, ∃ᶠ n in atTop, S n ≠ ∅ ∧ (p n).1 = k := by
    by_contra hcon
    have h1 : ∀ᶠ n in atTop, ∀ k ∈ Finset.range Q.length, ¬ (S n ≠ ∅ ∧ (p n).1 = k) := by
      rw [eventually_all_finset]
      intro k hk
      have := fun h => hcon ⟨k, Finset.mem_range.mp hk, h⟩
      exact not_frequently.mp this
    obtain ⟨n, hn1, hn2⟩ := (h1.and hfreq).exists
    exact hn1 (p n).1 (Finset.mem_range.mpr (hp n hn2).1.1) ⟨hn2, rfl⟩
  obtain ⟨k, hkl, hfr⟩ := hk
  obtain ⟨φ1, hφ1, hφ1P⟩ := extraction_of_frequently_atTop hfr
  set a := (Q.getD k default).a
  set b := (Q.getD k default).b
  let x : ℕ → ℝ := fun n => (p (φ1 n)).2
  have hpk : ∀ n, p (φ1 n) = (k, x n) := fun n => Prod.ext (hφ1P n).2 rfl
  have hval : ∀ n, Q.ValidPos (k, x n) := fun n => by rw [← hpk]; exact (hp _ (hφ1P n).1).1
  have hx : ∀ n, x n ∈ Set.Icc a b := fun n => ⟨(hval n).2.1, (hval n).2.2⟩
  obtain ⟨xs, hxs, φ2, hφ2, htend⟩ := isCompact_Icc.tendsto_subseq hx
  refine ⟨φ1 ∘ φ2, hφ1.comp hφ2, (suffixList Q (k, xs)).toSet,
    Or.inr ⟨(k, xs), ⟨hkl, hxs.1, hxs.2⟩, rfl⟩, fun v => ?_⟩
  let F := (Set.Icc (0 : ℝ) 1).indicator v.density
  have hF : MeasureTheory.Integrable F := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]; exact v.integrable
  have hab : a ≤ b := hxs.1.trans hxs.2
  have hG : ContinuousOn (fun y => (∫ z in y..b, F z) + v.value (Piece.toSet (Q.drop (k + 1))))
      (Set.Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval_left (a := a) (b := b) hF.integrableOn
    rw [Set.uIcc_of_le hab] at this
    exact this.add continuousOn_const
  have hlim := ((hG xs hxs).tendsto).comp (tendsto_nhdsWithin_iff.mpr
    ⟨htend, Eventually.of_forall (fun n => hx (φ2 n))⟩)
  rw [suffix_value Q hQ k xs ⟨hkl, hxs.1, hxs.2⟩ v]
  refine hlim.congr (fun n => ?_)
  simp only [Function.comp]
  rw [(hp _ (hφ1P (φ2 n)).1).2, hpk, suffix_value Q hQ k _ (hval _) v]

/-- Greedy step: approximately admissible supersets of the largest admissible suffix converge to
it in value. -/
theorem greedy_limit {ι : Type} (V : ι → Valuation) (Q : Piece) (hQ : Q.WF) (C : Set ℝ)
    (hC : IsSuffix C Q) (cons : List ι) (w : ι → ℝ)
    (hmax : ∀ S, IsSuffix S Q → (∀ a ∈ cons, (V a).value S ≤ w a) → S ⊆ C)
    (S : ℕ → Set ℝ) (hS : ∀ n, IsSuffix (S n) Q) (hCS : ∀ n, C ⊆ S n)
    (ε : ι → ℕ → ℝ) (hε : ∀ a ∈ cons, Tendsto (ε a) atTop (𝓝 0))
    (hle : ∀ a ∈ cons, ∀ n, (V a).value (S n) ≤ w a + ε a n) (v : Valuation) :
    Tendsto (fun n => v.value (S n)) atTop (𝓝 (v.value C)) := by
  have hlow : ∀ n, v.value C ≤ v.value (S n) :=
    fun n => value_mono v (hCS n) (suffix_measurable (hS n))
  rw [tendsto_order]
  refine ⟨fun c hc => Eventually.of_forall (fun n => lt_of_lt_of_le hc (hlow n)), fun c hc => ?_⟩
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨φ0, hφ0, hφ0P⟩ := extraction_of_frequently_atTop hcon
  obtain ⟨φ, hφ, T, hT, hTlim⟩ := seq_compact Q hQ (S ∘ φ0) (fun n => hS _)
  have hadm : ∀ a ∈ cons, (V a).value T ≤ w a := by
    intro a ha
    have h2 : Tendsto (fun n => w a + ε a (φ0 (φ n))) atTop (𝓝 (w a + 0)) :=
      tendsto_const_nhds.add ((hε a ha).comp ((hφ0.comp hφ).tendsto_atTop))
    rw [add_zero] at h2
    exact le_of_tendsto_of_tendsto' (hTlim (V a)) h2 (fun n => hle a ha _)
  have hTC := value_mono v (hmax T hT hadm) (suffix_measurable hC)
  have hge : c ≤ v.value T :=
    ge_of_tendsto' (hTlim v) (fun n => not_lt.mp (hφ0P (φ n)))
  linarith

end CPAux

open CPAux in
theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : N.Nonempty) (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet)
    (C : (List ι × List ι) → ι → Set ℝ)
    (hC : ∀ g ∈ guesses N, EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1 V P g.1 g.2 (C g))
    (happrox : ∀ δ : ℝ, 0 < δ →
      ∃ g ∈ guesses N, ∃ X : ι → Set ℝ,
        (∀ p ∈ g.1.zip g.2, IsSuffix (X p.1) (P p.2)) ∧
        (∀ i ∈ N, C g i ⊆ X i) ∧
        (∀ i ∈ N, ∀ j ∈ N, (V i).value (X j) ≤ (V i).value (X i) + δ)) :
    ∃ g ∈ guesses N, EnvyFree V N (C g) := by
  classical
  let Good : (List ι × List ι) → ℝ → Prop := fun g δ => ∃ X : ι → Set ℝ,
    (∀ p ∈ g.1.zip g.2, IsSuffix (X p.1) (P p.2)) ∧ (∀ i ∈ N, C g i ⊆ X i) ∧
      (∀ i ∈ N, ∀ j ∈ N, (V i).value (X j) ≤ (V i).value (X i) + δ)
  -- pigeonhole: one guess has approximants for every δ
  have hpig : ∃ g ∈ guesses N, ∀ δ : ℝ, 0 < δ → Good g δ := by
    by_contra hcon
    push Not at hcon
    have hD : ∀ g, ∃ d : ℝ, 0 < d ∧ (g ∈ guesses N → ¬ Good g d) := by
      intro g
      by_cases hg : g ∈ guesses N
      · obtain ⟨d, hd, hnd⟩ := hcon g hg
        exact ⟨d, hd, fun _ => hnd⟩
      · exact ⟨1, one_pos, fun h => absurd h hg⟩
    choose D hDpos hDbad using hD
    have hne : (guesses N).toFinset.Nonempty := by
      refine ⟨(N.toList, N.toList), ?_⟩
      rw [List.mem_toFinset]
      unfold guesses
      rw [List.pair_mem_product, List.mem_permutations]
      exact ⟨List.Perm.refl _, List.Perm.refl _⟩
    set d0 := (guesses N).toFinset.inf' hne D
    have hd0 : 0 < d0 := (Finset.lt_inf'_iff hne).mpr (fun g _ => hDpos g)
    obtain ⟨g, hg, X, hX1, hX2, hX3⟩ := happrox d0 hd0
    apply hDbad g hg
    refine ⟨X, hX1, hX2, fun i hi j hj => (hX3 i hi j hj).trans ?_⟩
    have : d0 ≤ D g := Finset.inf'_le _ (List.mem_toFinset.mpr hg)
    linarith
  obtain ⟨g, hg, hgood⟩ := hpig
  refine ⟨g, hg, ?_⟩
  obtain ⟨-, hmem, hcov⟩ := guess_facts N g hg
  have hGP := hC g hg
  -- the approximating sequence
  have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose X hX1 hX2 hX3 using fun n : ℕ => hgood _ (hδ n)
  have hδlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- convergence along the guess, by strong induction on the position
  have key : ∀ m : ℕ, ∀ (before : List (ι × ι)) (p : ι × ι) (after : List (ι × ι)),
      g.1.zip g.2 = before ++ p :: after → before.length = m →
      ∀ v : Valuation, Tendsto (fun n => v.value (X n p.1)) atTop (𝓝 (v.value (C g p.1))) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro before p after hz hlen v
      have hpmem : p ∈ g.1.zip g.2 := by rw [hz]; simp
      have hp1 := (hmem p hpmem).1
      obtain ⟨hsuf, -, hmaxGP⟩ := hGP before p after hz
      -- earlier agents converge
      have hprev : ∀ q ∈ before, ∀ v : Valuation,
          Tendsto (fun n => v.value (X n q.1)) atTop (𝓝 (v.value (C g q.1))) := by
        intro q hq
        obtain ⟨b1, b2, rfl⟩ := List.append_of_mem hq
        exact ih b1.length (by simp at hlen; omega) b1 q (b2 ++ p :: after) (by rw [hz]; simp) rfl
      let ε : ι → ℕ → ℝ := fun a n =>
        1 / ((n : ℝ) + 1) + |(V a).value (X n a) - (V a).value (C g a)|
      refine greedy_limit V (P p.2) (hP p.2 (hmem p hpmem).2) (C g p.1) hsuf
        (before.map Prod.fst) (fun a => (V a).value (C g a)) ?_ (fun n => X n p.1)
        (fun n => hX1 n p hpmem) (fun n => hX2 n p.1 hp1) ε ?_ ?_ v
      · intro S hS hadm
        exact hmaxGP S hS (fun q hq => hadm q.1 (List.mem_map_of_mem hq))
      · intro a ha
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        have h1 := hprev q hq (V q.1)
        have h2 : Tendsto (fun n => |(V q.1).value (X n q.1) - (V q.1).value (C g q.1)|)
            atTop (𝓝 0) := by
          have := (h1.sub_const ((V q.1).value (C g q.1))).abs
          simpa using this
        show Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) +
          |(V q.1).value (X n q.1) - (V q.1).value (C g q.1)|) atTop (𝓝 0)
        simpa using hδlim.add h2
      · intro a ha n
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        have hq1 : q.1 ∈ N := (hmem q (by rw [hz]; simp [hq])).1
        have := hX3 n q.1 hq1 p.1 hp1
        have h3 := le_abs_self ((V q.1).value (X n q.1) - (V q.1).value (C g q.1))
        simp only [ε]
        linarith
  have hconv : ∀ i ∈ N, ∀ v : Valuation,
      Tendsto (fun n => v.value (X n i)) atTop (𝓝 (v.value (C g i))) := by
    intro i hi v
    obtain ⟨p, hp, rfl⟩ := hcov i hi
    obtain ⟨before, after, hz⟩ := List.append_of_mem hp
    exact key _ before p after hz rfl v
  have hmeas : ∀ n, ∀ j ∈ N, MeasurableSet (X n j) := by
    intro n j hj
    obtain ⟨p, hp, rfl⟩ := hcov j hj
    exact suffix_measurable (hX1 n p hp)
  intro i hi j hj
  have hlim := (hconv i hi (V i)).add hδlim
  rw [add_zero] at hlim
  refine ge_of_tendsto' hlim (fun n => ?_)
  have h1 := value_mono (V i) (hX2 n j hj) (hmeas n j hj)
  have h2 := hX3 n i hi j hj
  linarith
