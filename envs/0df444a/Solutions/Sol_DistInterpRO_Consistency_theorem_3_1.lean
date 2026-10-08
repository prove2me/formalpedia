-- Prove2me | solution 1 for DistInterpRO.Consistency.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-05T07:13:28.307674+00:00
-- url     : https://prove2.me/submissions/71f62339-d633-49f6-85f6-3f4d95940007

import Mathlib
import Definitions.Def_DistInterpRO_Consistency_Model

open MeasureTheory Filter Topology ProbabilityTheory

set_option autoImplicit false


/- Inlined checked module: BoundedSampling -/
section
open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Proof

noncomputable def sampleMean {S Ω : Type*} (g : S → ℝ) (X : ℕ → Ω → S)
    (n : ℕ) (ω : Ω) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, g (X i ω)

theorem bounded_integrable {S : Type*} [MeasurableSpace S] (μ : Measure S)
    [IsFiniteMeasure μ] {g : S → ℝ} (hg : Measurable g) (C : ℝ)
    (hC : ∀ x, |g x| ≤ C) : Integrable g μ := by
  apply Integrable.of_bound hg.aestronglyMeasurable C
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hC x)

theorem sampleMean_strong_law {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure S)
    (X : ℕ → Ω → S) (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = μ) (g : S → ℝ) (hg : Measurable g)
    (C : ℝ) (hC : ∀ x, |g x| ≤ C) :
    ∀ᵐ ω ∂P, Tendsto (fun n => sampleMean g X n ω) atTop (𝓝 (∫ x, g x ∂μ)) := by
  have hint : Integrable (fun ω => g (X 0 ω)) P :=
    bounded_integrable P (hg.comp (hXm 0)) C (fun ω => hC (X 0 ω))
  have hpair : Pairwise (fun i j => (fun ω => g (X i ω)) ⟂ᵢ[P] (fun ω => g (X j ω))) := by
    intro i j hij
    exact (hind.indepFun hij).comp hg hg
  have hident (i : ℕ) : IdentDistrib (fun ω => g (X i ω)) (fun ω => g (X 0 ω)) P P := by
    have hi : IdentDistrib (X i) (X 0) P P :=
      ⟨(hXm i).aemeasurable, (hXm 0).aemeasurable, (hlaw i).trans (hlaw 0).symm⟩
    exact hi.comp hg
  have he : (∫ ω, g (X 0 ω) ∂P) = ∫ x, g x ∂μ := by
    rw [← integral_map_of_stronglyMeasurable (hXm 0) hg.stronglyMeasurable, hlaw 0]
  have h := strong_law_ae_real (fun i ω => g (X i ω)) hint hpair hident
  filter_upwards [h] with ω hω
  have hm : (fun n => sampleMean g X n ω) =
      (fun n => (∑ i ∈ Finset.range n, g (X i ω)) / (n : ℝ)) := by
    funext n
    unfold sampleMean
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => g (X i ω)) n]
    ring
  rw [hm]
  simpa only [he] using hω

theorem sampleMean_mono {S Ω : Type*} {g h : S → ℝ} (hgh : ∀ x, g x ≤ h x)
    (X : ℕ → Ω → S) (n : ℕ) (ω : Ω) : sampleMean g X n ω ≤ sampleMean h X n ω := by
  unfold sampleMean
  apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun (i : Fin n) _ => hgh (X i ω)))
  positivity

theorem sampleMean_sub {S Ω : Type*} (g h : S → ℝ) (X : ℕ → Ω → S)
    (n : ℕ) (ω : Ω) :
    sampleMean (fun x => g x - h x) X n ω = sampleMean g X n ω - sampleMean h X n ω := by
  simp only [sampleMean, Finset.sum_sub_distrib, mul_sub]

theorem sampleMean_const {S Ω : Type*} (a : ℝ) (X : ℕ → Ω → S)
    {n : ℕ} (hn : 0 < n) (ω : Ω) : sampleMean (fun _ => a) X n ω = a := by
  simp only [sampleMean, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp

end DistInterpRO.Proof
end


/- Inlined checked module: ModulusControl -/
section
open MeasureTheory Filter Topology
open DistInterpRO.Consistency

namespace DistInterpRO.Proof

variable {V : Type*} {m : ℕ} (f : V → (Fin m → ℝ) → ℝ)

theorem payoff_oscillation_bound {C : ℝ} (hfC : ∀ v x, |f v x| ≤ C)
    (v : V) (x y : Fin m → ℝ) : |f v x - f v y| ≤ 2 * C := by
  exact (abs_sub (f v x) (f v y)).trans (by linarith [hfC v x, hfC v y])

theorem modulus_bound [Nonempty V] {C ε : ℝ} (hfC : ∀ v x, |f v x| ≤ C)
    (hε : 0 ≤ ε) : modulus f ε ≤ 2 * C := by
  have : Nonempty {δ : Fin m → ℝ // ‖δ‖ ≤ ε} := ⟨⟨0, by simpa using hε⟩⟩
  apply ciSup_le
  intro v
  apply ciSup_le
  intro x
  apply ciSup_le
  intro δ
  exact payoff_oscillation_bound f hfC v x _

theorem abs_sub_le_modulus {C ε : ℝ} (hfC : ∀ v x, |f v x| ≤ C)
    (v : V) (x δ : Fin m → ℝ) (hδ : ‖δ‖ ≤ ε) :
    |f v x - f v (x + δ)| ≤ modulus f ε := by
  have : Nonempty V := ⟨v⟩
  have : Nonempty {d : Fin m → ℝ // ‖d‖ ≤ ε} := ⟨⟨δ, hδ⟩⟩
  have hb₁ (v : V) (x : Fin m → ℝ) :
      BddAbove (Set.range (fun d : {d : Fin m → ℝ // ‖d‖ ≤ ε} =>
        |f v x - f v (x + d.1)|)) :=
    ⟨2 * C, by rintro _ ⟨d, rfl⟩; exact payoff_oscillation_bound f hfC v x _⟩
  have hb₂ (v : V) : BddAbove (Set.range (fun x : Fin m → ℝ =>
      ⨆ d : {d : Fin m → ℝ // ‖d‖ ≤ ε}, |f v x - f v (x + d.1)|)) := by
    refine ⟨2 * C, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact ciSup_le fun d => payoff_oscillation_bound f hfC v x _
  have hb₃ : BddAbove (Set.range (fun v : V => ⨆ x : Fin m → ℝ,
      ⨆ d : {d : Fin m → ℝ // ‖d‖ ≤ ε}, |f v x - f v (x + d.1)|)) := by
    refine ⟨2 * C, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact ciSup_le fun x => ciSup_le fun d => payoff_oscillation_bound f hfC w x _
  exact (le_ciSup (hb₁ v x) ⟨δ, hδ⟩).trans
    ((le_ciSup (hb₂ v) x).trans (le_ciSup hb₃ v))

theorem uniformEquicontinuous_payoff {C : ℝ} (hfC : ∀ v x, |f v x| ≤ C)
    (hd : Tendsto (modulus f) (𝓝[>] 0) (𝓝 0)) : UniformEquicontinuous f := by
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  have hsmall : ∀ᶠ d in 𝓝[>] (0 : ℝ), modulus f d < ε := hd (Iio_mem_nhds hε)
  have hpos : ∀ᶠ d in 𝓝[>] (0 : ℝ), 0 < d := self_mem_nhdsWithin
  obtain ⟨d, hdpos, hdsmall⟩ := (hpos.and hsmall).exists
  refine ⟨d, hdpos, ?_⟩
  intro x y hxy v
  have hn : ‖y - x‖ ≤ d := by
    rw [← dist_eq_norm, dist_comm]
    exact hxy.le
  have hb := abs_sub_le_modulus f hfC v x (y - x) hn
  have he : x + (y - x) = y := by abel
  simpa only [he, Real.dist_eq] using hb.trans_lt hdsmall

theorem continuous_payoff {C : ℝ} (hfC : ∀ v x, |f v x| ≤ C)
    (hd : Tendsto (modulus f) (𝓝[>] 0) (𝓝 0)) (v : V) : Continuous (f v) :=
  (uniformEquicontinuous_payoff f hfC hd).uniformContinuous v |>.continuous

end DistInterpRO.Proof
end


/- Inlined checked module: CompactPayoffApproximation -/
section
open MeasureTheory Filter Topology
open DistInterpRO.Consistency
open scoped BoundedContinuousFunction

noncomputable section

namespace DistInterpRO.Proof

theorem finite_compact_payoff_approximation {V : Type*} {m : ℕ}
    (f : V → (Fin m → ℝ) → ℝ) {C : ℝ} (hfC : ∀ v x, |f v x| ≤ C)
    (hd : Tendsto (modulus f) (𝓝[>] 0) (𝓝 0))
    (K : Set (Fin m → ℝ)) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset V, ∀ v : V, ∃ w ∈ s, ∀ x ∈ K, |f v x - f w x| ≤ ε := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : V → K →ᵇ ℝ := fun v => BoundedContinuousFunction.mkOfCompact
    ⟨fun x => f v x.1, (continuous_payoff f hfC hd v).comp continuous_subtype_val⟩
  let A : Set (K →ᵇ ℝ) := Set.range F
  have hAcont : Equicontinuous ((↑) : A → K → ℝ) := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro η hη
    obtain ⟨δ, hδ, hb⟩ := Metric.uniformEquicontinuous_iff.mp
      (uniformEquicontinuous_payoff f hfC hd) η hη
    refine ⟨δ, hδ, ?_⟩
    intro y hy g
    obtain ⟨v, hv⟩ := g.property
    rw [← hv]
    change dist (f v x.1) (f v y.1) < η
    apply hb x.1 y.1 _ v
    change dist y.1 x.1 < δ at hy
    rwa [dist_comm]
  have hArange : ∀ (g : K →ᵇ ℝ) (x : K), g ∈ A → g x ∈ Set.Icc (-C) C := by
    rintro g x ⟨v, rfl⟩
    exact abs_le.mp (hfC v x.1)
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Set.Icc (-C) C) isCompact_Icc A hArange hAcont
  have htotal : TotallyBounded A := hcompact.totallyBounded.subset subset_closure
  obtain ⟨t, htsub, ht, hcover⟩ := Metric.finite_approx_of_totallyBounded htotal ε hε
  let : Fintype t := ht.fintype
  let rep : t → V := fun g => Classical.choose (htsub g.property)
  have hrep (g : t) : F (rep g) = g.val := Classical.choose_spec (htsub g.property)
  refine ⟨Finset.univ.image rep, ?_⟩
  intro v
  obtain ⟨g, hgt, hvg⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_range_self v))
  let z : t := ⟨g, hgt⟩
  refine ⟨rep z, Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩, ?_⟩
  intro x hx
  have hdist : dist (F v) (F (rep z)) < ε := by
    rw [hrep]
    exact hvg
  have hpoint := (BoundedContinuousFunction.dist_coe_le_dist ⟨x, hx⟩).trans hdist.le
  change dist (f v x) (f (rep z) x) ≤ ε at hpoint
  simpa only [Real.dist_eq] using hpoint

theorem closedBall_payoff_approximants {V : Type*} {m : ℕ}
    (f : V → (Fin m → ℝ) → ℝ) {C : ℝ} (hfC : ∀ v x, |f v x| ≤ C)
    (hd : Tendsto (modulus f) (𝓝[>] 0) (𝓝 0)) (k : ℕ) :
    ∃ s : Finset V, ∀ v : V, ∃ w ∈ s,
      ∀ x ∈ Metric.closedBall (0 : Fin m → ℝ) (k : ℝ),
        |f v x - f w x| ≤ 1 / ((k : ℝ) + 1) :=
  finite_compact_payoff_approximation f hfC hd _ (isCompact_closedBall _ _) (by positivity)

end DistInterpRO.Proof
end
end


/- Inlined checked module: ModulusSequence -/
section
open Filter Topology
open DistInterpRO.Consistency

namespace DistInterpRO.Proof

theorem modulus_tendsto_sequence {V : Type*} {m : ℕ}
    (f : V → (Fin m → ℝ) → ℝ)
    (hd : Tendsto (modulus f) (𝓝[>] 0) (𝓝 0))
    (ε : ℕ → ℝ) (hεpos : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => modulus f (ε n)) atTop (𝓝 0) := by
  apply hd.comp
  apply tendsto_inf.mpr
  exact ⟨hεlim, tendsto_principal.mpr (Filter.Eventually.of_forall hεpos)⟩

end DistInterpRO.Proof
end


/- Inlined checked module: RobustEmpiricalBounds -/
section
open MeasureTheory Filter Topology
open DistInterpRO.Consistency

namespace DistInterpRO.Proof

theorem box_inf_le_payoff {V : Type*} {m : ℕ}
    (f : V → (Fin m → ℝ) → ℝ) {C ε : ℝ} (hfC : ∀ v x, |f v x| ≤ C)
    (hε : 0 ≤ ε) (v : V) (x : Fin m → ℝ) :
    (⨅ δ : {δ : Fin m → ℝ // ‖δ‖ ≤ ε}, f v (x + δ.1)) ≤ f v x := by
  have hb : BddBelow (Set.range (fun δ : {δ : Fin m → ℝ // ‖δ‖ ≤ ε} =>
      f v (x + δ.1))) := ⟨-C, by rintro _ ⟨δ, rfl⟩; exact (abs_le.mp (hfC v _)).1⟩
  have h := ciInf_le hb (⟨0, by simpa using hε⟩ : {δ : Fin m → ℝ // ‖δ‖ ≤ ε})
  simpa only [add_zero] using h

theorem payoff_sub_modulus_le_box_inf {V : Type*} {m : ℕ}
    (f : V → (Fin m → ℝ) → ℝ) {C ε : ℝ} (hfC : ∀ v x, |f v x| ≤ C)
    (hε : 0 ≤ ε) (v : V) (x : Fin m → ℝ) :
    f v x - modulus f ε ≤ (⨅ δ : {δ : Fin m → ℝ // ‖δ‖ ≤ ε}, f v (x + δ.1)) := by
  have : Nonempty {δ : Fin m → ℝ // ‖δ‖ ≤ ε} := ⟨⟨0, by simpa using hε⟩⟩
  apply le_ciInf
  intro δ
  have h := abs_sub_le_modulus f hfC v x δ.1 δ.2
  linarith [le_abs_self (f v x - f v (x + δ.1))]

theorem roObjective_le_sampleMean {V Ω : Type*} {m : ℕ}
    (f : V → (Fin m → ℝ) → ℝ) {C ε : ℝ} (hfC : ∀ v x, |f v x| ≤ C)
    (hε : 0 ≤ ε) (X : ℕ → Ω → Fin m → ℝ) (n : ℕ) (ω : Ω) (v : V) :
    roObjective f ε (fun i : Fin n => X i ω) v ≤ sampleMean (f v) X n ω := by
  unfold roObjective sampleMean
  apply mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun (i : Fin n) _ => box_inf_le_payoff f hfC hε v (X i ω)))
  positivity

theorem sampleMean_sub_modulus_le_roObjective {V Ω : Type*} {m : ℕ}
    (f : V → (Fin m → ℝ) → ℝ) {C ε : ℝ} (hfC : ∀ v x, |f v x| ≤ C)
    (hε : 0 ≤ ε) (X : ℕ → Ω → Fin m → ℝ) {n : ℕ} (hn : 0 < n)
    (ω : Ω) (v : V) :
    sampleMean (f v) X n ω - modulus f ε ≤ roObjective f ε (fun i : Fin n => X i ω) v := by
  have hb := Finset.sum_le_sum (fun (i : Fin n) (_ : i ∈ Finset.univ) =>
    payoff_sub_modulus_le_box_inf f hfC hε v (X i ω))
  have hmul := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (1 / (n : ℝ)))
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_sub, one_div, ← mul_assoc,
    inv_mul_cancel₀ hn0, one_mul] at hmul
  simpa only [sampleMean, roObjective, one_div] using hmul

end DistInterpRO.Proof
end


/- Inlined checked module: OptimizerConsistency -/
section
open Filter Topology

namespace DistInterpRO.Proof

theorem optimizer_gap_of_uniform_error {V : Type*} (F : Set V) (hF : F.Nonempty)
    (J A R : V → ℝ) (u : V) (hu : u ∈ F) (hopt : ∀ w ∈ F, R w ≤ R u)
    (C e d : ℝ) (hJ : ∀ w ∈ F, |J w| ≤ C)
    (herror : ∀ w ∈ F, |A w - J w| ≤ e)
    (hlower : ∀ w ∈ F, A w - d ≤ R w) (hupper : ∀ w ∈ F, R w ≤ A w) :
    (⨆ w : F, J w) - (2 * e + d) ≤ J u ∧ J u ≤ (⨆ w : F, J w) := by
  have : Nonempty F := hF.to_subtype
  have hb : BddAbove (Set.range (fun w : F => J w)) :=
    ⟨C, by rintro _ ⟨w, rfl⟩; exact (abs_le.mp (hJ w w.2)).2⟩
  constructor
  · have hbound : (⨆ w : F, J w) ≤ J u + (2 * e + d) := by
      apply ciSup_le
      intro w
      have hw := abs_le.mp (herror w w.2)
      have huu := abs_le.mp (herror u hu)
      linarith [hlower w w.2, hopt w w.2, hupper u hu]
    linarith
  · exact le_ciSup hb ⟨u, hu⟩

theorem selected_value_tendsto {V : Type*} (F : Set V) (hF : F.Nonempty)
    (J : V → ℝ) (A R : ℕ → V → ℝ) (u : ℕ → V)
    (hu : ∀ n, u n ∈ F) (hopt : ∀ n w, w ∈ F → R n w ≤ R n (u n))
    (C : ℝ) (hJ : ∀ w ∈ F, |J w| ≤ C) (e d : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hd : Tendsto d atTop (𝓝 0))
    (herror : ∀ᶠ n in atTop, ∀ w ∈ F, |A n w - J w| ≤ e n)
    (hlower : ∀ᶠ n in atTop, ∀ w ∈ F, A n w - d n ≤ R n w)
    (hupper : ∀ᶠ n in atTop, ∀ w ∈ F, R n w ≤ A n w) :
    Tendsto (fun n => J (u n)) atTop (𝓝 (⨆ w : F, J w)) := by
  have hbound : ∀ᶠ n in atTop,
      (⨆ w : F, J w) - (2 * e n + d n) ≤ J (u n) ∧ J (u n) ≤ (⨆ w : F, J w) := by
    filter_upwards [herror, hlower, hupper] with n hn hl hr
    exact optimizer_gap_of_uniform_error F hF J (A n) (R n) (u n) (hu n)
      (hopt n) C (e n) (d n) hJ hn hl hr
  have hlim : Tendsto (fun n => (⨆ w : F, J w) - (2 * e n + d n)) atTop
      (𝓝 (⨆ w : F, J w)) := by
    simpa using tendsto_const_nhds.sub ((tendsto_const_nhds.mul he).add hd)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
    (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2)

end DistInterpRO.Proof
end


/- Inlined checked module: UniformOptimizer -/
section
open Filter Topology
open DistInterpRO.Consistency

namespace DistInterpRO.Proof

theorem optimizer_consistency_of_uniform_event {V Ω : Type*} {m : ℕ}
    (f : V → (Fin m → ℝ) → ℝ) {C : ℝ} (hfC : ∀ v x, |f v x| ≤ C)
    (hd : Tendsto (modulus f) (𝓝[>] 0) (𝓝 0))
    (ε : ℕ → ℝ) (hεpos : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (F : Set V) (hF : F.Nonempty) (J : V → ℝ) (hJ : ∀ w, |J w| ≤ C)
    (X : ℕ → Ω → Fin m → ℝ) (ω : Ω) (v : ℕ → V)
    (hv : ∀ n, v n ∈ F ∧ ∀ w ∈ F,
      roObjective f (ε n) (fun i : Fin n => X i ω) w ≤
        roObjective f (ε n) (fun i : Fin n => X i ω) (v n))
    (huniform : ∀ η > 0, ∀ᶠ n in atTop, ∀ w,
      |sampleMean (f w) X n ω - J w| ≤ η) :
    Tendsto (fun n => J (v n)) atTop (𝓝 (⨆ w : F, J w)) := by
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  have hsample := huniform (δ / 4) (by positivity)
  have hmod : ∀ᶠ n in atTop, modulus f (ε n) < δ / 2 :=
    (modulus_tendsto_sequence f hd ε hεpos hεlim) (Iio_mem_nhds (by positivity))
  apply eventually_atTop.mp
  filter_upwards [hsample, hmod, eventually_gt_atTop (0 : ℕ)] with n hn hm hnpos
  have hb := optimizer_gap_of_uniform_error F hF J
    (fun w => sampleMean (f w) X n ω)
    (roObjective f (ε n) (fun i : Fin n => X i ω)) (v n) (hv n).1 (hv n).2
    C (δ / 4) (modulus f (ε n)) (fun w _ => hJ w) (fun w _ => hn w)
    (fun w _ => sampleMean_sub_modulus_le_roObjective f hfC (hεpos n).le X hnpos ω w)
    (fun w _ => roObjective_le_sampleMean f hfC (hεpos n).le X n ω w)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hb.1, hb.2]

end DistInterpRO.Proof
end


/- Inlined checked module: TightTails -/
section
open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Proof

noncomputable def tailIndicator {m : ℕ} (k : ℕ) (x : Fin m → ℝ) : ℝ :=
  if (k : ℝ) < ‖x‖ then 1 else 0

theorem tailIndicator_measurable {m : ℕ} (k : ℕ) :
    Measurable (tailIndicator (m := m) k) := by
  unfold tailIndicator
  exact Measurable.ite (measurableSet_lt measurable_const measurable_norm)
    measurable_const measurable_const

theorem tailIndicator_bounds {m : ℕ} (k : ℕ) (x : Fin m → ℝ) :
    0 ≤ tailIndicator k x ∧ |tailIndicator k x| ≤ 1 := by
  unfold tailIndicator
  split_ifs <;> norm_num

theorem tailIndicator_eq_zero {m : ℕ} (k : ℕ) {x : Fin m → ℝ}
    (hx : x ∈ Metric.closedBall (0 : Fin m → ℝ) (k : ℝ)) : tailIndicator k x = 0 := by
  have hn : ‖x‖ ≤ (k : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  simp only [tailIndicator, not_lt.mpr hn, if_false]

noncomputable def tailMass {m : ℕ} (μ : Measure (Fin m → ℝ)) (k : ℕ) : ℝ :=
  ∫ x, tailIndicator k x ∂μ

theorem tailMass_nonneg {m : ℕ} (μ : Measure (Fin m → ℝ)) (k : ℕ) :
    0 ≤ tailMass μ k :=
  integral_nonneg (fun x => (tailIndicator_bounds k x).1)

theorem tailIndicator_tendsto_zero {m : ℕ} (x : Fin m → ℝ) :
    Tendsto (fun k => tailIndicator k x) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  have he : ∀ᶠ k : ℕ in atTop, tailIndicator k x = 0 := by
    filter_upwards [eventually_ge_atTop N] with k hk
    have hn : ‖x‖ ≤ (k : ℝ) := hN.le.trans (Nat.cast_le.mpr hk)
    simp only [tailIndicator, not_lt.mpr hn, if_false]
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with k hk
  exact hk.symm

theorem tailMass_tendsto_zero {m : ℕ} (μ : Measure (Fin m → ℝ)) [IsFiniteMeasure μ] :
    Tendsto (tailMass μ) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun k => tailIndicator (m := m) k) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun k => (tailIndicator_measurable k).aestronglyMeasurable)
    (integrable_const 1)
    (fun k => Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using (tailIndicator_bounds k x).2))
    (Filter.Eventually.of_forall tailIndicator_tendsto_zero)
  change Tendsto (fun k => ∫ x, tailIndicator k x ∂μ) atTop (𝓝 0)
  simpa only [integral_zero] using h

end DistInterpRO.Proof
end


/- Inlined checked module: DensityExpectation -/
section
open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Proof

theorem probability_of_common_law {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure S) (X : Ω → S)
    (hX : Measurable X) (hlaw : P.map X = μ) : IsProbabilityMeasure μ := by
  rw [← hlaw]
  exact Measure.isProbabilityMeasure_map hX.aemeasurable

theorem integral_density {m : ℕ} (h : (Fin m → ℝ) → ℝ)
    (h_nonneg : ∀ x, 0 ≤ h x) (h_int : Integrable h) (g : (Fin m → ℝ) → ℝ) :
    (∫ x, g x ∂volume.withDensity (fun x => ENNReal.ofReal (h x))) =
      ∫ x, g x * h x := by
  rw [integral_withDensity_eq_integral_toReal_smul₀
    h_int.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  congr 1
  funext x
  simp only [ENNReal.toReal_ofReal (h_nonneg x), smul_eq_mul, mul_comm]

theorem bounded_expectation {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (g : S → ℝ) (C : ℝ)
    (hC : ∀ x, |g x| ≤ C) : |∫ x, g x ∂μ| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := g) (C := C) (Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using hC x))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

end DistInterpRO.Proof
end


/- Inlined checked module: MeanComparison -/
section
open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Proof

theorem sampleMean_abs_le {S Ω : Type*} (g : S → ℝ) (X : ℕ → Ω → S)
    (n : ℕ) (ω : Ω) : |sampleMean g X n ω| ≤ sampleMean (fun x => |g x|) X n ω := by
  simp only [sampleMean, abs_mul, abs_of_nonneg (show 0 ≤ 1 / (n : ℝ) by positivity)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)

theorem sampleMean_add {S Ω : Type*} (g h : S → ℝ) (X : ℕ → Ω → S)
    (n : ℕ) (ω : Ω) :
    sampleMean (fun x => g x + h x) X n ω = sampleMean g X n ω + sampleMean h X n ω := by
  simp only [sampleMean, Finset.sum_add_distrib, mul_add]

theorem sampleMean_mul {S Ω : Type*} (a : ℝ) (g : S → ℝ) (X : ℕ → Ω → S)
    (n : ℕ) (ω : Ω) : sampleMean (fun x => a * g x) X n ω = a * sampleMean g X n ω := by
  simp only [sampleMean, ← Finset.mul_sum]
  ring

theorem pointwise_net_bound {V : Type*} {m : ℕ} (f : V → (Fin m → ℝ) → ℝ)
    (C : ℝ) (hfC : ∀ v x, |f v x| ≤ C) (k : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (v w : V) (hclose : ∀ x ∈ Metric.closedBall (0 : Fin m → ℝ) (k : ℝ),
      |f v x - f w x| ≤ δ) (x : Fin m → ℝ) :
    |f v x - f w x| ≤ δ + 2 * C * tailIndicator k x := by
  by_cases hx : ‖x‖ ≤ (k : ℝ)
  · have hxK : x ∈ Metric.closedBall (0 : Fin m → ℝ) (k : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    rw [tailIndicator_eq_zero k hxK, mul_zero, add_zero]
    exact hclose x hxK
  · have hg : |f v x - f w x| ≤ C + C :=
      (abs_sub _ _).trans (add_le_add (hfC v x) (hfC w x))
    simp only [tailIndicator, lt_of_not_ge hx, if_true, mul_one]
    linarith

theorem sampleMean_net_bound {V Ω : Type*} {m : ℕ} (f : V → (Fin m → ℝ) → ℝ)
    (C : ℝ) (hfC : ∀ v x, |f v x| ≤ C) (k : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (v w : V) (hclose : ∀ x ∈ Metric.closedBall (0 : Fin m → ℝ) (k : ℝ),
      |f v x - f w x| ≤ δ) (X : ℕ → Ω → Fin m → ℝ) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    |sampleMean (f v) X n ω - sampleMean (f w) X n ω| ≤
      δ + 2 * C * sampleMean (tailIndicator k) X n ω := by
  rw [← sampleMean_sub]
  calc
    _ ≤ sampleMean (fun x => |f v x - f w x|) X n ω := sampleMean_abs_le _ _ _ _
    _ ≤ sampleMean (fun x => δ + 2 * C * tailIndicator k x) X n ω :=
      sampleMean_mono (pointwise_net_bound f C hfC k δ hδ v w hclose) X n ω
    _ = _ := by
      rw [sampleMean_add, sampleMean_const _ _ hn, sampleMean_mul]

theorem expectation_net_bound {V : Type*} {m : ℕ} (f : V → (Fin m → ℝ) → ℝ)
    (hfm : ∀ v, Measurable (f v)) (C : ℝ) (hfC : ∀ v x, |f v x| ≤ C)
    (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
    (k : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (v w : V)
    (hclose : ∀ x ∈ Metric.closedBall (0 : Fin m → ℝ) (k : ℝ), |f v x - f w x| ≤ δ) :
    |(∫ x, f v x ∂μ) - ∫ x, f w x ∂μ| ≤ δ + 2 * C * tailMass μ k := by
  have hv := bounded_integrable μ (hfm v) C (hfC v)
  have hw := bounded_integrable μ (hfm w) C (hfC w)
  have ht := bounded_integrable μ (tailIndicator_measurable (m := m) k) 1
    (fun x => (tailIndicator_bounds k x).2)
  rw [← integral_sub hv hw]
  calc
    _ ≤ ∫ x, |f v x - f w x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, δ + 2 * C * tailIndicator k x ∂μ :=
      integral_mono (hv.sub hw).abs ((integrable_const δ).add (ht.const_mul (2 * C)))
        (pointwise_net_bound f C hfC k δ hδ v w hclose)
    _ = _ := by
      rw [integral_add (integrable_const δ) (ht.const_mul (2 * C)), integral_const_mul]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, tailMass]

end DistInterpRO.Proof
end


/- Inlined checked module: DeterministicNet -/
section
open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Proof

theorem uniform_convergence_of_net_limits {V Ω : Type*} {m : ℕ}
    (f : V → (Fin m → ℝ) → ℝ) (hfm : ∀ v, Measurable (f v))
    (C : ℝ) (hfC : ∀ v x, |f v x| ≤ C)
    (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
    (s : ℕ → Finset V)
    (hnet : ∀ k v, ∃ w ∈ s k, ∀ x ∈ Metric.closedBall (0 : Fin m → ℝ) (k : ℝ),
      |f v x - f w x| ≤ 1 / ((k : ℝ) + 1))
    (X : ℕ → Ω → Fin m → ℝ) (ω : Ω)
    (htail : ∀ k, Tendsto (fun n => sampleMean (tailIndicator k) X n ω)
      atTop (𝓝 (tailMass μ k)))
    (hrep : ∀ k w, w ∈ s k → Tendsto (fun n => sampleMean (f w) X n ω)
      atTop (𝓝 (∫ x, f w x ∂μ))) :
    ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ v : V,
      |sampleMean (f v) X n ω - ∫ x, f v x ∂μ| ≤ η := by
  classical
  let B : ℕ → ℕ → ℝ := fun k n =>
    2 * (1 / ((k : ℝ) + 1)) +
      2 * C * (sampleMean (tailIndicator k) X n ω + tailMass μ k) +
        ∑ w ∈ s k, |sampleMean (f w) X n ω - ∫ x, f w x ∂μ|
  let b : ℕ → ℝ := fun k => 2 * (1 / ((k : ℝ) + 1)) + 4 * C * tailMass μ k
  have hbound (k n : ℕ) (hn : 0 < n) (v : V) :
      |sampleMean (f v) X n ω - ∫ x, f v x ∂μ| ≤ B k n := by
    obtain ⟨w, hw, hclose⟩ := hnet k v
    have hδ : 0 ≤ 1 / ((k : ℝ) + 1) := by positivity
    have hemp := sampleMean_net_bound f C hfC k _ hδ v w hclose X hn ω
    have hexp := expectation_net_bound f hfm C hfC μ k _ hδ v w hclose
    have hsum : |sampleMean (f w) X n ω - ∫ x, f w x ∂μ| ≤
        ∑ z ∈ s k, |sampleMean (f z) X n ω - ∫ x, f z x ∂μ| :=
      Finset.single_le_sum
        (f := fun z => |sampleMean (f z) X n ω - ∫ x, f z x ∂μ|)
        (fun _ _ => abs_nonneg _) hw
    have htri : |sampleMean (f v) X n ω - ∫ x, f v x ∂μ| ≤
        |sampleMean (f v) X n ω - sampleMean (f w) X n ω| +
        |sampleMean (f w) X n ω - ∫ x, f w x ∂μ| +
        |(∫ x, f w x ∂μ) - ∫ x, f v x ∂μ| := by
      calc
        _ = |(sampleMean (f v) X n ω - sampleMean (f w) X n ω) +
            (sampleMean (f w) X n ω - ∫ x, f w x ∂μ) +
            ((∫ x, f w x ∂μ) - ∫ x, f v x ∂μ)| := by congr 1; ring
        _ ≤ _ := (abs_add_le
          ((sampleMean (f v) X n ω - sampleMean (f w) X n ω) +
            (sampleMean (f w) X n ω - ∫ x, f w x ∂μ))
          ((∫ x, f w x ∂μ) - ∫ x, f v x ∂μ)).trans
          (add_le_add (abs_add_le
            (sampleMean (f v) X n ω - sampleMean (f w) X n ω)
            (sampleMean (f w) X n ω - ∫ x, f w x ∂μ)) le_rfl)
    rw [abs_sub_comm (∫ x, f w x ∂μ) (∫ x, f v x ∂μ)] at htri
    dsimp [B]
    linarith
  have hB (k : ℕ) : Tendsto (B k) atTop (𝓝 (b k)) := by
    have hsum : Tendsto
        (fun n => ∑ w ∈ s k, |sampleMean (f w) X n ω - ∫ x, f w x ∂μ|)
        atTop (𝓝 (∑ _w ∈ s k, (0 : ℝ))) := by
      apply tendsto_finsetSum
      intro w hw
      have hc : Tendsto (fun _n : ℕ => ∫ x, f w x ∂μ) atTop
          (𝓝 (∫ x, f w x ∂μ)) := tendsto_const_nhds
      simpa only [sub_self, abs_zero] using ((hrep k w hw).sub hc).abs
    have htc : Tendsto (fun _n : ℕ => tailMass μ k) atTop (𝓝 (tailMass μ k)) :=
      tendsto_const_nhds
    have ht := ((htail k).add htc).const_mul (2 * C)
    have hconst : Tendsto (fun _n : ℕ => 2 * (1 / ((k : ℝ) + 1))) atTop
        (𝓝 (2 * (1 / ((k : ℝ) + 1)))) := tendsto_const_nhds
    have hall := (hconst.add ht).add hsum
    convert hall using 1
    congr 1
    simp only [Finset.sum_const_zero, add_zero]
    dsimp [b]
    ring
  have hb : Tendsto b atTop (𝓝 0) := by
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2).add
      ((tailMass_tendsto_zero μ).const_mul (4 * C))
    change Tendsto (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1)) + 4 * C * tailMass μ k)
      atTop (𝓝 0)
    simpa only [mul_zero, add_zero] using h
  intro η hη
  obtain ⟨k, hk⟩ := (hb.eventually_lt_const hη).exists
  filter_upwards [(hB k).eventually_lt_const hk, eventually_gt_atTop (0 : ℕ)] with n hn hpos
  intro v
  exact (hbound k n hpos v).trans hn.le

end DistInterpRO.Proof
end


/- Inlined checked module: UniformSLLN -/
section
open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Proof

theorem uniform_sampleMean_ae {V Ω : Type*} {m : ℕ} [MeasurableSpace Ω]
    (f : V → (Fin m → ℝ) → ℝ) (hfm : ∀ v, Measurable (f v))
    (C : ℝ) (hfC : ∀ v x, |f v x| ≤ C)
    (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
    (hnet : ∀ k : ℕ, ∃ s : Finset V, ∀ v, ∃ w ∈ s,
      ∀ x ∈ Metric.closedBall (0 : Fin m → ℝ) (k : ℝ),
        |f v x - f w x| ≤ 1 / ((k : ℝ) + 1))
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → Fin m → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = μ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ v : V,
      |sampleMean (f v) X n ω - ∫ x, f v x ∂μ| ≤ η := by
  classical
  let s : ℕ → Finset V := fun k => (hnet k).choose
  have hs (k : ℕ) : ∀ v, ∃ w ∈ s k,
      ∀ x ∈ Metric.closedBall (0 : Fin m → ℝ) (k : ℝ),
        |f v x - f w x| ≤ 1 / ((k : ℝ) + 1) := (hnet k).choose_spec
  have hrep (k : ℕ) : ∀ᵐ ω ∂P, ∀ w ∈ s k,
      Tendsto (fun n => sampleMean (f w) X n ω) atTop (𝓝 (∫ x, f w x ∂μ)) := by
    apply (s k).eventually_all.mpr
    intro w _hw
    exact sampleMean_strong_law P μ X hXm hind hlaw (f w) (hfm w) C (hfC w)
  have htail (k : ℕ) : ∀ᵐ ω ∂P,
      Tendsto (fun n => sampleMean (tailIndicator k) X n ω) atTop (𝓝 (tailMass μ k)) :=
    sampleMean_strong_law P μ X hXm hind hlaw (tailIndicator k)
      (tailIndicator_measurable k) 1 (fun x => (tailIndicator_bounds k x).2)
  filter_upwards [ae_all_iff.mpr hrep, ae_all_iff.mpr htail] with ω hωrep hωtail
  exact uniform_convergence_of_net_limits f hfm C hfC μ s hs X ω hωtail hωrep

end DistInterpRO.Proof
end


/- Inlined checked module: BoxConsistencyRoot -/
section
open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Consistency

theorem theorem_3_1 {V : Type*} {m : ℕ} (F : Set V) (hF : F.Nonempty)
    (f : V → (Fin m → ℝ) → ℝ) (hfm : ∀ v, Measurable (f v))
    (C : ℝ) (hfC : ∀ v x, |f v x| ≤ C)
    (hd : Tendsto (modulus f) (𝓝[>] 0) (𝓝 0))
    (hstar : (Fin m → ℝ) → ℝ) (hstar_nonneg : ∀ x, 0 ≤ hstar x)
    (hstar_int : Integrable hstar) (_hstar_one : ∫ x, hstar x = 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin m → ℝ) (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = volume.withDensity (fun x => ENNReal.ofReal (hstar x)))
    (ε : ℕ → ℝ) (hε_pos : ∀ n, 0 < ε n)
    (_hε_anti : Antitone ε) (hε_lim : Tendsto ε atTop (𝓝 0))
    (_hnε_mono : Monotone (fun n : ℕ => (n : ℝ) * ε n ^ m))
    (_hnε_lim : Tendsto (fun n : ℕ => (n : ℝ) * ε n ^ m) atTop atTop)
    (v : ℕ → Ω → V)
    (hv : ∀ n ω, v n ω ∈ F ∧ ∀ w ∈ F,
      roObjective f (ε n) (fun i : Fin n => X i ω) w ≤
        roObjective f (ε n) (fun i : Fin n => X i ω) (v n ω)) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫ x, f (v n ω) x * hstar x) atTop
      (𝓝 (⨆ w : F, ∫ x, f w x * hstar x)) := by
  let μ : Measure (Fin m → ℝ) := volume.withDensity (fun x => ENNReal.ofReal (hstar x))
  have : IsProbabilityMeasure μ := Proof.probability_of_common_law P μ (X 0) (hXm 0) (hlaw 0)
  have huniform := Proof.uniform_sampleMean_ae f hfm C hfC μ
    (fun k => Proof.closedBall_payoff_approximants f hfC hd k) P X hXm hind hlaw
  filter_upwards [huniform] with ω hω
  have hbound (w : V) : |∫ x, f w x ∂μ| ≤ C :=
    Proof.bounded_expectation μ (f w) C (hfC w)
  have hlim := Proof.optimizer_consistency_of_uniform_event f hfC hd ε hε_pos hε_lim
    F hF (fun w => ∫ x, f w x ∂μ) hbound X ω (fun n => v n ω) (fun n => hv n ω) hω
  have he (w : V) : (∫ x, f w x ∂μ) = ∫ x, f w x * hstar x :=
    Proof.integral_density hstar hstar_nonneg hstar_int (f w)
  simpa only [he] using hlim

end DistInterpRO.Consistency
end


open MeasureTheory Filter Topology ProbabilityTheory DistInterpRO.Consistency

theorem solution {V : Type*} {m : ℕ} (F : Set V) (hF : F.Nonempty)
    (f : V → (Fin m → ℝ) → ℝ) (hfm : ∀ v, Measurable (f v))
    (C : ℝ) (hfC : ∀ v x, |f v x| ≤ C)
    (hd : Tendsto (modulus f) (𝓝[>] 0) (𝓝 0))
    (hstar : (Fin m → ℝ) → ℝ) (hstar_nonneg : ∀ x, 0 ≤ hstar x)
    (hstar_int : Integrable hstar) (hstar_one : ∫ x, hstar x = 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin m → ℝ) (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = volume.withDensity (fun x => ENNReal.ofReal (hstar x)))
    (ε : ℕ → ℝ) (hε_pos : ∀ n, 0 < ε n)
    (hε_anti : Antitone ε) (hε_lim : Tendsto ε atTop (𝓝 0))
    (hnε_mono : Monotone (fun n : ℕ => (n : ℝ) * ε n ^ m))
    (hnε_lim : Tendsto (fun n : ℕ => (n : ℝ) * ε n ^ m) atTop atTop)
    (v : ℕ → Ω → V)
    (hv : ∀ n ω, v n ω ∈ F ∧ ∀ w ∈ F,
      roObjective f (ε n) (fun i : Fin n => X i ω) w ≤
        roObjective f (ε n) (fun i : Fin n => X i ω) (v n ω)) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫ x, f (v n ω) x * hstar x) atTop
      (𝓝 (⨆ w : F, ∫ x, f w x * hstar x)) := DistInterpRO.Consistency.theorem_3_1 F hF f hfm C hfC hd hstar hstar_nonneg hstar_int hstar_one P X hXm hind hlaw ε hε_pos hε_anti hε_lim hnε_mono hnε_lim v hv
