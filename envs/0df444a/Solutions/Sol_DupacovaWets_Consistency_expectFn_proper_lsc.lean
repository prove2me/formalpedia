-- Prove2me | solution 1 for DupacovaWets.Consistency.expectFn_proper_lsc
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T06:41:45.324545+00:00
-- url     : https://prove2.me/submissions/85ff15ec-026e-4793-b737-c904a69eca87

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_DupacovaWets_Consistency_ExtendedFunctions
import Definitions.Def_DupacovaWets_Consistency_Assumptions
import Definitions.Def_DupacovaWets_Consistency_Multifunction
open MeasureTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction
open DupacovaWets.Consistency

namespace DW6Aux

section Normal
variable {T : Type*} [MeasurableSpace T] {n : ℕ}

local notation "Y" => EuclideanSpace ℝ (Fin n)

theorem T_meas (K : Set Y) (hK : IsCompact K)
    (φ : T → Y → ℝ) (hm : ∀ y, Measurable (fun s => φ s y))
    (hc : ∀ s, Continuous (φ s)) (a : T → ℝ) (ha : Measurable a) :
    MeasurableSet {s | ∃ y ∈ K, φ s y ≤ a s} := by
  obtain ⟨D, hDK, hDc, hKD⟩ := hK.isSeparable.exists_countable_dense_subset
  have heq : {s | ∃ y ∈ K, φ s y ≤ a s} =
      ⋂ k : ℕ, ⋃ y ∈ D, {s | φ s y < a s + 1 / ((k : ℝ) + 1)} := by
    ext s
    simp only [mem_setOf_eq, mem_iInter, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨y, hyK, hy⟩ k
      have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hopen : IsOpen {z | φ s z < a s + 1 / ((k : ℝ) + 1)} :=
        isOpen_lt (hc s) continuous_const
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp (hKD hyK) _ hopen (by
        show φ s y < _; linarith)
      exact ⟨z, hz2, hz1⟩
    · intro h
      choose y hyD hy using h
      have hyK : ∀ k, y k ∈ K := fun k => hDK (hyD k)
      obtain ⟨b, hbK, ψ, hψ, hlim⟩ := hK.tendsto_subseq hyK
      refine ⟨b, hbK, ?_⟩
      have h1 : Tendsto (fun k => φ s (y (ψ k))) atTop (𝓝 (φ s b)) :=
        ((hc s).tendsto b).comp hlim
      have h2 : Tendsto (fun k => a s + 1 / ((ψ k : ℝ) + 1)) atTop (𝓝 (a s + 0)) :=
        tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.comp hψ.tendsto_atTop)
      rw [add_zero] at h2
      exact le_of_tendsto_of_tendsto' h1 h2 (fun k => (hy (ψ k)).le)
  rw [heq]
  refine MeasurableSet.iInter fun k => ?_
  refine MeasurableSet.biUnion hDc fun y _ => ?_
  exact measurableSet_lt (hm y) (ha.add measurable_const)

/-- A "normal" function: increasing supremum of Carathéodory functions. -/
structure NormalRep (φ : ℕ → T → Y → ℝ) : Prop where
  meas : ∀ m y, Measurable (fun s => φ m s y)
  cont : ∀ m s, Continuous (φ m s)
  mono : ∀ s y, Monotone (fun m => φ m s y)

theorem N1 {φ : ℕ → T → Y → ℝ} (hφ : NormalRep φ) (K : Set Y) (hK : IsCompact K)
    (a : T → ℝ) (ha : Measurable a) :
    MeasurableSet {s | ∃ y ∈ K, (⨆ m, (φ m s y : EReal)) ≤ a s} := by
  have heq : {s | ∃ y ∈ K, (⨆ m, (φ m s y : EReal)) ≤ a s} =
      ⋂ m, {s | ∃ y ∈ K, φ m s y ≤ a s} := by
    ext s
    simp only [mem_setOf_eq, mem_iInter]
    constructor
    · rintro ⟨y, hyK, hy⟩ m
      refine ⟨y, hyK, ?_⟩
      have := (le_iSup (fun m => (φ m s y : EReal)) m).trans hy
      exact_mod_cast this
    · intro h
      choose y hyK hy using h
      obtain ⟨b, hbK, ψ, hψ, hlim⟩ := hK.tendsto_subseq hyK
      refine ⟨b, hbK, iSup_le fun m => ?_⟩
      have h1 : Tendsto (fun j => φ m s (y (ψ j))) atTop (𝓝 (φ m s b)) :=
        ((hφ.cont m s).tendsto b).comp hlim
      have h2 : ∀ᶠ j in atTop, φ m s (y (ψ j)) ≤ a s := by
        filter_upwards [eventually_ge_atTop m] with j hj
        exact (hφ.mono s _ (hj.trans (hψ.id_le j))).trans (hy (ψ j))
      exact_mod_cast le_of_tendsto h1 h2
  rw [heq]
  exact MeasurableSet.iInter fun m => T_meas K hK _ (hφ.meas m) (hφ.cont m) a ha

theorem N2 {φ : ℕ → T → Y → ℝ} (hφ : NormalRep φ) :
    Measurable (fun s => ⨅ y, ⨆ m, (φ m s y : EReal)) := by
  refine measurable_of_Iio fun c => ?_
  have heq : (fun s => ⨅ y, ⨆ m, (φ m s y : EReal)) ⁻¹' Iio c =
      ⋃ R : ℕ, ⋃ q : ℚ, ⋃ (_ : ((q : ℝ) : EReal) < c),
        {s | ∃ y ∈ Metric.closedBall (0 : Y) R, (⨆ m, (φ m s y : EReal)) ≤ ((q : ℝ) : ℝ)} := by
    ext s
    simp only [mem_preimage, mem_Iio, mem_iUnion, mem_setOf_eq, exists_prop]
    constructor
    · intro h
      obtain ⟨y, hy⟩ := iInf_lt_iff.mp h
      obtain ⟨q, hq1, hq2⟩ := EReal.exists_rat_btwn_of_lt hy
      obtain ⟨R, hR⟩ := exists_nat_ge ‖y‖
      exact ⟨R, q, hq2, y, by simpa using hR, hq1.le⟩
    · rintro ⟨R, q, hq, y, -, hy⟩
      exact lt_of_le_of_lt ((iInf_le _ y).trans hy) hq
  rw [heq]
  refine MeasurableSet.iUnion fun R => MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => ?_
  exact N1 hφ _ (isCompact_closedBall _ _) _ measurable_const

theorem N3 {φ : ℕ → T → Y → ℝ} (hφ : NormalRep φ) (F : Set Y) (hF : IsClosed F)
    (a : T → ℝ) (ha : Measurable a) :
    MeasurableSet {s | ∃ y ∈ F, (⨆ m, (φ m s y : EReal)) ≤ a s} := by
  have heq : {s | ∃ y ∈ F, (⨆ m, (φ m s y : EReal)) ≤ a s} =
      ⋃ R : ℕ, {s | ∃ y ∈ F ∩ Metric.closedBall (0 : Y) R, (⨆ m, (φ m s y : EReal)) ≤ a s} := by
    ext s
    simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨y, hyF, hy⟩
      obtain ⟨R, hR⟩ := exists_nat_ge ‖y‖
      exact ⟨R, y, ⟨hyF, by simpa using hR⟩, hy⟩
    · rintro ⟨R, y, ⟨hyF, -⟩, hy⟩
      exact ⟨y, hyF, hy⟩
  rw [heq]
  exact MeasurableSet.iUnion fun R =>
    N1 hφ _ ((isCompact_closedBall _ _).inter_left hF) a ha
end Normal

section Kern
variable {T : Type*} [MeasurableSpace T] {Ξ : Type*} [MeasurableSpace Ξ]

theorem klint_meas (κ : T → Measure Ξ) (hκ : ∀ A, MeasurableSet A → Measurable fun t => κ t A)
    (g : Ξ → ℝ≥0∞) (hg : Measurable g) : Measurable (fun t => ∫⁻ ξ, g ξ ∂(κ t)) :=
  (Measure.measurable_lintegral hg).comp (Measure.measurable_of_measurable_coe κ hκ)

theorem kint_meas (κ : T → Measure Ξ) (hκ : ∀ A, MeasurableSet A → Measurable fun t => κ t A)
    (hp : ∀ t, IsProbabilityMeasure (κ t)) (g : Ξ → ℝ) (hg : Measurable g) :
    Measurable (fun t => ∫ ξ, g ξ ∂(κ t)) := by
  let K : ProbabilityTheory.Kernel T Ξ := ⟨κ, Measure.measurable_of_measurable_coe κ hκ⟩
  haveI : ProbabilityTheory.IsMarkovKernel K := ⟨fun t => hp t⟩
  have := StronglyMeasurable.integral_kernel_prod_right (κ := K)
    (f := fun (_ : T) (ξ : Ξ) => g ξ) (hg.comp measurable_snd).stronglyMeasurable
  exact this.measurable
theorem ite_meas (A : Set T) [DecidablePred (· ∈ A)] (hA : MeasurableSet A) (g : T → ℝ) (hg : Measurable g) :
    Measurable (fun t => if t ∈ A then g t else 0) := Measurable.ite hA hg measurable_const
end Kern

section Env
variable {n : ℕ} {Ξ : Type*} [TopologicalSpace Ξ] [MeasurableSpace Ξ] [OpensMeasurableSpace Ξ]


/-- Pasch–Hausdorff envelope. -/
noncomputable def fenv {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (m : ℕ) (y : EuclideanSpace ℝ (Fin n)) (ξ : Ξ) : EReal :=
  ⨅ z, f z ξ + (((m : ℝ) * ‖y - z‖ : ℝ) : EReal)

variable (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal)

theorem fenv_measurable (S : Set (EuclideanSpace ℝ (Fin n))) (h34 : Assumption3_4 f S) (m : ℕ) (y : EuclideanSpace ℝ (Fin n)) : Measurable (fenv f m y) := by
  refine measurable_of_Iio fun a => ?_
  refine IsOpen.measurableSet ?_
  have : fenv f m y ⁻¹' Iio a = ⋃ z, {ξ | f z ξ + (((m : ℝ) * ‖y - z‖ : ℝ) : EReal) < a} := by
    ext ξ; simp [fenv, iInf_lt_iff]
  rw [this]
  refine isOpen_iUnion fun z => ?_
  by_cases hz : z ∈ S
  · have hc : Continuous fun ξ => f z ξ + (((m : ℝ) * ‖y - z‖ : ℝ) : EReal) := by
      refine continuous_iff_continuousAt.2 fun ξ => ?_
      exact (EReal.continuousAt_add (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _))).comp
        ((h34.continuous_of_mem z hz).continuousAt.prodMk continuousAt_const)
    exact isOpen_lt hc continuous_const
  · have : {ξ | f z ξ + (((m : ℝ) * ‖y - z‖ : ℝ) : EReal) < a} = ∅ := by
      ext ξ
      have h1 : f z ξ = ⊤ := by
        by_contra h
        exact hz ((h34.lt_top_iff z ξ).mp (lt_top_iff_ne_top.mpr h))
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [h1, EReal.top_add_coe]; exact le_top
    rw [this]; exact isOpen_empty

theorem psi_le_fenv (m : ℕ) (y : EuclideanSpace ℝ (Fin n)) (ξ : Ξ) : (⨅ x, f x ξ) ≤ fenv f m y ξ := by
  refine le_iInf fun z => ?_
  refine (iInf_le _ z).trans ?_
  have : (0 : EReal) ≤ (((m : ℝ) * ‖y - z‖ : ℝ) : EReal) := by
    exact_mod_cast mul_nonneg (Nat.cast_nonneg m) (norm_nonneg _)
  exact le_add_of_nonneg_right this

theorem fenv_le (m : ℕ) (y z : EuclideanSpace ℝ (Fin n)) (ξ : Ξ) :
    fenv f m y ξ ≤ f z ξ + (((m : ℝ) * ‖y - z‖ : ℝ) : EReal) := iInf_le _ z

theorem fenv_le_self (m : ℕ) (y : EuclideanSpace ℝ (Fin n)) (ξ : Ξ) : fenv f m y ξ ≤ f y ξ := by
  have := fenv_le f m y y ξ
  simpa using this

theorem fenv_mono (y : EuclideanSpace ℝ (Fin n)) (ξ : Ξ) : Monotone (fun m => fenv f m y ξ) := by
  intro m m' hmm
  refine iInf_mono fun z => ?_
  gcongr

theorem fenv_lip (m : ℕ) (y y' : EuclideanSpace ℝ (Fin n)) (ξ : Ξ) :
    fenv f m y ξ ≤ fenv f m y' ξ + (((m : ℝ) * ‖y - y'‖ : ℝ) : EReal) := by
  rw [← EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))]
  refine le_iInf fun z => ?_
  rw [EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))]
  refine (fenv_le f m y z ξ).trans ?_
  rw [add_assoc, ← EReal.coe_add]
  gcongr
  · have := norm_sub_le_norm_sub_add_norm_sub y y' z
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith [this]) hm

theorem fenv_iSup (S : Set (EuclideanSpace ℝ (Fin n))) (h34 : Assumption3_4 f S)
    (y : EuclideanSpace ℝ (Fin n)) (ξ : Ξ) (hψ : (⨅ x, f x ξ) ≠ ⊥) :
    (⨆ m, fenv f m y ξ) = f y ξ := by
  refine le_antisymm (iSup_le fun m => fenv_le_self f m y ξ) ?_
  have key : ∀ a, a < f y ξ → ∃ m, a ≤ fenv f m y ξ := by
    intro a ha
    by_cases hbt : (⨅ x, f x ξ) = ⊤
    · exact ⟨0, (le_top.trans_eq hbt.symm).trans (psi_le_fenv f 0 y ξ)⟩
    by_cases hab : a = ⊥
    · exact ⟨0, hab ▸ bot_le⟩
    have hat : a ≠ ⊤ := ha.ne_top
    set b := (⨅ x, f x ξ) with hb
    obtain ⟨b', hb'⟩ : ∃ b' : ℝ, b = b' := ⟨b.toReal, (EReal.coe_toReal hbt hψ).symm⟩
    obtain ⟨a', ha'⟩ : ∃ a' : ℝ, a = a' := ⟨a.toReal, (EReal.coe_toReal hat hab).symm⟩
    have hev := h34.lsc ξ y a ha
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    obtain ⟨m, hm⟩ := exists_nat_ge ((a' - b') / δ)
    refine ⟨m, le_iInf fun z => ?_⟩
    have hc0 : (0 : ℝ) ≤ (m : ℝ) * ‖y - z‖ := mul_nonneg (Nat.cast_nonneg m) (norm_nonneg _)
    by_cases hz : dist z y < δ
    · exact (hball hz).le.trans (le_add_of_nonneg_right (by exact_mod_cast hc0))
    · push_neg at hz
      have h1 : (b' : EReal) ≤ f z ξ := by rw [← hb']; exact iInf_le _ z
      have h2 : a' ≤ b' + (m : ℝ) * ‖y - z‖ := by
        have : δ ≤ ‖y - z‖ := by rw [← dist_eq_norm, dist_comm]; exact hz
        have h3 : a' - b' ≤ m * δ := by
          have := (div_le_iff₀ hδ).mp hm; linarith
        nlinarith [Nat.cast_nonneg (α := ℝ) m]
      rw [ha']
      calc (a' : EReal) ≤ ((b' + (m : ℝ) * ‖y - z‖ : ℝ) : EReal) := by exact_mod_cast h2
        _ = (b' : EReal) + (((m : ℝ) * ‖y - z‖ : ℝ) : EReal) := EReal.coe_add _ _
        _ ≤ f z ξ + (((m : ℝ) * ‖y - z‖ : ℝ) : EReal) := by gcongr
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨d, hcd, hd⟩ := exists_between hc
  obtain ⟨m, hm⟩ := key d hd
  exact hcd.trans_le (hm.trans (le_iSup (fun m => fenv f m y ξ) m))

end Env

section Exp
variable {Ξ : Type*} [MeasurableSpace Ξ]

theorem expect_mono (Q : Measure Ξ) (g g' : Ξ → EReal) (h : ∀ ξ, g ξ ≤ g' ξ) :
    expect Q g ≤ expect Q g' := by
  unfold expect
  by_cases h' : ∫⁻ ξ, (g' ξ).toENNReal ∂Q = ∞
  · rw [if_pos h']; exact le_top
  have hP : ∫⁻ ξ, (g ξ).toENNReal ∂Q ≤ ∫⁻ ξ, (g' ξ).toENNReal ∂Q :=
    lintegral_mono fun ξ => EReal.toENNReal_le_toENNReal (h ξ)
  have hP' : ∫⁻ ξ, (g ξ).toENNReal ∂Q ≠ ∞ := ne_top_of_le_ne_top h' hP
  rw [if_neg h', if_neg hP']
  refine EReal.sub_le_sub (by exact_mod_cast hP) ?_
  exact_mod_cast lintegral_mono fun ξ => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (h ξ))

theorem expect_tendsto (Q : Measure Ξ) (g : ℕ → Ξ → EReal) (G : Ξ → EReal)
    (hgm : ∀ m, Measurable (g m)) (hmono : ∀ ξ, Monotone fun m => g m ξ)
    (hlim : ∀ᵐ ξ ∂Q, Tendsto (fun m => g m ξ) atTop (𝓝 (G ξ)))
    (ψ : Ξ → EReal) (hψ : ∀ m ξ, ψ ξ ≤ g m ξ) (hψi : ∫⁻ ξ, (-ψ ξ).toENNReal ∂Q ≠ ∞)
    (hP : ∀ m, ∫⁻ ξ, (g m ξ).toENNReal ∂Q ≠ ∞) :
    Tendsto (fun m => expect Q (g m)) atTop (𝓝 (expect Q G)) := by
  have hPt : Tendsto (fun m => ∫⁻ ξ, (g m ξ).toENNReal ∂Q) atTop
      (𝓝 (∫⁻ ξ, (G ξ).toENNReal ∂Q)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun m => (hgm m).ereal_toENNReal.aemeasurable)
      (Eventually.of_forall fun ξ i j hij => EReal.toENNReal_le_toENNReal (hmono ξ hij)) ?_
    filter_upwards [hlim] with ξ hξ
    exact (EReal.continuous_toENNReal.tendsto _).comp hξ
  have hNt : Tendsto (fun m => ∫⁻ ξ, (-g m ξ).toENNReal ∂Q) atTop
      (𝓝 (∫⁻ ξ, (-G ξ).toENNReal ∂Q)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun ξ => (-ψ ξ).toENNReal)
      (fun m => (hgm m).neg.ereal_toENNReal)
      (fun m => Eventually.of_forall fun ξ => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hψ m ξ)))
      hψi ?_
    filter_upwards [hlim] with ξ hξ
    exact (EReal.continuous_toENNReal.tendsto _).comp ((continuous_neg.tendsto _).comp hξ)
  have hN0 : ∫⁻ ξ, (-G ξ).toENNReal ∂Q ≠ ∞ := by
    refine ne_top_of_le_ne_top hψi (le_of_tendsto' hNt fun m => ?_)
    exact lintegral_mono fun ξ => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hψ m ξ))
  have hG : expect Q G = ((∫⁻ ξ, (G ξ).toENNReal ∂Q : ℝ≥0∞) : EReal) +
      -((∫⁻ ξ, (-G ξ).toENNReal ∂Q : ℝ≥0∞) : EReal) := by
    unfold expect
    split_ifs with h
    · rw [h, EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal hN0, ← EReal.coe_neg,
        EReal.top_add_coe]
    · rfl
  have hg : ∀ m, expect Q (g m) = ((∫⁻ ξ, (g m ξ).toENNReal ∂Q : ℝ≥0∞) : EReal) +
      -((∫⁻ ξ, (-g m ξ).toENNReal ∂Q : ℝ≥0∞) : EReal) := by
    intro m; unfold expect; rw [if_neg (hP m)]; rfl
  simp only [hg, hG]
  have hc : ContinuousAt (fun p : EReal × EReal => p.1 + p.2)
      (((∫⁻ ξ, (G ξ).toENNReal ∂Q : ℝ≥0∞) : EReal),
        -((∫⁻ ξ, (-G ξ).toENNReal ∂Q : ℝ≥0∞) : EReal)) := by
    refine EReal.continuousAt_add (.inr ?_) (.inl ?_)
    · rw [← EReal.coe_ennreal_toReal hN0, ← EReal.coe_neg]; exact EReal.coe_ne_bot _
    · exact (EReal.coe_ennreal_nonneg _).trans_lt' (EReal.bot_lt_zero) |>.ne'
  exact hc.tendsto.comp (((continuous_coe_ennreal_ereal.tendsto _).comp hPt).prodMk_nhds
    ((continuous_neg.tendsto _).comp ((continuous_coe_ennreal_ereal.tendsto _).comp hNt)))

theorem expect_ae_coe (Q : Measure Ξ) (g : Ξ → EReal)
    (hfin : ∀ᵐ ξ ∂Q, g ξ ≠ ⊥ ∧ g ξ ≠ ⊤) (hi : Integrable (fun ξ => (g ξ).toReal) Q) :
    expect Q g = ((∫ ξ, (g ξ).toReal ∂Q : ℝ) : EReal) := by
  have h1 : ∫⁻ ξ, ENNReal.ofReal ((g ξ).toReal) ∂Q ≠ ∞ := hi.lintegral_lt_top.ne
  have h2 : ∫⁻ ξ, ENNReal.ofReal (-(g ξ).toReal) ∂Q ≠ ∞ := hi.neg.lintegral_lt_top.ne
  have e1 : ∫⁻ ξ, (g ξ).toENNReal ∂Q = ∫⁻ ξ, ENNReal.ofReal ((g ξ).toReal) ∂Q := by
    refine lintegral_congr_ae ?_
    filter_upwards [hfin] with ξ hξ
    rw [EReal.toENNReal_of_ne_top hξ.2]
  have e2 : ∫⁻ ξ, (-g ξ).toENNReal ∂Q = ∫⁻ ξ, ENNReal.ofReal (-(g ξ).toReal) ∂Q := by
    refine lintegral_congr_ae ?_
    filter_upwards [hfin] with ξ hξ
    rw [← EReal.coe_toReal hξ.2 hξ.1, ← EReal.coe_neg]
    simp
  unfold expect
  rw [e1, e2, if_neg h1, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
    EReal.coe_sub, EReal.coe_ennreal_toReal h1, EReal.coe_ennreal_toReal h2]

end Exp

section Rep
variable {n : ℕ} {Ξ : Type*} [TopologicalSpace Ξ] [MeasurableSpace Ξ] [OpensMeasurableSpace Ξ]
variable (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
  (h34 : Assumption3_4 f S)
include h34

theorem psi_measurable : Measurable (fun ξ => ⨅ x, f x ξ) := by
  refine measurable_of_Iio fun a => IsOpen.measurableSet ?_
  have : (fun ξ => ⨅ x, f x ξ) ⁻¹' Iio a = ⋃ x, {ξ | f x ξ < a} := by
    ext ξ; simp [iInf_lt_iff]
  rw [this]
  refine isOpen_iUnion fun x => ?_
  by_cases hx : x ∈ S
  · exact isOpen_lt (h34.continuous_of_mem x hx) continuous_const
  · have : {ξ | f x ξ < a} = ∅ := by
      ext ξ
      have h1 : f x ξ = ⊤ := by
        by_contra h
        exact hx ((h34.lt_top_iff x ξ).mp (lt_top_iff_ne_top.mpr h))
      simp [h1]
    rw [this]; exact isOpen_empty

theorem fenv_bound (m : ℕ) (y x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ S) (ξ : Ξ)
    (hψ : (⨅ x, f x ξ) ≠ ⊥) :
    fenv f m y ξ ≠ ⊥ ∧ fenv f m y ξ ≠ ⊤ ∧
      |(fenv f m y ξ).toReal| ≤ |(f x0 ξ).toReal| + (m : ℝ) * ‖y - x0‖ +
        ((-(⨅ x, f x ξ)).toENNReal).toReal := by
  have hlo := psi_le_fenv f m y ξ
  have hup := fenv_le f m y x0 ξ
  have hx0t : f x0 ξ ≠ ⊤ := ((h34.lt_top_iff x0 ξ).mpr hx0).ne
  have hψt : (⨅ x, f x ξ) ≠ ⊤ := ne_top_of_le_ne_top hx0t (iInf_le _ x0)
  have hb : fenv f m y ξ ≠ ⊥ := ne_bot_of_le_ne_bot hψ hlo
  have ht : fenv f m y ξ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hup
    rw [← EReal.coe_toReal hx0t (h34.ne_bot x0 ξ), ← EReal.coe_add]; exact EReal.coe_ne_top _
  refine ⟨hb, ht, ?_⟩
  set r := (fenv f m y ξ).toReal
  set p := (f x0 ξ).toReal
  set q := (⨅ x, f x ξ).toReal
  have er : fenv f m y ξ = r := (EReal.coe_toReal ht hb).symm
  have ep : f x0 ξ = p := (EReal.coe_toReal hx0t (h34.ne_bot x0 ξ)).symm
  have eq : (⨅ x, f x ξ) = q := (EReal.coe_toReal hψt hψ).symm
  have h1 : q ≤ r := by rw [er, eq] at hlo; exact_mod_cast hlo
  have h2 : r ≤ p + (m : ℝ) * ‖y - x0‖ := by
    rw [er, ep, ← EReal.coe_add] at hup; exact_mod_cast hup
  have h3 : ((-(⨅ x, f x ξ)).toENNReal).toReal = max (-q) 0 := by
    rw [eq, ← EReal.coe_neg, EReal.real_coe_toENNReal, ENNReal.toReal_ofReal']
  rw [h3]
  have := le_abs_self p
  have := le_max_left (-q) 0
  have := le_max_right (-q) 0
  have hc : 0 ≤ (m : ℝ) * ‖y - x0‖ := mul_nonneg (Nat.cast_nonneg m) (norm_nonneg _)
  rw [abs_le]; constructor <;> linarith [abs_nonneg p]

theorem rep (Q : Measure Ξ) [IsProbabilityMeasure Q] (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ S)
    (hψi : ∫⁻ ξ, (-(⨅ x, f x ξ)).toENNReal ∂Q ≠ ∞)
    (hi0 : Integrable (fun ξ => (f x0 ξ).toReal) Q) :
    (∀ m y, Integrable (fun ξ => (fenv f m y ξ).toReal) Q) ∧
    (∀ y, expectFn Q f y = ⨆ m, ((∫ ξ, (fenv f m y ξ).toReal ∂Q : ℝ) : EReal)) ∧
    (∀ m, Continuous (fun y => ∫ ξ, (fenv f m y ξ).toReal ∂Q)) ∧
    (∀ y, Monotone (fun m => ∫ ξ, (fenv f m y ξ).toReal ∂Q)) := by
  have hae : ∀ᵐ ξ ∂Q, (⨅ x, f x ξ) ≠ ⊥ := by
    have := ae_lt_top ((psi_measurable f S h34).neg.ereal_toENNReal) hψi
    filter_upwards [this] with ξ hξ
    intro h
    simp only [Pi.neg_apply] at hξ
    rw [h, EReal.neg_bot, EReal.toENNReal_top] at hξ
    exact lt_irrefl _ hξ
  have hi : ∀ m y, Integrable (fun ξ => (fenv f m y ξ).toReal) Q := by
    intro m y
    refine Integrable.mono' ((hi0.abs.add (integrable_const ((m : ℝ) * ‖y - x0‖))).add
      (integrable_toReal_of_lintegral_ne_top
        ((psi_measurable f S h34).neg.ereal_toENNReal.aemeasurable) hψi))
      (fenv_measurable f S h34 m y).ereal_toReal.aestronglyMeasurable ?_
    filter_upwards [hae] with ξ hξ
    rw [Real.norm_eq_abs]
    exact (fenv_bound f S h34 m y x0 hx0 ξ hξ).2.2
  have hfin : ∀ m y, ∀ᵐ ξ ∂Q, fenv f m y ξ ≠ ⊥ ∧ fenv f m y ξ ≠ ⊤ := by
    intro m y
    filter_upwards [hae] with ξ hξ
    exact ⟨(fenv_bound f S h34 m y x0 hx0 ξ hξ).1, (fenv_bound f S h34 m y x0 hx0 ξ hξ).2.1⟩
  have hcoe : ∀ m y, expect Q (fenv f m y) = ((∫ ξ, (fenv f m y ξ).toReal ∂Q : ℝ) : EReal) :=
    fun m y => expect_ae_coe Q _ (hfin m y) (hi m y)
  refine ⟨hi, ?_, ?_, ?_⟩
  · intro y
    have hP : ∀ m, ∫⁻ ξ, (fenv f m y ξ).toENNReal ∂Q ≠ ∞ := by
      intro m
      have : ∫⁻ ξ, (fenv f m y ξ).toENNReal ∂Q = ∫⁻ ξ, ENNReal.ofReal ((fenv f m y ξ).toReal) ∂Q := by
        refine lintegral_congr_ae ?_
        filter_upwards [hfin m y] with ξ hξ
        rw [EReal.toENNReal_of_ne_top hξ.2]
      rw [this]; exact (hi m y).lintegral_lt_top.ne
    have hlim : ∀ᵐ ξ ∂Q, Tendsto (fun m => fenv f m y ξ) atTop (𝓝 (f y ξ)) := by
      filter_upwards [hae] with ξ hξ
      rw [← fenv_iSup f S h34 y ξ hξ]
      exact tendsto_atTop_iSup (fenv_mono f y ξ)
    have ht := expect_tendsto Q (fun m => fenv f m y) (f y) (fun m => fenv_measurable f S h34 m y)
      (fun ξ => fenv_mono f y ξ) hlim _ (fun m ξ => psi_le_fenv f m y ξ) hψi hP
    have hmono : Monotone fun m => expect Q (fenv f m y) := fun i j hij =>
      expect_mono Q _ _ fun ξ => fenv_mono f y ξ hij
    have := tendsto_nhds_unique ht (tendsto_atTop_iSup hmono)
    unfold expectFn
    rw [this]
    simp only [hcoe]
  · intro m
    have hle : ∀ y y', ∫ ξ, (fenv f m y ξ).toReal ∂Q ≤
        ∫ ξ, (fenv f m y' ξ).toReal ∂Q + (m : ℝ) * ‖y - y'‖ := by
      intro y y'
      have := integral_mono_ae (hi m y) ((hi m y').add (integrable_const ((m : ℝ) * ‖y - y'‖))) (by
        filter_upwards [hfin m y, hfin m y'] with ξ h1 h2
        have h3 := fenv_lip f m y y' ξ
        rw [← EReal.coe_toReal h1.2 h1.1, ← EReal.coe_toReal h2.2 h2.1, ← EReal.coe_add] at h3
        exact_mod_cast h3)
      simp only [Pi.add_apply] at this
      rw [integral_add (hi m y') (integrable_const _), integral_const] at this
      simpa using this
    have hlip : LipschitzWith (m : NNReal) (fun y => ∫ ξ, (fenv f m y ξ).toReal ∂Q) := by
      refine LipschitzWith.of_dist_le_mul fun y y' => ?_
      rw [Real.dist_eq, dist_eq_norm, NNReal.coe_natCast, abs_le]
      have h1 := hle y y'
      have h2 := hle y' y
      rw [norm_sub_rev y' y] at h2
      constructor <;> linarith
    exact hlip.continuous
  · intro y i j hij
    refine integral_mono_ae (hi i y) (hi j y) ?_
    filter_upwards [hfin i y, hfin j y] with ξ h1 h2
    exact EReal.toReal_le_toReal (fenv_mono f y ξ hij) h1.1 h2.2

end Rep

section Tight
variable {Ξ : Type*} [TopologicalSpace Ξ] [PolishSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]

theorem integrable_of_tail (Q : Measure Ξ) [IsProbabilityMeasure Q] (h : Ξ → ℝ)
    (hc : Continuous h) (K : Set Ξ) (hK : IsCompact K)
    (ht : ∫⁻ ξ in Kᶜ, ENNReal.ofReal |h ξ| ∂Q ≠ ∞) : Integrable h Q := by
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  unfold HasFiniteIntegral
  have e : (fun ξ => ‖h ξ‖ₑ) = fun ξ => ENNReal.ofReal |h ξ| := by
    funext ξ; rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
  rw [e, ← lintegral_add_compl _ hKm]
  refine ENNReal.add_lt_top.mpr ⟨?_, lt_of_le_of_ne le_top ht⟩
  calc ∫⁻ ξ in K, ENNReal.ofReal |h ξ| ∂Q ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂Q := by
        refine setLIntegral_mono measurable_const fun ξ hξ => ?_
        exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hC ξ hξ)
    _ < ∞ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

end Tight

end DW6Aux


open DW6Aux in
theorem DW6Aux.lemma36_measure {n : ℕ} {Ξ : Type*} [TopologicalSpace Ξ] [PolishSpace Ξ]
    [MeasurableSpace Ξ] [BorelSpace Ξ]
    (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    (h34 : Assumption3_4 f S) (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (hint : ∀ x ∈ S, Integrable (fun ξ => (f x ξ).toReal) Q)
    (hψi : ∫⁻ ξ, (-(⨅ x, f x ξ)).toENNReal ∂Q ≠ ∞) :
    IsProperFn (expectFn Q f) ∧ LowerSemicontinuous (expectFn Q f) ∧
      effDom (expectFn Q f) = S ∧ ∀ x ∈ S, expectFn Q f x ≠ ⊥ ∧ expectFn Q f x ≠ ⊤ := by
  obtain ⟨x0, hx0⟩ := h34.nonempty_S
  obtain ⟨-, hrep, hcont, -⟩ := rep f S h34 Q x0 hx0 hψi (hint x0 hx0)
  have hcoe : ∀ x ∈ S, expectFn Q f x = ((∫ ξ, (f x ξ).toReal ∂Q : ℝ) : EReal) := by
    intro x hx
    simp only [expectFn]
    exact expect_ae_coe _ _ (Eventually.of_forall fun ξ =>
      ⟨h34.ne_bot x ξ, ((h34.lt_top_iff x ξ).mpr hx).ne⟩) (hint x hx)
  have htop : ∀ x ∉ S, expectFn Q f x = ⊤ := by
    intro x hx
    simp only [expectFn, expect]
    have : ∫⁻ ξ, (f x ξ).toENNReal ∂Q = ∞ := by
      have e : ∀ ξ, f x ξ = ⊤ := fun ξ => by
        by_contra h
        exact hx ((h34.lt_top_iff x ξ).mp (lt_top_iff_ne_top.mpr h))
      simp [e]
    rw [if_pos this]
  have hlow : expect Q (fun ξ => ⨅ x, f x ξ) ≠ ⊥ := by
    have hP : ∫⁻ ξ, ((⨅ x, f x ξ)).toENNReal ∂Q ≠ ∞ := by
      refine ne_top_of_le_ne_top (hint x0 hx0).lintegral_lt_top.ne (lintegral_mono fun ξ => ?_)
      refine (EReal.toENNReal_le_toENNReal (iInf_le _ x0)).trans ?_
      rw [EReal.toENNReal_of_ne_top ((h34.lt_top_iff x0 ξ).mpr hx0).ne]
    unfold expect
    rw [if_neg hP, ← EReal.coe_ennreal_toReal hP, ← EReal.coe_ennreal_toReal hψi, ← EReal.coe_sub]
    exact EReal.coe_ne_bot _
  have hbot : ∀ x, ⊥ < expectFn Q f x := fun x =>
    (bot_lt_iff_ne_bot.mpr hlow).trans_le (expect_mono _ _ _ fun ξ => iInf_le _ x)
  refine ⟨⟨hbot, x0, by rw [hcoe x0 hx0]; exact EReal.coe_ne_top _⟩, ?_, ?_, ?_⟩
  · have : expectFn Q f = fun y => ⨆ m, ((∫ ξ, (fenv f m y ξ).toReal ∂Q : ℝ) : EReal) :=
      funext hrep
    rw [this]
    exact lowerSemicontinuous_iSup fun m =>
      (continuous_coe_real_ereal.comp (hcont m)).lowerSemicontinuous
  · ext x
    simp only [effDom, Set.mem_setOf_eq]
    constructor
    · intro h
      by_contra hx
      rw [htop x hx] at h; exact lt_irrefl _ h
    · intro hx
      rw [hcoe x hx]; exact EReal.coe_lt_top _
  · intro x hx
    exact ⟨(hbot x).ne', by rw [hcoe x hx]; exact EReal.coe_ne_top _⟩

open DW6Aux in
theorem solution {n : ℕ} {Ξ : Type*} [TopologicalSpace Ξ] [PolishSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P]
    {Z : Type*} [mZ : MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (𝔽 : Filtration ℕ mZ) (Pν : ℕ → Z → Measure Ξ)
    (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    (h34 : Assumption3_4 f S) (h35 : Assumption3_5 f S P μ 𝔽 Pν) :
    ∃ Z₀ : Set Z, MeasurableSet Z₀ ∧ μ Z₀ = 1 ∧ ∀ ζ ∈ Z₀,
      (IsProperFn (expectFn P f) ∧ LowerSemicontinuous (expectFn P f) ∧
        effDom (expectFn P f) = S ∧ ∀ x ∈ S, expectFn P f x ≠ ⊥ ∧ expectFn P f x ≠ ⊤) ∧
      ∀ k, IsProperFn (expectFn (Pν k ζ) f) ∧ LowerSemicontinuous (expectFn (Pν k ζ) f) ∧
        effDom (expectFn (Pν k ζ) f) = S ∧
        ∀ x ∈ S, expectFn (Pν k ζ) f x ≠ ⊥ ∧ expectFn (Pν k ζ) f x ≠ ⊤ := by
  obtain ⟨x0, hx0⟩ := h34.nonempty_S
  have hcont : ∀ x ∈ S, Continuous fun ξ => (f x ξ).toReal := by
    intro x hx
    refine EReal.continuousOn_toReal.comp_continuous (h34.continuous_of_mem x hx) fun ξ => ?_
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h34.ne_bot x ξ, ((h34.lt_top_iff x ξ).mpr hx).ne⟩
  -- ψ⁻ integrable from (3.12)
  have hneg : ∀ (Q : Measure Ξ) [IsProbabilityMeasure Q],
      Integrable (fun ξ => (f x0 ξ).toReal) Q →
      ⊥ < expect Q (fun ξ => ⨅ x, f x ξ) → ∫⁻ ξ, (-(⨅ x, f x ξ)).toENNReal ∂Q ≠ ∞ := by
    intro Q _ hi hl
    have hP : ∫⁻ ξ, ((⨅ x, f x ξ)).toENNReal ∂Q ≠ ∞ := by
      refine ne_top_of_le_ne_top hi.lintegral_lt_top.ne (lintegral_mono fun ξ => ?_)
      refine (EReal.toENNReal_le_toENNReal (iInf_le _ x0)).trans ?_
      rw [EReal.toENNReal_of_ne_top ((h34.lt_top_iff x0 ξ).mpr hx0).ne]
    unfold expect at hl
    rw [if_neg hP] at hl
    intro hN
    rw [hN, EReal.coe_ennreal_top, EReal.sub_top] at hl
    exact lt_irrefl _ hl
  have hae : ∀ᵐ ζ ∂μ,
      ((IsProperFn (expectFn P f) ∧ LowerSemicontinuous (expectFn P f) ∧
        effDom (expectFn P f) = S ∧ ∀ x ∈ S, expectFn P f x ≠ ⊥ ∧ expectFn P f x ≠ ⊤) ∧
      ∀ k, IsProperFn (expectFn (Pν k ζ) f) ∧ LowerSemicontinuous (expectFn (Pν k ζ) f) ∧
        effDom (expectFn (Pν k ζ) f) = S ∧
        ∀ x ∈ S, expectFn (Pν k ζ) f x ≠ ⊥ ∧ expectFn (Pν k ζ) f x ≠ ⊤) := by
    filter_upwards [h35.ae] with ζ hζ
    obtain ⟨-, htail, hlowP, hlowk⟩ := hζ
    have hintP : ∀ x ∈ S, Integrable (fun ξ => (f x ξ).toReal) P := by
      intro x hx
      obtain ⟨K, hK, h1, -⟩ := htail x hx 1 one_pos
      exact integrable_of_tail P _ (hcont x hx) K hK (ne_top_of_lt h1)
    refine ⟨lemma36_measure f S h34 P hintP (hneg P (hintP x0 hx0) hlowP), fun k => ?_⟩
    haveI := h35.isProb k ζ
    have hintk : ∀ x ∈ S, Integrable (fun ξ => (f x ξ).toReal) (Pν k ζ) := by
      intro x hx
      obtain ⟨K, hK, -, h2⟩ := htail x hx 1 one_pos
      exact integrable_of_tail _ _ (hcont x hx) K hK (ne_top_of_lt (h2 k))
    exact lemma36_measure f S h34 (Pν k ζ) hintk (hneg _ (hintk x0 hx0) (hlowk k))
  set A := {ζ | ¬ (((IsProperFn (expectFn P f) ∧ LowerSemicontinuous (expectFn P f) ∧
        effDom (expectFn P f) = S ∧ ∀ x ∈ S, expectFn P f x ≠ ⊥ ∧ expectFn P f x ≠ ⊤) ∧
      ∀ k, IsProperFn (expectFn (Pν k ζ) f) ∧ LowerSemicontinuous (expectFn (Pν k ζ) f) ∧
        effDom (expectFn (Pν k ζ) f) = S ∧
        ∀ x ∈ S, expectFn (Pν k ζ) f x ≠ ⊥ ∧ expectFn (Pν k ζ) f x ≠ ⊤))} with hA
  have hA0 : μ A = 0 := by rw [ae_iff] at hae; exact hae
  refine ⟨(toMeasurable μ A)ᶜ, (measurableSet_toMeasurable μ A).compl, ?_, ?_⟩
  · rw [prob_compl_eq_one_sub (measurableSet_toMeasurable μ A), measure_toMeasurable, hA0,
      tsub_zero]
  · intro ζ hζ
    have : ζ ∉ A := fun h' => hζ (subset_toMeasurable μ A h')
    rw [hA, Set.mem_setOf_eq, not_not] at this
    exact this
