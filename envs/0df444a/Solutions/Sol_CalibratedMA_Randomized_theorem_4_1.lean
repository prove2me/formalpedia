-- Prove2me | solution 1 for CalibratedMA.Randomized.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Aaron
-- created : 2026-11-13T18:55:04.874206+00:00
-- url     : https://prove2.me/submissions/0cb8ef32-a014-455e-8d59-70616cedc81b

-- Complete proof of STOC 2027 submission 900, Theorem 4.1.
-- Local development helpers are included below; imports are public platform modules only.
import Definitions.Def_CalibratedMA_Randomized_Algorithm1
import Definitions.Def_CalibratedMA_Randomized_OnlineRule
import Definitions.Def_CalibratedMA_Randomized_Rounding
import Definitions.Def_CalibratedMA_Randomized_Setting
import Mathlib
import Theorems.Thm_CalibratedMA_Randomized_eq_2
import Theorems.Thm_CalibratedMA_Randomized_eq_4
import Theorems.Thm_CalibratedMA_Randomized_lemma_3_1
import Theorems.Thm_CalibratedMA_Randomized_lemma_3_2
import Theorems.Thm_CalibratedMA_Randomized_lemma_3_3
import Theorems.Thm_CalibratedMA_Randomized_lemma_3_4

-- Solutions.CalibrationLaw
section

open MeasureTheory ProbabilityTheory

namespace CalibratedMA.Randomized.CalibrationLaw

variable {X : Type*} [MeasurableSpace X]

/-- The law obtained by attaching the input and label to a sampled prediction
depends measurably on the labeled example. -/
lemma measurable_jointKernel (Q : X → Measure ℝ) (hQ : IsRandomizedPredictor Q) :
    Measurable (fun z : X × ℝ => (Q z.1).map (fun p => (z.1, z.2, p))) := by
  let κ : Kernel (X × ℝ) ℝ := ⟨fun z => Q z.1, hQ.1.comp measurable_fst⟩
  let : IsMarkovKernel κ := ⟨fun z => (hQ.2 z.1).1⟩
  let f : (X × ℝ) × ℝ → X × ℝ × ℝ := fun zp => (zp.1.1, zp.1.2, zp.2)
  have hf : Measurable f := by fun_prop
  let η : Kernel (X × ℝ) (X × ℝ × ℝ) := (Kernel.id ×ₖ κ).map f
  have heq : (fun z : X × ℝ => (Q z.1).map (fun p => (z.1, z.2, p))) = η := by
    funext z
    apply Measure.ext
    intro A hA
    change (Q z.1).map (fun p => (z.1, z.2, p)) A = ((Kernel.id ×ₖ κ).map f) z A
    rw [Kernel.map_apply' _ hf _ hA, Kernel.id_prod_apply' _ _ (hf hA)]
    rw [Measure.map_apply (by fun_prop) hA]
    rfl
  rw [heq]
  exact η.measurable

/-- An admissible predictor and a probability data distribution induce a probability joint law. -/
lemma jointLaw_isProbabilityMeasure (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (Q : X → Measure ℝ) (hQ : IsRandomizedPredictor Q) :
    IsProbabilityMeasure (jointLaw D Q) := by
  apply isProbabilityMeasure_bind (measurable_jointKernel Q hQ).aemeasurable
  apply Filter.Eventually.of_forall
  intro z
  let : IsProbabilityMeasure (Q z.1) := (hQ.2 z.1).1
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The joint law retains the label support and the predictor's support. -/
lemma jointLaw_support (D : Measure (X × ℝ))
    (Q : X → Measure ℝ) (hD : ∀ᵐ z ∂D, z.2 ∈ Set.Icc (0 : ℝ) 1)
    (hQ : IsRandomizedPredictor Q) :
    ∀ᵐ w ∂jointLaw D Q,
      w.2.1 ∈ Set.Icc (0 : ℝ) 1 ∧ w.2.2 ∈ Set.Icc (0 : ℝ) 1 := by
  have hA : MeasurableSet {w : X × ℝ × ℝ |
      w.2.1 ∈ Set.Icc (0 : ℝ) 1 ∧ w.2.2 ∈ Set.Icc (0 : ℝ) 1} := by
    exact (measurableSet_Icc.preimage (by fun_prop)).inter
      (measurableSet_Icc.preimage (by fun_prop))
  rw [ae_iff]
  unfold jointLaw
  change (D.bind (fun z : X × ℝ => (Q z.1).map (fun p => (z.1, z.2, p))))
    ({w : X × ℝ × ℝ | w.2.1 ∈ Set.Icc (0 : ℝ) 1 ∧ w.2.2 ∈ Set.Icc (0 : ℝ) 1}ᶜ) = 0
  rw [Measure.bind_apply hA.compl (measurable_jointKernel Q hQ).aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hD] with z hz
  rw [Measure.map_apply (by fun_prop) hA.compl]
  simpa only [Set.preimage_compl, Set.preimage_ofPred_eq, hz, true_and, Pi.zero_apply,
    Set.ofPred_mem_eq]
    using (hQ.2 z.1).2

/-- The bounded residual is integrable under the actual joint law. -/
lemma integrable_residual (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (Q : X → Measure ℝ) (hD : ∀ᵐ z ∂D, z.2 ∈ Set.Icc (0 : ℝ) 1)
    (hQ : IsRandomizedPredictor Q) :
    Integrable (fun w : X × ℝ × ℝ => w.2.1 - w.2.2) (jointLaw D Q) := by
  let : IsProbabilityMeasure (jointLaw D Q) := jointLaw_isProbabilityMeasure D Q hQ
  apply (integrable_const (1 : ℝ)).mono'
    ((show Measurable (fun w : X × ℝ × ℝ => w.2.1 - w.2.2) by fun_prop).aestronglyMeasurable)
  filter_upwards [jointLaw_support D Q hD hQ] with w hw
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [hw.1.1, hw.2.2], by linarith [hw.1.2, hw.2.1]⟩

end CalibratedMA.Randomized.CalibrationLaw

end

-- Solutions.MainEmpirical
section

open MeasureTheory
open scoped ENNReal

namespace CalibratedMA.Randomized.MainEmpirical

noncomputable def empiricalScores (n : ℕ) (S : Fin n → ℝ) : Measure ℝ :=
  (n : ℝ≥0∞)⁻¹ • ∑ t : Fin n, Measure.dirac (S t)

lemma empiricalScores_probability (n : ℕ) (hn : 1 ≤ n) (S : Fin n → ℝ) :
    IsProbabilityMeasure (empiricalScores n S) := by
  refine ⟨?_⟩
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simpa [empiricalScores, Measure.smul_apply] using
    ENNReal.inv_mul_cancel hn0 (by simp : (n : ℝ≥0∞) ≠ ⊤)

lemma empiricalScores_support (n : ℕ) (S : Fin n → ℝ)
    (hS : ∀ t, S t ∈ Set.Icc (0 : ℝ) 1) :
    empiricalScores n S (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  have hdirac (t : Fin n) : Measure.dirac (S t) (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
    simp [Measure.dirac_apply', measurableSet_Icc.compl, hS t]
  simp [empiricalScores, Measure.smul_apply, hdirac]

lemma integral_empiricalScores (n : ℕ) (S : Fin n → ℝ) (f : ℝ → ℝ) :
    (∫ s, f s ∂empiricalScores n S) = (1 / (n : ℝ)) * ∑ t : Fin n, f (S t) := by
  have hi : ∀ t ∈ (Finset.univ : Finset (Fin n)), Integrable f (Measure.dirac (S t)) :=
    fun _ _ => integrable_dirac (by simp)
  rw [empiricalScores, integral_smul_measure, integral_finsetSum_measure hi]
  simp [integral_dirac, smul_eq_mul, one_div]

lemma integrable_roundMeasure (M : ℕ) (γ : ℕ → ℝ) (s : ℝ) (h : ℝ → ℝ) :
    Integrable h (roundMeasure M γ s) := by
  apply Integrable.add_measure
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma rounded_residual_split (M : ℕ) (γ : ℕ → ℝ) (h : ℝ → ℝ) (s y : ℝ) :
    (∫ p, h p * (y - p) ∂roundMeasure M γ s) =
      liftTest M γ h s * (y - s) + ∫ p, h p * (s - p) ∂roundMeasure M γ s := by
  rw [liftTest, ← integral_mul_const,
    ← integral_add (integrable_roundMeasure M γ s (fun p => h p * (y - s)))
      (integrable_roundMeasure M γ s (fun p => h p * (s - p)))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => by ring)

lemma empirical_rounding_residual_le (K M n : ℕ) (hn : 1 ≤ n) (γ : ℕ → ℝ)
    (hΓ : IsGridPartition K M γ) (S : Fin n → ℝ) (hS : ∀ t, S t ∈ Set.Icc (0 : ℝ) 1)
    (h : ℝ → ℝ) (hh : ∀ j ≤ M, h (γ j) ∈ Set.Icc (-1 : ℝ) 1) :
    |(1 / (n : ℝ)) * ∑ t : Fin n, (∫ p, h p * (S t - p) ∂roundMeasure M γ (S t))| ≤
      RoundErr (empiricalScores n S) M γ := by
  let : IsProbabilityMeasure (empiricalScores n S) := empiricalScores_probability n hn S
  have hlub := (lemma_3_3 K M γ hΓ (empiricalScores n S) (empiricalScores_support n S hS)).1
  rw [← integral_empiricalScores n S (fun s => ∫ p, h p * (s - p) ∂roundMeasure M γ s)]
  exact hlub.1 ⟨h, hh, rfl⟩

lemma empirical_calibration_bound (K M n : ℕ) (hn : 1 ≤ n) (γ : ℕ → ℝ)
    (hΓ : IsGridPartition K M γ) (S Y : Fin n → ℝ) (hS : ∀ t, S t ∈ Set.Icc (0 : ℝ) 1)
    (h : ℝ → ℝ) (hh : ∀ j ≤ M, h (γ j) ∈ Set.Icc (-1 : ℝ) 1)
    (B : ℝ) (hB : |(1 / (n : ℝ)) * ∑ t : Fin n, liftTest M γ h (S t) * (Y t - S t)| ≤ B) :
    |(1 / (n : ℝ)) * ∑ t : Fin n, (∫ p, h p * (Y t - p) ∂roundMeasure M γ (S t))| ≤
      B + RoundErr (empiricalScores n S) M γ := by
  rw [Finset.sum_congr rfl (fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) =>
    rounded_residual_split M γ h (S t) (Y t))]
  rw [Finset.sum_add_distrib, mul_add]
  exact (abs_add_le _ _).trans
    (add_le_add hB (empirical_rounding_residual_le K M n hn γ hΓ S hS h hh))

end CalibratedMA.Randomized.MainEmpirical

end

-- Solutions.MainCandidatesGrid
section

namespace CalibratedMA.Randomized.MainCandidatesGrid

lemma sorted_getD_eq_orderEmb (S : Finset ℕ) (K j : ℕ) (hj : j < S.card) :
    (S.sort (· ≤ ·)).getD j K = S.orderEmbOfFin rfl ⟨j, hj⟩ := by
  rw [Finset.orderEmbOfFin_apply]
  exact List.getD_eq_getElem _ _ (by simpa only [Finset.length_sort] using hj)

lemma card_ge_two (K : ℕ) (S : Finset ℕ) (hK : 1 ≤ K)
    (hzero : 0 ∈ S) (hlast : K ∈ S) : 2 ≤ S.card := by
  have hp : ({0, K} : Finset ℕ) ⊆ S := by simp [Finset.insert_subset_iff, hzero, hlast]
  have hc := Finset.card_le_card hp
  have hn : (0 : ℕ) ≠ K := by omega
  rwa [Finset.card_pair hn] at hc

/-- Enumerating an endpoint-containing set of grid indices produces a valid partition. -/
lemma partitionOfIndexSet_isGridPartition (K : ℕ) (S : Finset ℕ) (hK : 1 ≤ K)
    (hS : S ⊆ Finset.range (K + 1)) (hzero : 0 ∈ S) (hlast : K ∈ S) :
    IsGridPartition K (partitionOfIndexSet K S).1 (partitionOfIndexSet K S).2 := by
  have hc2 := card_ge_two K S hK hzero hlast
  have hc : 0 < S.card := by omega
  have hlastidx : S.card - 1 < S.card := by omega
  have hKreal : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hmin : S.min' (Finset.card_pos.mp hc) = 0 :=
    le_antisymm (Finset.min'_le _ _ hzero) (Nat.zero_le _)
  have hmax : S.max' (Finset.card_pos.mp hc) = K := by
    apply le_antisymm
    · have hm := hS (Finset.max'_mem _ (Finset.card_pos.mp hc))
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    · exact Finset.le_max' _ _ hlast
  change IsGridPartition K (S.card - 1)
    (fun j => ((S.sort (· ≤ ·)).getD j K : ℝ) / K)
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [sorted_getD_eq_orderEmb S K 0 hc, Finset.orderEmbOfFin_zero rfl hc, hmin]
    simp
  · dsimp only
    rw [sorted_getD_eq_orderEmb S K (S.card - 1) hlastidx,
      Finset.orderEmbOfFin_last rfl hc, hmax]
    exact div_self (ne_of_gt hKreal)
  · intro j hj
    have hj0 : j < S.card := by omega
    have hj1 : j + 1 < S.card := by omega
    dsimp only
    apply (div_lt_div_iff_of_pos_right hKreal).2
    rw [sorted_getD_eq_orderEmb S K j hj0, sorted_getD_eq_orderEmb S K (j + 1) hj1]
    exact_mod_cast (S.orderEmbOfFin rfl).strictMono (show (⟨j, hj0⟩ : Fin S.card) < ⟨j + 1, hj1⟩ by simp)
  · intro j hj
    have hjc : j < S.card := by omega
    refine ⟨(S.sort (· ≤ ·)).getD j K, ?_, rfl⟩
    rw [sorted_getD_eq_orderEmb S K j hjc]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp (hS (Finset.orderEmbOfFin_mem S rfl ⟨j, hjc⟩)))

lemma sorted_getD_eq_orderEmb_of_card (S : Finset ℕ) (K n : ℕ) (hc : S.card = n)
    (j : Fin n) :
    (S.sort (· ≤ ·)).getD j K = S.orderEmbOfFin hc j := by
  rw [Finset.orderEmbOfFin_apply]
  exact List.getD_eq_getElem _ _ (by rw [Finset.length_sort, hc]; exact j.isLt)

/-- Every valid grid partition has a finite index-set representation with exactly
its original number of knots, in the original increasing order. -/
lemma exists_indexSet (K L : ℕ) (γ : ℕ → ℝ) (hK : 1 ≤ K)
    (hΓ : IsGridPartition K L γ) :
    ∃ S : Finset ℕ,
      S ⊆ Finset.range (K + 1) ∧ 0 ∈ S ∧ K ∈ S ∧ S.card = L + 1 ∧
        ∀ j ≤ L, (partitionOfIndexSet K S).2 j = γ j := by
  classical
  have hKreal : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKreal
  choose f hfbound hfval using
    (fun j : Fin (L + 1) => hΓ.2.2.2 (j : ℕ) (by omega))
  have hγmono : StrictMonoOn γ (Set.Iic L) :=
    strictMonoOn_Iic_of_lt_succ (fun j hj => hΓ.2.2.1 j hj)
  have hfmono : StrictMono f := by
    intro i j hij
    have hh := hγmono (show (i : ℕ) ≤ L by omega) (show (j : ℕ) ≤ L by omega) hij
    rw [hfval i, hfval j] at hh
    exact_mod_cast (div_lt_div_iff_of_pos_right hKreal).mp hh
  let S : Finset ℕ := Finset.univ.image f
  have hfS : ∀ j, f j ∈ S := by
    intro j
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  have hcard : S.card = L + 1 := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ hfmono.injective]
    simp
  have hS : S ⊆ Finset.range (K + 1) := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (by have hh := hfbound j; omega)
  have hf0 : f ⟨0, by omega⟩ = 0 := by
    have hh := hfval ⟨0, by omega⟩
    change γ 0 = (f ⟨0, by omega⟩ : ℝ) / K at hh
    rw [hΓ.1] at hh
    have hmul := (div_eq_iff hKne).mp hh.symm
    have hz : (f ⟨0, by omega⟩ : ℝ) = 0 := by simpa using hmul
    exact_mod_cast hz
  have hfL : f ⟨L, by omega⟩ = K := by
    have hh := hfval ⟨L, by omega⟩
    change γ L = (f ⟨L, by omega⟩ : ℝ) / K at hh
    rw [hΓ.2.1] at hh
    have hmul := (div_eq_iff hKne).mp hh.symm
    have hz : (f ⟨L, by omega⟩ : ℝ) = K := by simpa using hmul
    exact_mod_cast hz
  have hzero : 0 ∈ S := hf0 ▸ hfS ⟨0, by omega⟩
  have hlast : K ∈ S := hfL ▸ hfS ⟨L, by omega⟩
  have hf_order : f = S.orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique hcard hfS hfmono
  refine ⟨S, hS, hzero, hlast, hcard, ?_⟩
  intro j hj
  change ((S.sort (· ≤ ·)).getD j K : ℝ) / K = γ j
  have hjfin : j < L + 1 := by omega
  rw [sorted_getD_eq_orderEmb_of_card S K (L + 1) hcard ⟨j, hjfin⟩]
  rw [← hf_order]
  exact (hfval ⟨j, hjfin⟩).symm

/-- The selected index depends only on the partition's listed left endpoints. -/
lemma roundIndex_congr (L : ℕ) (γ δ : ℕ → ℝ)
    (hγδ : ∀ j < L, γ j = δ j) (s : ℝ) :
    roundIndex L γ s = roundIndex L δ s := by
  unfold roundIndex
  have hfilter : ((Finset.range L).filter (fun j => γ j ≤ clamp01 s)) =
      (Finset.range L).filter (fun j => δ j ≤ clamp01 s) := by
    apply Finset.filter_congr
    intro j hj
    rw [hγδ j (Finset.mem_range.mp hj)]
  rw [hfilter]

/-- Agreement at the finitely many knots gives equality of rounding laws for every real score. -/
lemma roundMeasure_congr (L : ℕ) (γ δ : ℕ → ℝ) (hL : 0 < L)
    (hγδ : ∀ j ≤ L, γ j = δ j) (s : ℝ) :
    roundMeasure L γ s = roundMeasure L δ s := by
  have hidx := roundIndex_congr L γ δ (fun j hj => hγδ j hj.le) s
  have hi : roundIndex L δ s < L := by
    unfold roundIndex
    apply (Finset.sup_lt_iff hL).2
    intro j hj
    exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have he0 := hγδ (roundIndex L δ s) hi.le
  have he1 := hγδ (roundIndex L δ s + 1) (by omega)
  have hw : roundWeight L γ s = roundWeight L δ s := by
    simp only [roundWeight, hidx, he0, he1]
  simp only [roundMeasure, hidx, hw, he0, he1]

/-- Agreement on the finite knot sequence gives equality of all lifted tests,
including their clamped extension outside `[0,1]`. -/
lemma liftTest_congr (L : ℕ) (γ δ : ℕ → ℝ) (hL : 0 < L)
    (hγδ : ∀ j ≤ L, γ j = δ j) (h : ℝ → ℝ) :
    liftTest L γ h = liftTest L δ h := by
  funext s
  unfold liftTest
  rw [roundMeasure_congr L γ δ hL hγδ s]

end CalibratedMA.Randomized.MainCandidatesGrid

end

-- Solutions.MainCandidatesRegularity
section

open MeasureTheory

namespace CalibratedMA.Randomized.MainCandidatesRegularity

lemma clamp01_mem (s : ℝ) : clamp01 s ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma clamp01_eq_of_mem {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) : clamp01 s = s := by
  simp only [clamp01, min_eq_right hs.2, max_eq_right hs.1]

@[simp] lemma clamp01_idem (s : ℝ) : clamp01 (clamp01 s) = clamp01 s :=
  clamp01_eq_of_mem (clamp01_mem s)

lemma continuous_clamp01 : Continuous clamp01 := by
  unfold clamp01
  fun_prop

lemma roundMeasure_clamp (M : ℕ) (γ : ℕ → ℝ) (s : ℝ) :
    roundMeasure M γ (clamp01 s) = roundMeasure M γ s := by
  simp only [roundMeasure, roundWeight, roundIndex, clamp01_idem]

lemma liftTest_clamp (M : ℕ) (γ : ℕ → ℝ) (h : ℝ → ℝ) (s : ℝ) :
    liftTest M γ h (clamp01 s) = liftTest M γ h s := by
  unfold liftTest
  rw [roundMeasure_clamp]

/-- Continuity on the compact score interval extends through the clamping convention. -/
lemma continuous_liftTest (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ)
    (h : ℝ → ℝ) : Continuous (liftTest M γ h) := by
  have hc := (lemma_3_2 K M γ hΓ h).2.comp_continuous continuous_clamp01 clamp01_mem
  convert hc using 1
  funext s
  exact (liftTest_clamp M γ h s).symm

lemma measurable_filtered_sup (S : Finset ℕ) (γ : ℕ → ℝ) :
    Measurable (fun s : ℝ => (S.filter (fun j => γ j ≤ clamp01 s)).sup id) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      have hm : MeasurableSet {s : ℝ | γ i ≤ clamp01 s} :=
        measurableSet_le measurable_const continuous_clamp01.measurable
      have heq : (fun s : ℝ => ((insert i S).filter (fun j => γ j ≤ clamp01 s)).sup id) =
          fun s => if γ i ≤ clamp01 s then i ⊔ (S.filter (fun j => γ j ≤ clamp01 s)).sup id
            else (S.filter (fun j => γ j ≤ clamp01 s)).sup id := by
        funext s
        by_cases hs : γ i ≤ clamp01 s <;> simp [Finset.filter_insert, hs, Finset.sup_insert]
      rw [heq]
      exact Measurable.ite hm (measurable_const.sup ih) ih

lemma measurable_roundIndex (M : ℕ) (γ : ℕ → ℝ) : Measurable (roundIndex M γ) :=
  measurable_filtered_sup (Finset.range M) γ

lemma measurable_roundWeight (M : ℕ) (γ : ℕ → ℝ) : Measurable (roundWeight M γ) := by
  have hj := measurable_roundIndex M γ
  have hleft : Measurable (fun s => γ (roundIndex M γ s)) :=
    (measurable_of_countable γ).comp hj
  have hright : Measurable (fun s => γ (roundIndex M γ s + 1)) :=
    (measurable_of_countable (fun j : ℕ => γ (j + 1))).comp hj
  unfold roundWeight
  exact measurable_const.max (measurable_const.min
    ((continuous_clamp01.measurable.sub hleft).div (hright.sub hleft)))

/-- The rounding law is a measurable measure-valued function for arbitrary knot lists. -/
lemma measurable_roundMeasure (M : ℕ) (γ : ℕ → ℝ) : Measurable (roundMeasure M γ) := by
  have hj := measurable_roundIndex M γ
  have hw := measurable_roundWeight M γ
  have hleft : Measurable (fun s => γ (roundIndex M γ s)) :=
    (measurable_of_countable γ).comp hj
  have hright : Measurable (fun s => γ (roundIndex M γ s + 1)) :=
    (measurable_of_countable (fun j : ℕ => γ (j + 1))).comp hj
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp only [roundMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact ((measurable_const.sub hw).ennreal_ofReal.mul
      ((Measure.measurable_coe hA).comp (Measure.measurable_dirac.comp hleft))).add
    (hw.ennreal_ofReal.mul
      ((Measure.measurable_coe hA).comp (Measure.measurable_dirac.comp hright)))

lemma roundWeight_mem (M : ℕ) (γ : ℕ → ℝ) (s : ℝ) :
    roundWeight M γ s ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Clamped weights always define a probability measure. -/
lemma roundMeasure_probability (M : ℕ) (γ : ℕ → ℝ) (s : ℝ) :
    IsProbabilityMeasure (roundMeasure M γ s) := by
  apply isProbabilityMeasure_iff.mpr
  simp only [roundMeasure, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr (roundWeight_mem M γ s).2)
    (roundWeight_mem M γ s).1]
  simp

lemma grid_point_mem (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ)
    (j : ℕ) (hj : j ≤ M) : γ j ∈ Set.Icc (0 : ℝ) 1 := by
  have hmono : MonotoneOn γ (Set.Iic M) :=
    (strictMonoOn_Iic_of_lt_succ (fun i hi => hΓ.2.2.1 i hi)).monotoneOn
  constructor
  · simpa only [hΓ.1] using hmono (show 0 ≤ M by omega) hj (Nat.zero_le j)
  · simpa only [hΓ.2.1] using hmono hj (le_refl M) hj

lemma selected_index_lt (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ) (s : ℝ) :
    roundIndex M γ s < M := by
  have hM : 0 < M := by
    by_contra h
    have heq : M = 0 := by omega
    have hz := hΓ.1
    have ho := hΓ.2.1
    rw [heq, hz] at ho
    norm_num at ho
  unfold roundIndex
  apply (Finset.sup_lt_iff hM).2
  intro j hj
  exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1

/-- Every rounded value lies in `[0,1]`, including on clamped input scores. -/
lemma roundMeasure_support (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ) (s : ℝ) :
    roundMeasure M γ s (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  have hj := selected_index_lt K M γ hΓ s
  have hleft := grid_point_mem K M γ hΓ (roundIndex M γ s) (by omega)
  have hright := grid_point_mem K M γ hΓ (roundIndex M γ s + 1) (by omega)
  simp only [roundMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [Measure.dirac_apply' _ measurableSet_Icc.compl,
    Measure.dirac_apply' _ measurableSet_Icc.compl]
  simp [hleft, hright]

lemma integral_roundMeasure_test (M : ℕ) (γ : ℕ → ℝ) (s : ℝ) (h : ℝ → ℝ) :
    ∫ p, h p ∂(roundMeasure M γ s) =
      (1 - roundWeight M γ s) * h (γ (roundIndex M γ s)) +
        roundWeight M γ s * h (γ (roundIndex M γ s + 1)) := by
  have hw0 := (roundWeight_mem M γ s).1
  have hw1 := (roundWeight_mem M γ s).2
  have ha : Integrable h
      (ENNReal.ofReal (1 - roundWeight M γ s) • Measure.dirac (γ (roundIndex M γ s))) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hb : Integrable h
      (ENNReal.ofReal (roundWeight M γ s) • Measure.dirac (γ (roundIndex M γ s + 1))) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [roundMeasure, integral_add_measure ha hb]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hw0,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hw1), smul_eq_mul]

lemma liftTest_mem (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ)
    (h : ℝ → ℝ) (hh : ∀ j ≤ M, h (γ j) ∈ Set.Icc (-1 : ℝ) 1) (s : ℝ) :
    liftTest M γ h s ∈ Set.Icc (-1 : ℝ) 1 := by
  have hj := selected_index_lt K M γ hΓ s
  have hl := hh (roundIndex M γ s) (by omega)
  have hr := hh (roundIndex M γ s + 1) (by omega)
  have hw := roundWeight_mem M γ s
  rw [liftTest, integral_roundMeasure_test]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hw.2) (show 0 ≤ h (γ (roundIndex M γ s)) + 1 by linarith [hl.1]),
      mul_nonneg hw.1 (show 0 ≤ h (γ (roundIndex M γ s + 1)) + 1 by linarith [hr.1])]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hw.2) (show 0 ≤ 1 - h (γ (roundIndex M γ s)) by linarith [hl.2]),
      mul_nonneg hw.1 (show 0 ≤ 1 - h (γ (roundIndex M γ s + 1)) by linarith [hr.2])]

lemma signTest_mem (K : ℕ) (T : Finset ℕ) (s : ℝ) :
    signTest K T s ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold signTest
  split_ifs <;> norm_num

/-- Every lifted candidate is measurable, continuous on the score interval, and bounded. -/
lemma liftedClass_regular (K M : ℕ) (hK : 1 ≤ K) (a : ℝ → ℝ)
    (ha : a ∈ liftedClass K M) :
    Measurable a ∧ ContinuousOn a (Set.Icc (0 : ℝ) 1) ∧
      ∀ s : ℝ, a s ∈ Set.Icc (-1 : ℝ) 1 := by
  classical
  unfold liftedClass at ha
  rcases Finset.mem_image.mp ha with ⟨⟨S, T⟩, hST, rfl⟩
  rcases Finset.mem_product.mp hST with ⟨hS, hT⟩
  rcases Finset.mem_filter.mp hS with ⟨hSpow, hzero, hlast, hcard⟩
  have hΓ := MainCandidatesGrid.partitionOfIndexSet_isGridPartition K S hK
    (Finset.mem_powerset.mp hSpow) hzero hlast
  exact ⟨(continuous_liftTest K _ _ hΓ _).measurable,
    (lemma_3_2 K _ _ hΓ _).2,
    fun s => liftTest_mem K _ _ hΓ _ (fun j hj => signTest_mem K T _) s⟩

/-- The two-endpoint partition provides at least one candidate whenever the parameters are positive. -/
lemma liftedClass_nonempty (K M : ℕ) (hK : 1 ≤ K) (hM : 1 ≤ M) :
    (liftedClass K M).Nonempty := by
  classical
  unfold liftedClass
  apply Finset.image_nonempty.mpr
  apply Finset.nonempty_product.mpr
  constructor
  · refine ⟨{0, K}, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · apply Finset.mem_powerset.mpr
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> simp [Finset.mem_range]
    · refine ⟨by simp, by simp, ?_⟩
      have hne : (0 : ℕ) ≠ K := by omega
      rw [Finset.card_pair hne]
      omega
  · exact ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩

variable {X : Type*}

lemma testFamily_measurable [MeasurableSpace X] (G : Finset (X → ℝ))
    (A : Finset (ℝ → ℝ)) (hG : ∀ g ∈ G, Measurable g)
    (hA : ∀ a ∈ A, Measurable a) (ϕ : X → ℝ → ℝ) (hϕ : ϕ ∈ testFamily G A) :
    Measurable (Function.uncurry ϕ) := by
  classical
  rcases Finset.mem_union.mp hϕ with hϕ | hϕ
  · rcases Finset.mem_image.mp hϕ with ⟨g, hg, rfl⟩
    exact (hG g hg).comp measurable_fst
  · rcases Finset.mem_image.mp hϕ with ⟨a, ha, rfl⟩
    exact (hA a ha).comp measurable_snd

lemma testFamily_continuous (G : Finset (X → ℝ)) (A : Finset (ℝ → ℝ))
    (hA : ∀ a ∈ A, ContinuousOn a (Set.Icc (0 : ℝ) 1))
    (ϕ : X → ℝ → ℝ) (hϕ : ϕ ∈ testFamily G A) (x : X) :
    ContinuousOn (ϕ x) (Set.Icc (0 : ℝ) 1) := by
  classical
  rcases Finset.mem_union.mp hϕ with hϕ | hϕ
  · rcases Finset.mem_image.mp hϕ with ⟨g, hg, rfl⟩
    exact continuousOn_const
  · rcases Finset.mem_image.mp hϕ with ⟨a, ha, rfl⟩
    exact hA a ha

lemma testFamily_bounded (G : Finset (X → ℝ)) (A : Finset (ℝ → ℝ))
    (hG : ∀ g ∈ G, ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1)
    (hA : ∀ a ∈ A, ∀ s, a s ∈ Set.Icc (-1 : ℝ) 1)
    (ϕ : X → ℝ → ℝ) (hϕ : ϕ ∈ testFamily G A) (x : X) (s : ℝ) :
    ϕ x s ∈ Set.Icc (-1 : ℝ) 1 := by
  classical
  rcases Finset.mem_union.mp hϕ with hϕ | hϕ
  · rcases Finset.mem_image.mp hϕ with ⟨g, hg, rfl⟩
    exact hG g hg x
  · rcases Finset.mem_image.mp hϕ with ⟨a, ha, rfl⟩
    exact hA a ha s

lemma testFamily_nonempty (G : Finset (X → ℝ)) (A : Finset (ℝ → ℝ))
    (hA : A.Nonempty) : (testFamily G A).Nonempty := by
  classical
  exact Finset.Nonempty.inr (Finset.image_nonempty.mpr hA)

lemma algM_sq_pos (n : ℕ) (δ : ℝ) : 1 ≤ algM n δ ^ 2 := by
  have hm : 2 ≤ algM n δ := le_max_left _ _
  nlinarith

lemma algTests_measurable [MeasurableSpace X] (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ))
    (hG : ∀ g ∈ G, Measurable g) (ϕ : X → ℝ → ℝ) (hϕ : ϕ ∈ algTests n δ G) :
    Measurable (Function.uncurry ϕ) := by
  exact testFamily_measurable G _ hG
    (fun a ha => (liftedClass_regular _ _ (algM_sq_pos n δ) a ha).1) ϕ hϕ

lemma algTests_continuous (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ))
    (ϕ : X → ℝ → ℝ) (hϕ : ϕ ∈ algTests n δ G) (x : X) :
    ContinuousOn (ϕ x) (Set.Icc (0 : ℝ) 1) := by
  exact testFamily_continuous G _
    (fun a ha => (liftedClass_regular _ _ (algM_sq_pos n δ) a ha).2.1) ϕ hϕ x

lemma algTests_bounded (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ))
    (hG : ∀ g ∈ G, ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1)
    (ϕ : X → ℝ → ℝ) (hϕ : ϕ ∈ algTests n δ G) (x : X) (s : ℝ) :
    ϕ x s ∈ Set.Icc (-1 : ℝ) 1 := by
  exact testFamily_bounded G _ hG
    (fun a ha => (liftedClass_regular _ _ (algM_sq_pos n δ) a ha).2.2) ϕ hϕ x s

lemma algTests_nonempty (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ)) :
    (algTests n δ G).Nonempty := by
  exact testFamily_nonempty G _ (liftedClass_nonempty _ _ (algM_sq_pos n δ) (by omega))

end CalibratedMA.Randomized.MainCandidatesRegularity

end

-- Solutions.MainPopulation
section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CalibratedMA.Randomized.MainPopulation

variable {X : Type*} [MeasurableSpace X]

lemma jointLaw_integral (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (Q : X → Measure ℝ) (hQ : IsRandomizedPredictor Q) (f : X × ℝ × ℝ → ℝ)
    (hf : Measurable f) (hi : Integrable f (jointLaw D Q)) :
    (∫ w, f w ∂jointLaw D Q) = ∫ z, ∫ p, f (z.1, z.2, p) ∂Q z.1 ∂D := by
  let κ : Kernel (X × ℝ) (X × ℝ × ℝ) :=
    ⟨fun z => (Q z.1).map (fun p => (z.1, z.2, p)), CalibrationLaw.measurable_jointKernel Q hQ⟩
  let : IsMarkovKernel κ := ⟨fun z => by
    let : IsProbabilityMeasure (Q z.1) := (hQ.2 z.1).1
    exact Measure.isProbabilityMeasure_map (by fun_prop)⟩
  change Integrable f (κ ∘ₘ D) at hi
  change (∫ w, f w ∂(κ ∘ₘ D)) = _
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  exact integral_map_of_stronglyMeasurable (by fun_prop) hf.stronglyMeasurable

lemma integrable_jointLaw_integral (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (Q : X → Measure ℝ) (hQ : IsRandomizedPredictor Q) (f : X × ℝ × ℝ → ℝ)
    (hf : Measurable f) (hi : Integrable f (jointLaw D Q)) :
    Integrable (fun z => ∫ p, f (z.1, z.2, p) ∂Q z.1) D := by
  let κ : Kernel (X × ℝ) (X × ℝ × ℝ) :=
    ⟨fun z => (Q z.1).map (fun p => (z.1, z.2, p)), CalibrationLaw.measurable_jointKernel Q hQ⟩
  let : IsMarkovKernel κ := ⟨fun z => by
    let : IsProbabilityMeasure (Q z.1) := (hQ.2 z.1).1
    exact Measure.isProbabilityMeasure_map (by fun_prop)⟩
  change Integrable f (κ ∘ₘ D) at hi
  rw [Measure.comp_eq_comp_const_apply] at hi
  have hout := hi.integral_comp
  apply hout.congr
  apply Filter.Eventually.of_forall
  intro z
  exact integral_map_of_stronglyMeasurable (by fun_prop) hf.stronglyMeasurable

lemma integrable_test_residual (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, z.2 ∈ Set.Icc (0 : ℝ) 1)
    (Q : X → Measure ℝ) (hQ : IsRandomizedPredictor Q)
    (φ : X → ℝ → ℝ) (hφm : Measurable (Function.uncurry φ))
    (hφ : ∀ x, ∀ p ∈ Set.Icc (0 : ℝ) 1, |φ x p| ≤ 1) :
    Integrable (fun w : X × ℝ × ℝ => φ w.1 w.2.2 * (w.2.1 - w.2.2)) (jointLaw D Q) := by
  apply (CalibrationLaw.integrable_residual D Q hD hQ).bdd_mul
    (hφm.comp (show Measurable (fun w : X × ℝ × ℝ => (w.1, w.2.2)) by fun_prop)).aestronglyMeasurable
  filter_upwards [CalibrationLaw.jointLaw_support D Q hD hQ] with w hw
  simpa only [Real.norm_eq_abs, Function.comp_apply, Function.uncurry_apply_pair] using hφ w.1 w.2.2 hw.2

noncomputable def mixture (n M : ℕ) (γ : ℕ → ℝ) (s : Fin n → X → ℝ) : X → Measure ℝ :=
  fun x => (n : ℝ≥0∞)⁻¹ • ∑ t : Fin n, roundMeasure M γ (s t x)

lemma round_predictor (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ)
    (s : X → ℝ) (hs : Measurable s) : IsRandomizedPredictor (fun x => roundMeasure M γ (s x)) := by
  exact ⟨(MainCandidatesRegularity.measurable_roundMeasure M γ).comp hs,
    fun x => ⟨MainCandidatesRegularity.roundMeasure_probability M γ (s x),
      MainCandidatesRegularity.roundMeasure_support K M γ hΓ (s x)⟩⟩

lemma mixture_predictor (K M n : ℕ) (hn : 1 ≤ n) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ)
    (s : Fin n → X → ℝ) (hs : ∀ t, Measurable (s t)) : IsRandomizedPredictor (mixture n M γ s) := by
  have hr (t : Fin n) := round_predictor K M γ hΓ (s t) (hs t)
  refine ⟨?_, fun x => ⟨?_, ?_⟩⟩
  · apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [mixture, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
    exact measurable_const.mul (Finset.measurable_fun_sum _
      (fun t _ => (Measure.measurable_coe hA).comp (hr t).1))
  · refine ⟨?_⟩
    have huniv (t : Fin n) : roundMeasure M γ (s t x) Set.univ = 1 := by
      let : IsProbabilityMeasure (roundMeasure M γ (s t x)) := (hr t).2 x |>.1
      exact measure_univ
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simpa [mixture, Measure.smul_apply, huniv] using
      ENNReal.inv_mul_cancel hn0 (by simp : (n : ℝ≥0∞) ≠ ⊤)
  · have hzero (t : Fin n) : roundMeasure M γ (s t x) (Set.Icc (0 : ℝ) 1)ᶜ = 0 := (hr t).2 x |>.2
    simp [mixture, Measure.smul_apply, hzero]

omit [MeasurableSpace X] in
lemma integral_mixture (n M : ℕ) (γ : ℕ → ℝ) (s : Fin n → X → ℝ) (x : X) (h : ℝ → ℝ) :
    (∫ p, h p ∂mixture n M γ s x) =
      (1 / (n : ℝ)) * ∑ t : Fin n, ∫ p, h p ∂roundMeasure M γ (s t x) := by
  rw [mixture, integral_smul_measure,
    integral_finsetSum_measure (fun t _ => MainEmpirical.integrable_roundMeasure M γ (s t x) h)]
  simp [smul_eq_mul, one_div]

lemma mixture_residual (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, z.2 ∈ Set.Icc (0 : ℝ) 1)
    (K M n : ℕ) (hn : 1 ≤ n) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ)
    (s : Fin n → X → ℝ) (hs : ∀ t, Measurable (s t))
    (φ : X → ℝ → ℝ) (hφm : Measurable (Function.uncurry φ))
    (hφ : ∀ x, ∀ p ∈ Set.Icc (0 : ℝ) 1, |φ x p| ≤ 1) :
    (∫ w, φ w.1 w.2.2 * (w.2.1 - w.2.2) ∂jointLaw D (mixture n M γ s)) =
      (1 / (n : ℝ)) * ∑ t : Fin n,
        ∫ z, ∫ p, φ z.1 p * (z.2 - p) ∂roundMeasure M γ (s t z.1) ∂D := by
  have hQ := mixture_predictor K M n hn γ hΓ s hs
  have hfm : Measurable (fun w : X × ℝ × ℝ => φ w.1 w.2.2 * (w.2.1 - w.2.2)) :=
    (hφm.comp (show Measurable (fun w : X × ℝ × ℝ => (w.1, w.2.2)) by fun_prop)).mul (by fun_prop)
  have hi := integrable_test_residual D hD _ hQ φ hφm hφ
  rw [jointLaw_integral D _ hQ _ hfm hi]
  simp_rw [integral_mixture]
  rw [integral_const_mul, integral_finsetSum]
  intro t ht
  exact integrable_jointLaw_integral D _ (round_predictor K M γ hΓ (s t) (hs t)) _ hfm
    (integrable_test_residual D hD _ (round_predictor K M γ hΓ (s t) (hs t)) φ hφm hφ)

lemma rounded_input_residual (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ)
    (s y g : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (∫ p, g * (y - p) ∂roundMeasure M γ s) = g * (y - s) := by
  let : IsProbabilityMeasure (roundMeasure M γ s) := MainCandidatesRegularity.roundMeasure_probability M γ s
  rw [integral_const_mul, integral_sub
    (MainEmpirical.integrable_roundMeasure M γ s (fun _ => y))
    (MainEmpirical.integrable_roundMeasure M γ s (fun p => p))]
  simp [eq_4 K M γ hΓ s hs]

lemma CMA_le_of_residual_bounds (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, z.2 ∈ Set.Icc (0 : ℝ) 1)
    (Q : X → Measure ℝ) (hQ : IsRandomizedPredictor Q) (G : Finset (X → ℝ))
    (B : ℝ) (hB : 0 ≤ B)
    (hG : ∀ g ∈ G, |∫ w, g w.1 * (w.2.1 - w.2.2) ∂jointLaw D Q| ≤ B)
    (hH : ∀ h : ℝ → ℝ, Measurable h → (∀ p, h p = 1 ∨ h p = -1) →
      (∫ w, h w.2.2 * (w.2.1 - w.2.2) ∂jointLaw D Q) ≤ B) : CMA D Q G ≤ B := by
  apply max_le
  · by_cases hne : G.Nonempty
    · let : Nonempty G := by obtain ⟨g,hg⟩ := hne; exact ⟨⟨g,hg⟩⟩
      exact ciSup_le (fun g => hG g g.property)
    · have hzero : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst G
      let : IsEmpty (↑(∅ : Finset (X → ℝ))) := ⟨fun g => Finset.notMem_empty g.val g.property⟩
      simpa [MA, Real.sSup_empty] using hB
  · apply (eq_2 D hD Q hQ).2
    rintro v ⟨h, hh, hsign, rfl⟩
    exact hH h hh hsign

lemma abs_test_residual_le_one (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, z.2 ∈ Set.Icc (0 : ℝ) 1)
    (Q : X → Measure ℝ) (hQ : IsRandomizedPredictor Q)
    (φ : X → ℝ → ℝ) (hφm : Measurable (Function.uncurry φ))
    (hφ : ∀ x, ∀ p ∈ Set.Icc (0 : ℝ) 1, |φ x p| ≤ 1) :
    |∫ w, φ w.1 w.2.2 * (w.2.1 - w.2.2) ∂jointLaw D Q| ≤ 1 := by
  let : IsProbabilityMeasure (jointLaw D Q) := CalibrationLaw.jointLaw_isProbabilityMeasure D Q hQ
  have hi := integrable_test_residual D hD Q hQ φ hφm hφ
  calc
    _ ≤ ∫ w, |φ w.1 w.2.2 * (w.2.1 - w.2.2)| ∂jointLaw D Q := abs_integral_le_integral_abs
    _ ≤ ∫ _w, (1 : ℝ) ∂jointLaw D Q := by
      apply integral_mono_ae hi.abs (integrable_const 1)
      filter_upwards [CalibrationLaw.jointLaw_support D Q hD hQ] with w hw
      rw [abs_mul]
      have hr : |w.2.1 - w.2.2| ≤ 1 := abs_le.mpr
        ⟨by linarith [hw.1.1, hw.2.2], by linarith [hw.1.2, hw.2.1]⟩
      simpa using mul_le_mul (hφ w.1 w.2.2 hw.2) hr (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = 1 := by simp

lemma CMA_le_one (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, z.2 ∈ Set.Icc (0 : ℝ) 1)
    (Q : X → Measure ℝ) (hQ : IsRandomizedPredictor Q) (G : Finset (X → ℝ))
    (hG : ∀ g ∈ G, Measurable g ∧ ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) :
    CMA D Q G ≤ 1 := by
  apply CMA_le_of_residual_bounds D hD Q hQ G 1 (by norm_num)
  · intro g hg
    exact abs_test_residual_le_one D hD Q hQ (fun x _ => g x)
      ((hG g hg).1.comp measurable_fst) (fun x _ _ => abs_le.mpr ((hG g hg).2 x))
  · intro h hm hh
    apply (le_abs_self _).trans
    apply abs_test_residual_le_one D hD Q hQ (fun _ p => h p) (hm.comp measurable_snd)
    intro x p hp
    rcases hh p with hh | hh <;> simp [hh]

end CalibratedMA.Randomized.MainPopulation

end

-- Solutions.LiftedRestriction
section

open MeasureTheory

namespace CalibratedMA.Randomized.LiftedRestriction

/-- At a grid point with nonzero denominator, the sign test reads its index's membership. -/
lemma signTest_grid (K : ℕ) (T : Finset ℕ) (i : ℕ) (hK : 1 ≤ K) :
    signTest K T ((i : ℝ) / K) = if i ∈ T then 1 else -1 := by
  classical
  have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  simp only [signTest, div_left_inj' hKne, Nat.cast_inj]
  simp

/-- Restricting the sign assignment does not change its values at retained grid indices. -/
lemma signTest_inter_eq_of_mem (K : ℕ) (S T : Finset ℕ) (hK : 1 ≤ K)
    (i : ℕ) (hi : i ∈ S) :
    signTest K T ((i : ℝ) / K) = signTest K (T ∩ S) ((i : ℝ) / K) := by
  rw [signTest_grid K T i hK, signTest_grid K (T ∩ S) i hK]
  simp only [Finset.mem_inter, hi, and_true]

/-- An in-range entry of the sorted index list belongs to the original finite set. -/
lemma sorted_getD_mem (S : Finset ℕ) (K j : ℕ) (hj : j < S.card) :
    (S.sort (· ≤ ·)).getD j K ∈ S := by
  have hlen : j < (S.sort (· ≤ ·)).length := by simpa only [Finset.length_sort] using hj
  rw [List.getD_eq_getElem _ _ hlen]
  exact (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hlen)

/-- A finite supremum of indices below a positive bound remains below that bound,
even when the filtered set is empty. -/
lemma roundIndex_lt (M : ℕ) (γ : ℕ → ℝ) (s : ℝ) (hM : 0 < M) :
    roundIndex M γ s < M := by
  unfold roundIndex
  apply (Finset.sup_lt_iff hM).2
  intro j hj
  exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1

/-- Integration against the rounding law only uses its two selected endpoints. -/
lemma integral_roundMeasure_test (M : ℕ) (γ : ℕ → ℝ) (s : ℝ) (h : ℝ → ℝ) :
    ∫ p, h p ∂(roundMeasure M γ s) =
      (1 - roundWeight M γ s) * h (γ (roundIndex M γ s)) +
        roundWeight M γ s * h (γ (roundIndex M γ s + 1)) := by
  have hw0 : 0 ≤ roundWeight M γ s := le_max_left _ _
  have hw1 : roundWeight M γ s ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have ha : Integrable h
      (ENNReal.ofReal (1 - roundWeight M γ s) • Measure.dirac (γ (roundIndex M γ s))) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hb : Integrable h
      (ENNReal.ofReal (roundWeight M γ s) • Measure.dirac (γ (roundIndex M γ s + 1))) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [roundMeasure, integral_add_measure ha hb]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hw0,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hw1), smul_eq_mul]

/-- Signs outside the chosen partition points never affect the lifted function.
The identity holds on all real scores, including the clamped extension. -/
lemma liftTest_inter_of_card (K : ℕ) (S T : Finset ℕ) (hK : 1 ≤ K) (hS : 2 ≤ S.card) :
    liftTest (partitionOfIndexSet K S).1 (partitionOfIndexSet K S).2 (signTest K T) =
      liftTest (partitionOfIndexSet K S).1 (partitionOfIndexSet K S).2 (signTest K (T ∩ S)) := by
  funext s
  let L := S.card - 1
  let γ : ℕ → ℝ := fun j => ((S.sort (· ≤ ·)).getD j K : ℝ) / K
  change liftTest L γ (signTest K T) s = liftTest L γ (signTest K (T ∩ S)) s
  have hL : 0 < L := by dsimp only [L]; omega
  have hLc : L + 1 = S.card := by dsimp only [L]; omega
  have hj := roundIndex_lt L γ s hL
  have hsign : ∀ j < S.card, signTest K T (γ j) = signTest K (T ∩ S) (γ j) := by
    intro j hjS
    exact signTest_inter_eq_of_mem K S T hK _ (sorted_getD_mem S K j hjS)
  unfold liftTest
  rw [integral_roundMeasure_test, integral_roundMeasure_test]
  rw [hsign (roundIndex L γ s) (by omega)]
  rw [hsign (roundIndex L γ s + 1) (by omega)]

/-- The restriction identity for the endpoint-containing sets used by `liftedClass`. -/
lemma liftTest_inter (K : ℕ) (S T : Finset ℕ) (hK : 1 ≤ K)
    (hzero : 0 ∈ S) (hlast : K ∈ S) :
    liftTest (partitionOfIndexSet K S).1 (partitionOfIndexSet K S).2 (signTest K T) =
      liftTest (partitionOfIndexSet K S).1 (partitionOfIndexSet K S).2 (signTest K (T ∩ S)) := by
  have hpair : ({0, K} : Finset ℕ) ⊆ S := by simp [Finset.insert_subset_iff, hzero, hlast]
  have hcard := Finset.card_le_card hpair
  have hne : (0 : ℕ) ≠ K := by omega
  rw [Finset.card_pair hne] at hcard
  exact liftTest_inter_of_card K S T hK hcard

end CalibratedMA.Randomized.LiftedRestriction

end

-- Solutions.LiftedLogBound
section

namespace CalibratedMA.Randomized.LiftedLogBound

lemma counting_sum_le (K M : ℕ) :
    (∑ L ∈ Finset.Icc 1 M, Nat.choose (K + 1) (L + 1) * 2 ^ (L + 1)) ≤
      (M + 1) * (2 * (K + 1)) ^ (M + 1) := by
  have hterm (L : ℕ) (hL : L ∈ Finset.Icc 1 M) :
      Nat.choose (K + 1) (L + 1) * 2 ^ (L + 1) ≤ (2 * (K + 1)) ^ (M + 1) := by
    calc
      _ ≤ (K + 1) ^ (L + 1) * 2 ^ (L + 1) :=
        Nat.mul_le_mul_right _ (Nat.choose_le_pow (K + 1) (L + 1))
      _ = (2 * (K + 1)) ^ (L + 1) := by rw [mul_pow, mul_comm]
      _ ≤ _ := pow_le_pow_right' (by omega) (by have := (Finset.mem_Icc.mp hL).2; omega)
  calc
    _ ≤ ∑ _L ∈ Finset.Icc 1 M, (2 * (K + 1)) ^ (M + 1) := Finset.sum_le_sum hterm
    _ = M * (2 * (K + 1)) ^ (M + 1) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_succ M)

lemma log_grid_scale (K : ℕ) (hK : 1 ≤ K) :
    Real.log (Real.exp 1 / (1 / (K : ℝ))) = 1 + Real.log (K : ℝ) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  rw [one_div, div_inv_eq_mul,
    Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hKpos), Real.log_exp]

lemma log_le_of_card_le (K M n : ℕ) (hK : 1 ≤ K) (hM : 1 ≤ M)
    (hn : n ≤ (M + 1) * (2 * (K + 1)) ^ (M + 1)) :
    Real.log (n : ℝ) ≤ 10 * M * Real.log (Real.exp 1 / (1 / (K : ℝ))) := by
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hKpos : (0 : ℝ) < K := by linarith
  have hMnonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_natCast_nonneg K
  rw [log_grid_scale K hK]
  by_cases hnzero : n = 0
  · subst n
    simp only [Nat.cast_zero, Real.log_zero]
    positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hnzero)
  have hlogn : Real.log (n : ℝ) ≤
      Real.log (((M : ℝ) + 1) * (2 * ((K : ℝ) + 1)) ^ (M + 1)) := by
    apply Real.log_le_log hnpos
    exact_mod_cast hn
  have hlogM : Real.log ((M : ℝ) + 1) ≤ M := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (M : ℝ) + 1)
    linarith
  have hlogbase : Real.log (2 * ((K : ℝ) + 1)) ≤ 3 * (1 + Real.log (K : ℝ)) := by
    have hcompare : 2 * ((K : ℝ) + 1) ≤ 4 * (K : ℝ) := by linarith
    have hlogcompare := Real.log_le_log (by positivity : 0 < 2 * ((K : ℝ) + 1)) hcompare
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hKpos)] at hlogcompare
    have hlogfour : Real.log (4 : ℝ) ≤ 3 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      norm_num at h ⊢
      exact h
    linarith
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Nat.cast_add, Nat.cast_one] at hlogn
  have hmul : ((M : ℝ) + 1) * Real.log (2 * ((K : ℝ) + 1)) ≤
      ((M : ℝ) + 1) * (3 * (1 + Real.log (K : ℝ))) :=
    mul_le_mul_of_nonneg_left hlogbase (by positivity)
  have hdouble : (M : ℝ) + 1 ≤ 2 * M := by linarith
  have hmul' := mul_le_mul_of_nonneg_right hdouble
    (by positivity : 0 ≤ 3 * (1 + Real.log (K : ℝ)))
  have hMscale : (M : ℝ) ≤ M * (1 + Real.log (K : ℝ)) := by
    nlinarith [mul_nonneg hMnonneg hlogK]
  nlinarith [mul_nonneg hMnonneg hlogK]

end CalibratedMA.Randomized.LiftedLogBound

end

-- Solutions.MainCandidates
section

namespace CalibratedMA.Randomized.MainCandidates

/-- The index sets of partitions with at most `M` intervals on the fine grid. -/
def parts (K M : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (K + 1)).powerset.filter
    (fun S => 0 ∈ S ∧ K ∈ S ∧ S.card ≤ M + 1)

/-- Candidate partitions with sign assignments specified only on their partition points. -/
def candidates (K M : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (parts K M).biUnion (fun S => S.powerset.image (fun T => (S, T)))

/-- The lifted test represented by a candidate partition and sign assignment. -/
noncomputable def candidateLift (K : ℕ) (ST : Finset ℕ × Finset ℕ) : ℝ → ℝ :=
  liftTest (partitionOfIndexSet K ST.1).1 (partitionOfIndexSet K ST.1).2
    (signTest K ST.2)

@[simp] lemma mem_parts (K M : ℕ) (S : Finset ℕ) :
    S ∈ parts K M ↔
      S ⊆ Finset.range (K + 1) ∧ 0 ∈ S ∧ K ∈ S ∧ S.card ≤ M + 1 := by
  simp only [parts, Finset.mem_filter, Finset.mem_powerset]

@[simp] lemma mem_candidates (K M : ℕ) (ST : Finset ℕ × Finset ℕ) :
    ST ∈ candidates K M ↔
      ST.1 ⊆ Finset.range (K + 1) ∧ 0 ∈ ST.1 ∧ K ∈ ST.1 ∧
        ST.1.card ≤ M + 1 ∧ ST.2 ⊆ ST.1 := by
  rcases ST with ⟨S, T⟩
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨S', hS', hp⟩
    rcases Finset.mem_image.mp hp with ⟨T', hT', hpair⟩
    rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
    rcases (mem_parts K M S').mp hS' with ⟨hSA, h0, hK, hcard⟩
    exact ⟨hSA, h0, hK, hcard, Finset.mem_powerset.mp hT'⟩
  · rintro ⟨hSA, h0, hK, hcard, hTS⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨S, (mem_parts K M S).mpr ⟨hSA, h0, hK, hcard⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨T, Finset.mem_powerset.mpr hTS, rfl⟩

lemma card_parts_ge_two (K M : ℕ) (hK : 1 ≤ K) (S : Finset ℕ) (hS : S ∈ parts K M) :
    2 ≤ S.card := by
  obtain ⟨_, h0, hlast, _⟩ := (mem_parts K M S).mp hS
  have hpair : ({0, K} : Finset ℕ) ⊆ S := by simp [Finset.insert_subset_iff, h0, hlast]
  have hc := Finset.card_le_card hpair
  simpa only [Finset.card_pair (show (0 : ℕ) ≠ K by omega)] using hc

/-- The candidate count uses signs only at the selected partition points. -/
lemma candidates_card_le (K M : ℕ) (hK : 1 ≤ K) :
    (candidates K M).card ≤
      ∑ L ∈ Finset.Icc 1 M, Nat.choose (K + 1) (L + 1) * 2 ^ (L + 1) := by
  let A := Finset.range (K + 1)
  let F := (Finset.Icc 1 M).biUnion (fun L =>
    (Finset.powersetCard (L + 1) A).biUnion
      (fun S => S.powerset.image (fun T => (S, T))))
  have hsub : candidates K M ⊆ F := by
    intro ST hST
    obtain ⟨hSA, h0, hlast, hcard, hTS⟩ := (mem_candidates K M ST).mp hST
    have hlo := card_parts_ge_two K M hK ST.1
      ((mem_parts K M ST.1).mpr ⟨hSA, h0, hlast, hcard⟩)
    apply Finset.mem_biUnion.mpr
    refine ⟨ST.1.card - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨ST.1, Finset.mem_powersetCard.mpr ⟨hSA, by omega⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨ST.2, Finset.mem_powerset.mpr hTS, Prod.eta ST⟩
  calc
    (candidates K M).card ≤ F.card := Finset.card_le_card hsub
    _ ≤ ∑ L ∈ Finset.Icc 1 M,
        ((Finset.powersetCard (L + 1) A).biUnion
          (fun S => S.powerset.image (fun T => (S, T)))).card := Finset.card_biUnion_le
    _ ≤ ∑ L ∈ Finset.Icc 1 M, Nat.choose (K + 1) (L + 1) * 2 ^ (L + 1) := by
      apply Finset.sum_le_sum
      intro L hL
      calc
        _ ≤ ∑ S ∈ Finset.powersetCard (L + 1) A,
            (S.powerset.image (fun T => (S, T))).card := Finset.card_biUnion_le
        _ ≤ ∑ _S ∈ Finset.powersetCard (L + 1) A, 2 ^ (L + 1) := by
          apply Finset.sum_le_sum
          intro S hS
          exact Finset.card_image_le.trans (by
            rw [Finset.card_powerset, (Finset.mem_powersetCard.mp hS).2])
        _ = _ := by simp [A]

lemma candidates_nonempty (K M : ℕ) (hK : 1 ≤ K) (hM : 1 ≤ M) :
    (candidates K M).Nonempty := by
  have hne : (0 : ℕ) ≠ K := by omega
  refine ⟨({0, K}, ∅), (mem_candidates K M _).mpr ?_⟩
  refine ⟨?_, by simp, by simp, ?_, Finset.empty_subset _⟩
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_range]
    omega
  · simp only [Finset.card_pair hne]
    omega

lemma candidates_card_le_poly (K M : ℕ) (hK : 1 ≤ K) :
    (candidates K M).card ≤ (M + 1) * (2 * (K + 1)) ^ (M + 1) :=
  (candidates_card_le K M hK).trans (LiftedLogBound.counting_sum_le K M)

lemma log_candidates_card_le (K M : ℕ) (hK : 1 ≤ K) (hM : 1 ≤ M) :
    Real.log (candidates K M).card ≤
      10 * (M : ℝ) * Real.log (Real.exp 1 / (1 / (K : ℝ))) := by
  exact LiftedLogBound.log_le_of_card_le K M _ hK hM (candidates_card_le_poly K M hK)

open Classical in
/-- Restricted sign assignments represent exactly the lifted class, not a relaxation. -/
lemma candidates_image_eq_liftedClass (K M : ℕ) (hK : 1 ≤ K) :
    (candidates K M).image (candidateLift K) = liftedClass K M := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨ST, hST, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hSA, h0, hlast, hcard, hTS⟩ := (mem_candidates K M ST).mp hST
    apply Finset.mem_image.mpr
    refine ⟨ST, Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSA, h0, hlast, hcard⟩
    · exact Finset.mem_powerset.mpr (hTS.trans hSA)
  · intro ha
    obtain ⟨⟨S, T⟩, hST, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hS, _⟩ := Finset.mem_product.mp hST
    obtain ⟨hSA, h0, hlast, hcard⟩ := Finset.mem_filter.mp hS
    apply Finset.mem_image.mpr
    refine ⟨(S, T ∩ S), (mem_candidates K M _).mpr
      ⟨Finset.mem_powerset.mp hSA, h0, hlast, hcard, Finset.inter_subset_right⟩, ?_⟩
    exact (LiftedRestriction.liftTest_inter K S T hK h0 hlast).symm

lemma candidateLift_mem (K M : ℕ) (hK : 1 ≤ K) (ST : Finset ℕ × Finset ℕ)
    (hST : ST ∈ candidates K M) : candidateLift K ST ∈ liftedClass K M := by
  classical
  rw [← candidates_image_eq_liftedClass K M hK]
  exact Finset.mem_image.mpr ⟨ST, hST, rfl⟩

lemma exists_candidate_of_mem (K M : ℕ) (hK : 1 ≤ K) (a : ℝ → ℝ)
    (ha : a ∈ liftedClass K M) :
    ∃ ST ∈ candidates K M, candidateLift K ST = a := by
  classical
  rw [← candidates_image_eq_liftedClass K M hK] at ha
  exact Finset.mem_image.mp ha

end CalibratedMA.Randomized.MainCandidates

end

-- Solutions.MainCandidatesRepresentation
section

namespace CalibratedMA.Randomized.MainCandidates

/-- Encode prescribed signs by the subset of grid indices assigned the positive sign. -/
lemma signTest_filter_eq (K : ℕ) (S : Finset ℕ) (h : ℝ → ℝ) (hK : 1 ≤ K)
    (i : ℕ) (hi : i ∈ S)
    (hh : h ((i : ℝ) / K) = 1 ∨ h ((i : ℝ) / K) = -1) :
    signTest K (S.filter (fun i => h ((i : ℝ) / K) = 1)) ((i : ℝ) / K) = h ((i : ℝ) / K) := by
  classical
  rw [LiftedRestriction.signTest_grid K _ i hK]
  rcases hh with hh | hh <;> norm_num [Finset.mem_filter, hi, hh]

/-- Every valid partition with signs on its knots is represented by a finite candidate. -/
lemma exists_candidate_for_partition (K M L : ℕ) (γ : ℕ → ℝ)
    (hK : 1 ≤ K) (hΓ : IsGridPartition K L γ) (hLM : L ≤ M)
    (h : ℝ → ℝ) (hh : ∀ j ≤ L, h (γ j) = 1 ∨ h (γ j) = -1) :
    ∃ ST ∈ candidates K M,
      (partitionOfIndexSet K ST.1).1 = L ∧
      (∀ j ≤ L, (partitionOfIndexSet K ST.1).2 j = γ j) ∧
      ∀ j ≤ L, signTest K ST.2 (γ j) = h (γ j) := by
  classical
  obtain ⟨S, hSA, h0, hlast, hcard, hγ⟩ :=
    MainCandidatesGrid.exists_indexSet K L γ hK hΓ
  let T : Finset ℕ := S.filter (fun i : ℕ => h ((i : ℝ) / K) = 1)
  refine ⟨(S, T), (mem_candidates K M _).mpr
    ⟨hSA, h0, hlast, by change S.card ≤ M + 1; omega,
      Finset.filter_subset _ _⟩, ?_, hγ, ?_⟩
  · simp only [partitionOfIndexSet, hcard, Nat.add_sub_cancel]
  · intro j hj
    let i := (S.sort (· ≤ ·)).getD j K
    have hi : i ∈ S := LiftedRestriction.sorted_getD_mem S K j (by omega)
    have hval : (i : ℝ) / K = γ j := hγ j hj
    rw [← hval]
    exact signTest_filter_eq K S h hK i hi (by simpa only [hval] using hh j hj)

/-- Two tests agreeing at every possible rounding endpoint have identical lifts on all scores. -/
lemma liftTest_test_congr (L : ℕ) (γ : ℕ → ℝ) (h h' : ℝ → ℝ) (hL : 0 < L)
    (hh : ∀ j ≤ L, h (γ j) = h' (γ j)) : liftTest L γ h = liftTest L γ h' := by
  funext s
  have hj := LiftedRestriction.roundIndex_lt L γ s hL
  unfold liftTest
  rw [LiftedRestriction.integral_roundMeasure_test, LiftedRestriction.integral_roundMeasure_test,
    hh (roundIndex L γ s) (by omega), hh (roundIndex L γ s + 1) (by omega)]

/-- Every signed lift on a valid grid partition is represented by a finite candidate. -/
lemma exists_candidate_lift (K M L : ℕ) (γ : ℕ → ℝ)
    (hK : 1 ≤ K) (hΓ : IsGridPartition K L γ) (hLM : L ≤ M)
    (h : ℝ → ℝ) (hh : ∀ j ≤ L, h (γ j) = 1 ∨ h (γ j) = -1) :
    ∃ ST ∈ candidates K M, candidateLift K ST = liftTest L γ h := by
  obtain ⟨ST, hST, hlen, hknots, hsign⟩ :=
    exists_candidate_for_partition K M L γ hK hΓ hLM h hh
  have hL : 0 < L := by
    by_contra hL
    have hL : L = 0 := by omega
    have heq := hΓ.2.1
    rw [hL, hΓ.1] at heq
    norm_num at heq
  refine ⟨ST, hST, ?_⟩
  unfold candidateLift
  rw [hlen, MainCandidatesGrid.liftTest_congr L _ γ hL hknots]
  exact liftTest_test_congr L γ _ h hL hsign

/-- The lifted test class contains every sign assignment on every admissible partition. -/
lemma liftTest_mem_liftedClass (K M L : ℕ) (γ : ℕ → ℝ)
    (hK : 1 ≤ K) (hΓ : IsGridPartition K L γ) (hLM : L ≤ M)
    (h : ℝ → ℝ) (hh : ∀ j ≤ L, h (γ j) = 1 ∨ h (γ j) = -1) :
    liftTest L γ h ∈ liftedClass K M := by
  obtain ⟨ST, hST, heq⟩ := exists_candidate_lift K M L γ hK hΓ hLM h hh
  rw [← heq]
  exact candidateLift_mem K M hK ST hST

end CalibratedMA.Randomized.MainCandidates

end

-- Solutions.MainCandidateResidual
section

open MeasureTheory

namespace CalibratedMA.Randomized.MainCandidates

/-- A finite candidate reproduces every rounded signed residual of a valid
partition, including scores outside the unit interval under the clamping convention. -/
lemma exists_candidate_rounded_residual (K M L : ℕ) (γ : ℕ → ℝ)
    (hK : 1 ≤ K) (hΓ : IsGridPartition K L γ) (hLM : L ≤ M)
    (h : ℝ → ℝ) (hh : ∀ j ≤ L, h (γ j) = 1 ∨ h (γ j) = -1) :
    ∃ ST ∈ candidates K M, ∀ s y : ℝ,
      (∫ p, h p * (y - p) ∂roundMeasure L γ s) =
        ∫ p, signTest K ST.2 p * (y - p) ∂roundMeasure
          (partitionOfIndexSet K ST.1).1 (partitionOfIndexSet K ST.1).2 s := by
  obtain ⟨ST, hST, hlen, hknots, hsign⟩ :=
    exists_candidate_for_partition K M L γ hK hΓ hLM h hh
  have hL : 0 < L := by
    by_contra hL
    have hL : L = 0 := by omega
    have heq := hΓ.2.1
    rw [hL, hΓ.1] at heq
    norm_num at heq
  refine ⟨ST, hST, ?_⟩
  intro s y
  rw [hlen, MainCandidatesGrid.roundMeasure_congr L _ γ hL hknots s]
  exact congrFun (liftTest_test_congr L γ (fun p => h p * (y - p))
    (fun p => signTest K ST.2 p * (y - p)) hL
    (fun j hj => by rw [hsign j hj])) s

end CalibratedMA.Randomized.MainCandidates

end

-- Solutions.OnlinePrediction
section

namespace CalibratedMA.Randomized.OnlinePrediction

variable {X : Type*}

/-- The rule always selects a score in the unit interval, even before continuity
of the potential is assumed. -/
lemma predictFrom_mem (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (R : (X → ℝ → ℝ) → Bool → ℝ) (x : X) :
    predictFrom N Φ R x ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  simp only [predictFrom]
  split_ifs with hz hpos
  · rcases hz with ⟨p, hp, hpzero⟩
    have hnonempty : {q ∈ Set.Icc (0 : ℝ) 1 | potential N Φ R x q = 0}.Nonempty :=
      ⟨p, hp, hpzero⟩
    have hbdd : BddBelow {q ∈ Set.Icc (0 : ℝ) 1 | potential N Φ R x q = 0} :=
      ⟨0, fun q hq => hq.1.1⟩
    exact ⟨le_csInf hnonempty (fun q hq => hq.1.1),
      (csInf_le hbdd ⟨hp, hpzero⟩).trans hp.2⟩
  · exact ⟨zero_le_one, le_refl _⟩
  · exact ⟨le_refl _, zero_le_one⟩

/-- A finite weighted sum of continuous tests is continuous on the score interval. -/
lemma continuousOn_potential (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (R : (X → ℝ → ℝ) → Bool → ℝ) (x : X)
    (hΦ : ∀ ϕ ∈ Φ, ContinuousOn (ϕ x) (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (potential N Φ R x) (Set.Icc (0 : ℝ) 1) := by
  unfold potential
  apply continuousOn_finsetSum
  intro ϕ hϕ
  apply continuousOn_finsetSum
  intro b _
  exact continuousOn_const.mul (continuousOn_const.mul (hΦ ϕ hϕ))

/-- When a continuous function has a zero on the compact score interval, its
smallest zero lies in the interval and is itself a zero. -/
lemma sInf_zero_mem (H : ℝ → ℝ) (hH : ContinuousOn H (Set.Icc (0 : ℝ) 1))
    (hz : ∃ p ∈ Set.Icc (0 : ℝ) 1, H p = 0) :
    sInf {p ∈ Set.Icc (0 : ℝ) 1 | H p = 0} ∈ {p ∈ Set.Icc (0 : ℝ) 1 | H p = 0} := by
  have hclosed : IsClosed {p ∈ Set.Icc (0 : ℝ) 1 | H p = 0} :=
    isClosed_Icc.isClosed_eq hH continuousOn_const
  have hcompact : IsCompact {p ∈ Set.Icc (0 : ℝ) 1 | H p = 0} :=
    isCompact_Icc.of_isClosed_subset hclosed (fun _ hp => hp.1)
  exact hcompact.sInf_mem hz

/-- The chosen score makes the potential-weighted residual nonpositive for
every possible label in the unit interval. -/
lemma predictFrom_residual_nonpos (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (R : (X → ℝ → ℝ) → Bool → ℝ) (x : X)
    (hΦ : ∀ ϕ ∈ Φ, ContinuousOn (ϕ x) (Set.Icc (0 : ℝ) 1))
    (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (y - predictFrom N Φ R x) * potential N Φ R x (predictFrom N Φ R x) ≤ 0 := by
  classical
  have hH := continuousOn_potential N Φ R x hΦ
  simp only [predictFrom]
  split_ifs with hz hpos
  · rw [(sInf_zero_mem _ hH hz).2, mul_zero]
  · have hright : 0 ≤ potential N Φ R x 1 := by
      by_contra h
      have hnegative : potential N Φ R x 1 < 0 := lt_of_not_ge h
      obtain ⟨p, hp, hpzero⟩ :=
        intermediate_value_Icc' zero_le_one hH ⟨hnegative.le, hpos.le⟩
      exact hz ⟨p, hp, hpzero⟩
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy.2) hright
  · simp only [sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hy.1 (le_of_not_gt hpos)

end CalibratedMA.Randomized.OnlinePrediction

end

-- Solutions.MainMeasurability
section

open MeasureTheory Classical
open scoped ENNReal

namespace CalibratedMA.Randomized.MainMeasurability

/-- For a measurable family of continuous real functions, having a zero on a
fixed compact interval is a measurable event. -/
lemma measurableSet_exists_zero_Icc {A : Type*} [MeasurableSpace A]
    (H : A → ℝ → ℝ) (l u : ℝ) (hlu : l ≤ u)
    (hm : ∀ p ∈ Set.Icc l u, Measurable (fun a => H a p))
    (hc : ∀ a, ContinuousOn (H a) (Set.Icc l u)) :
    MeasurableSet {a | ∃ p ∈ Set.Icc l u, H a p = 0} := by
  let F : A → ℝ≥0∞ := fun a => ⨅ p : Set.Icc l u, ENNReal.ofReal |H a p|
  have hF : Measurable F := by
    have hInf : Measurable (⨅ p : Set.Icc l u, fun a => ENNReal.ofReal |H a p|) := by
      apply measurable_iInf_of_upperSemicontinuous
      · intro p
        exact (hm p p.property).abs.ennreal_ofReal
      · intro a
        have hcont : Continuous (fun p : Set.Icc l u => ENNReal.ofReal |H a p|) :=
          ENNReal.continuous_ofReal.comp
            ((continuousOn_iff_continuous_domRestrict.mp (hc a)).abs)
        exact hcont.upperSemicontinuous
    have heq : F = ⨅ p : Set.Icc l u, fun a => ENNReal.ofReal |H a p| := by
      funext a
      simp only [F, iInf_apply]
    rw [heq]
    exact hInf
  have hzero (a : A) : F a = 0 ↔ ∃ p ∈ Set.Icc l u, H a p = 0 := by
    constructor
    · intro hFa
      obtain ⟨p, hp, hmin⟩ := isCompact_Icc.exists_isMinOn
        (show (Set.Icc l u).Nonempty from ⟨l, le_rfl, hlu⟩) (hc a).abs
      have hle : ENNReal.ofReal |H a p| ≤ F a := by
        apply le_iInf
        intro q
        exact ENNReal.ofReal_le_ofReal (hmin q.property)
      rw [hFa] at hle
      have habs : |H a p| ≤ 0 := ENNReal.ofReal_eq_zero.mp (le_antisymm hle bot_le)
      exact ⟨p, hp, abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))⟩
    · rintro ⟨p, hp, hpzero⟩
      apply le_antisymm _ bot_le
      calc
        F a ≤ ENNReal.ofReal |H a p| :=
          iInf_le (fun q : Set.Icc l u => ENNReal.ofReal |H a q|) ⟨p, hp⟩
        _ = 0 := by simp [hpzero]
  have heq : {a | ∃ p ∈ Set.Icc l u, H a p = 0} = {a | F a = 0} := by
    ext a
    exact (hzero a).symm
  rw [heq]
  exact measurableSet_eq_fun hF measurable_const

/-- The smallest zero in `[0,1]`, with default zero when no root exists. -/
noncomputable def firstZero (H : ℝ → ℝ) : ℝ :=
  if ∃ p ∈ Set.Icc (0 : ℝ) 1, H p = 0 then
    sInf {p ∈ Set.Icc (0 : ℝ) 1 | H p = 0} else 0

lemma firstZero_mem (H : ℝ → ℝ) : firstZero H ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold firstZero
  split_ifs with hz
  · rcases hz with ⟨p, hp, hpzero⟩
    have hne : {q ∈ Set.Icc (0 : ℝ) 1 | H q = 0}.Nonempty := ⟨p, hp, hpzero⟩
    have hbdd : BddBelow {q ∈ Set.Icc (0 : ℝ) 1 | H q = 0} := ⟨0, fun q hq => hq.1.1⟩
    exact ⟨le_csInf hne (fun q hq => hq.1.1), (csInf_le hbdd ⟨hp, hpzero⟩).trans hp.2⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- Sublevel events of the smallest root are compact-interval root events. -/
lemma firstZero_le_iff (H : ℝ → ℝ) (hc : ContinuousOn H (Set.Icc (0 : ℝ) 1))
    (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    firstZero H ≤ r ↔ (∃ p ∈ Set.Icc (0 : ℝ) r, H p = 0) ∨
      ¬∃ p ∈ Set.Icc (0 : ℝ) 1, H p = 0 := by
  classical
  unfold firstZero
  split_ifs with hz
  · have hmem := OnlinePrediction.sInf_zero_mem H hc hz
    constructor
    · intro hle
      exact Or.inl ⟨_, ⟨hmem.1.1, hle⟩, hmem.2⟩
    · rintro (⟨p, hp, hpzero⟩ | hnone)
      · have hbdd : BddBelow {q ∈ Set.Icc (0 : ℝ) 1 | H q = 0} :=
          ⟨0, fun q hq => hq.1.1⟩
        exact (csInf_le hbdd ⟨⟨hp.1, hp.2.trans hr.2⟩, hpzero⟩).trans hp.2
      · exact False.elim (hnone hz)
  · exact iff_of_true hr.1 (Or.inr hz)

lemma measurable_firstZero {A : Type*} [MeasurableSpace A]
    (H : A → ℝ → ℝ)
    (hm : ∀ p ∈ Set.Icc (0 : ℝ) 1, Measurable (fun a => H a p))
    (hc : ∀ a, ContinuousOn (H a) (Set.Icc (0 : ℝ) 1)) :
    Measurable (fun a => firstZero (H a)) := by
  apply measurable_of_Iic
  intro r
  by_cases hr0 : 0 ≤ r
  · by_cases hr1 : r ≤ 1
    · have heq : (fun a => firstZero (H a)) ⁻¹' Set.Iic r =
          {a | ∃ p ∈ Set.Icc (0 : ℝ) r, H a p = 0} ∪
          {a | ∃ p ∈ Set.Icc (0 : ℝ) 1, H a p = 0}ᶜ := by
        ext a
        exact firstZero_le_iff (H a) (hc a) r ⟨hr0, hr1⟩
      rw [heq]
      have hsub : Set.Icc (0 : ℝ) r ⊆ Set.Icc (0 : ℝ) 1 :=
        fun p hp => ⟨hp.1, hp.2.trans hr1⟩
      exact (measurableSet_exists_zero_Icc H 0 r hr0
        (fun p hp => hm p (hsub hp)) (fun a => (hc a).mono hsub)).union
        (measurableSet_exists_zero_Icc H 0 1 zero_le_one hm hc).compl
    · have heq : (fun a => firstZero (H a)) ⁻¹' Set.Iic r = Set.univ := by
        ext a
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
        exact (firstZero_mem (H a)).2.trans (le_of_not_ge hr1)
      rw [heq]
      exact MeasurableSet.univ
  · have heq : (fun a => firstZero (H a)) ⁻¹' Set.Iic r = ∅ := by
      ext a
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr ((lt_of_not_ge hr0).trans_le (firstZero_mem (H a)).1)
    rw [heq]
    exact MeasurableSet.empty

/-- Measurability of the smallest-root / endpoint rule for a measurable family
of continuous potentials. -/
lemma measurable_zero_or_endpoint {A : Type*} [MeasurableSpace A]
    (H : A → ℝ → ℝ)
    (hm : ∀ p ∈ Set.Icc (0 : ℝ) 1, Measurable (fun a => H a p))
    (hc : ∀ a, ContinuousOn (H a) (Set.Icc (0 : ℝ) 1)) :
    Measurable (fun a =>
      if ∃ p ∈ Set.Icc (0 : ℝ) 1, H a p = 0 then
        sInf {p ∈ Set.Icc (0 : ℝ) 1 | H a p = 0}
      else if 0 < H a 0 then (1 : ℝ) else 0) := by
  classical
  have heq : (fun a =>
      if ∃ p ∈ Set.Icc (0 : ℝ) 1, H a p = 0 then
        sInf {p ∈ Set.Icc (0 : ℝ) 1 | H a p = 0}
      else if 0 < H a 0 then (1 : ℝ) else 0) =
      (fun a => if ∃ p ∈ Set.Icc (0 : ℝ) 1, H a p = 0 then firstZero (H a)
        else if 0 < H a 0 then (1 : ℝ) else 0) := by
    funext a
    by_cases hz : ∃ p ∈ Set.Icc (0 : ℝ) 1, H a p = 0
    · simp only [firstZero, if_pos hz]
    · simp only [firstZero, if_neg hz]
  rw [heq]
  apply Measurable.ite (measurableSet_exists_zero_Icc H 0 1 zero_le_one hm hc)
  · exact measurable_firstZero H hm hc
  · exact Measurable.ite (measurableSet_lt measurable_const (hm 0 ⟨le_rfl, zero_le_one⟩))
      measurable_const measurable_const

lemma measurable_potential {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (R : A → (X → ℝ → ℝ) → Bool → ℝ) (x : A → X) (p : ℝ)
    (hR : ∀ ϕ ∈ Φ, ∀ b, Measurable (fun a => R a ϕ b))
    (hx : Measurable x)
    (hΦ : ∀ ϕ ∈ Φ, Measurable (Function.uncurry ϕ)) :
    Measurable (fun a => potential N Φ (R a) (x a) p) := by
  unfold potential
  apply Finset.measurable_sum
  intro ϕ hϕ
  apply Finset.measurable_sum
  intro b _
  exact ((measurable_const.mul (hR ϕ hϕ b)).exp).mul
    (measurable_const.mul ((hΦ ϕ hϕ).comp (hx.prodMk measurable_const)))

/-- Joint measurability of the actual online prediction rule in an arbitrary
measurable parameter, including both residual state and context. -/
lemma measurable_predictFrom {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (R : A → (X → ℝ → ℝ) → Bool → ℝ) (x : A → X)
    (hR : ∀ ϕ ∈ Φ, ∀ b, Measurable (fun a => R a ϕ b))
    (hx : Measurable x)
    (hΦm : ∀ ϕ ∈ Φ, Measurable (Function.uncurry ϕ))
    (hΦc : ∀ ϕ ∈ Φ, ∀ x, ContinuousOn (ϕ x) (Set.Icc (0 : ℝ) 1)) :
    Measurable (fun a => predictFrom N Φ (R a) (x a)) := by
  exact measurable_zero_or_endpoint (fun a p => potential N Φ (R a) (x a) p)
    (fun p _ => measurable_potential N Φ R x p hR hx hΦm)
    (fun a => OnlinePrediction.continuousOn_potential N Φ (R a) (x a)
      (fun ϕ hϕ => hΦc ϕ hϕ (x a)))

end CalibratedMA.Randomized.MainMeasurability

end

-- Solutions.MainMeasurabilityOnline
section

namespace CalibratedMA.Randomized.MainMeasurability

variable {X : Type*} [MeasurableSpace X]

/-- Every tracked residual coordinate is measurable in the training sequence. -/
lemma measurable_residSums (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (hΦm : ∀ ϕ ∈ Φ, Measurable (Function.uncurry ϕ))
    (hΦc : ∀ ϕ ∈ Φ, ∀ x, ContinuousOn (ϕ x) (Set.Icc (0 : ℝ) 1))
    (t : ℕ) : ∀ ϕ ∈ Φ, ∀ b,
      Measurable (fun z : Fin N → X × ℝ => residSums N Φ z t ϕ b) := by
  induction t with
  | zero =>
    intro ϕ hϕ b
    exact measurable_const
  | succ t ih =>
    intro ϕ hϕ b
    by_cases ht : t < N
    · have hx : Measurable (fun z : Fin N → X × ℝ => (z ⟨t, ht⟩).1) :=
        (measurable_pi_apply (⟨t, ht⟩ : Fin N)).fst
      have hy : Measurable (fun z : Fin N → X × ℝ => (z ⟨t, ht⟩).2) :=
        (measurable_pi_apply (⟨t, ht⟩ : Fin N)).snd
      have hs := measurable_predictFrom N Φ
        (fun z : Fin N → X × ℝ => residSums N Φ z t)
        (fun z : Fin N → X × ℝ => (z ⟨t, ht⟩).1) ih hx hΦm hΦc
      have hv := (hΦm ϕ hϕ).comp (hx.prodMk hs)
      have hsgn : Measurable (fun _z : Fin N → X × ℝ => sgnB b) := measurable_const
      have hstep := (ih ϕ hϕ b).add ((hsgn.mul hv).mul (hy.sub hs))
      convert hstep using 1
      funext z
      simp only [residSums, dif_pos ht, Pi.add_apply, Pi.mul_apply, Pi.sub_apply,
        Function.comp_apply, Function.uncurry_apply_pair]
    · simpa only [residSums, dif_neg ht] using ih ϕ hϕ b

/-- The online predictor is jointly measurable in training data and new context. -/
lemma measurable_onlineRule_joint (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (hΦm : ∀ ϕ ∈ Φ, Measurable (Function.uncurry ϕ))
    (hΦc : ∀ ϕ ∈ Φ, ∀ x, ContinuousOn (ϕ x) (Set.Icc (0 : ℝ) 1))
    (t : ℕ) :
    Measurable (fun w : (Fin N → X × ℝ) × X => onlineRule N Φ w.1 t w.2) := by
  exact measurable_predictFrom N Φ
    (fun w : (Fin N → X × ℝ) × X => residSums N Φ w.1 t)
    (fun w : (Fin N → X × ℝ) × X => w.2)
    (fun ϕ hϕ b => (measurable_residSums N Φ hΦm hΦc t ϕ hϕ b).comp measurable_fst)
    measurable_snd hΦm hΦc

/-- For each realized training sequence the online predictor is measurable in context. -/
lemma measurable_onlineRule (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (hΦm : ∀ ϕ ∈ Φ, Measurable (Function.uncurry ϕ))
    (hΦc : ∀ ϕ ∈ Φ, ∀ x, ContinuousOn (ϕ x) (Set.Icc (0 : ℝ) 1))
    (z : Fin N → X × ℝ) (t : ℕ) : Measurable (onlineRule N Φ z t) := by
  have hpair : Measurable (fun x : X => (z, x)) := measurable_const.prodMk measurable_id
  simpa only [Function.comp_def] using
    (measurable_onlineRule_joint N Φ hΦm hΦc t).comp hpair

/-- The adaptively chosen score on each training example is measurable in all
training data. -/
lemma measurable_onlineScore (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (hΦm : ∀ ϕ ∈ Φ, Measurable (Function.uncurry ϕ))
    (hΦc : ∀ ϕ ∈ Φ, ∀ x, ContinuousOn (ϕ x) (Set.Icc (0 : ℝ) 1))
    (t : Fin N) : Measurable (fun z : Fin N → X × ℝ => onlineScore N Φ z t) := by
  have hpair : Measurable (fun z : Fin N → X × ℝ => (z, (z t).1)) :=
    measurable_id.prodMk (measurable_pi_apply t).fst
  simpa only [Function.comp_def, onlineScore] using
    (measurable_onlineRule_joint N Φ hΦm hΦc t).comp hpair

omit [MeasurableSpace X] in
lemma onlineRule_mem (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (z : Fin N → X × ℝ) (t : ℕ) (x : X) :
    onlineRule N Φ z t x ∈ Set.Icc (0 : ℝ) 1 :=
  OnlinePrediction.predictFrom_mem N Φ (residSums N Φ z t) x

omit [MeasurableSpace X] in
lemma onlineScore_mem (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (z : Fin N → X × ℝ) (t : Fin N) : onlineScore N Φ z t ∈ Set.Icc (0 : ℝ) 1 :=
  onlineRule_mem N Φ z t (z t).1

end CalibratedMA.Randomized.MainMeasurability

end

-- Solutions.MainMeasurabilityAlgorithm
section

namespace CalibratedMA.Randomized.MainMeasurability

variable {X : Type*} [MeasurableSpace X]

lemma measurable_alg_onlineRule_joint (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ))
    (hG : ∀ g ∈ G, Measurable g) (t : ℕ) :
    Measurable (fun w : (Fin n → X × ℝ) × X =>
      onlineRule n (algTests n δ G) w.1 t w.2) :=
  measurable_onlineRule_joint n (algTests n δ G)
    (MainCandidatesRegularity.algTests_measurable n δ G hG)
    (MainCandidatesRegularity.algTests_continuous n δ G) t

lemma measurable_alg_onlineRule (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ))
    (hG : ∀ g ∈ G, Measurable g) (ω : Fin n → X × ℝ) (t : ℕ) :
    Measurable (onlineRule n (algTests n δ G) ω t) :=
  measurable_onlineRule n (algTests n δ G)
    (MainCandidatesRegularity.algTests_measurable n δ G hG)
    (MainCandidatesRegularity.algTests_continuous n δ G) ω t

lemma measurable_alg_onlineScore (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ))
    (hG : ∀ g ∈ G, Measurable g) (t : Fin n) :
    Measurable (fun ω : Fin n → X × ℝ => onlineScore n (algTests n δ G) ω t) :=
  measurable_onlineScore n (algTests n δ G)
    (MainCandidatesRegularity.algTests_measurable n δ G hG)
    (MainCandidatesRegularity.algTests_continuous n δ G) t

/-- For each fixed training sample the postprocessed online component is a
measurable map into measures, for any fixed rounding partition. -/
lemma measurable_alg_rounded_component (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ))
    (hG : ∀ g ∈ G, Measurable g) (ω : Fin n → X × ℝ) (t M : ℕ) (γ : ℕ → ℝ) :
    Measurable (fun x => roundMeasure M γ (onlineRule n (algTests n δ G) ω t x)) := by
  have h := (MainCandidatesRegularity.measurable_roundMeasure M γ).comp
    (measurable_alg_onlineRule n δ G hG ω t)
  simpa only [Function.comp_def] using h

end CalibratedMA.Randomized.MainMeasurability

end

-- Solutions.OnlineState
section

namespace CalibratedMA.Randomized.OnlineState

variable {X : Type*}

/-- The residual state at round `t` only uses examples from earlier rounds. -/
lemma residSums_history (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (z z' : Fin N → X × ℝ) (t : ℕ)
    (hz : ∀ s : Fin N, (s : ℕ) < t → z s = z' s) :
    residSums N Φ z t = residSums N Φ z' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hh := ih (fun s hs => hz s (by omega))
      simp only [residSums]
      rw [hh]
      split_ifs with ht
      · rw [hz ⟨t, ht⟩ (by simp)]
      · rfl

/-- The online prediction rule has the history-dependence property in Lemma 3.1. -/
lemma onlineRule_history (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (z z' : Fin N → X × ℝ) (t : ℕ)
    (hz : ∀ s : Fin N, (s : ℕ) < t → z s = z' s) :
    onlineRule N Φ z t = onlineRule N Φ z' t := by
  unfold onlineRule
  rw [residSums_history N Φ z z' t hz]

/-- Expand the recursive residual state as a sum of the increments already observed. -/
lemma residSums_eq_sum_range (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (z : Fin N → X × ℝ) (t : ℕ) (ϕ : X → ℝ → ℝ) (b : Bool) :
    residSums N Φ z t ϕ b =
      ∑ j ∈ Finset.range t, if hj : j < N then
        sgnB b * ϕ (z ⟨j, hj⟩).1 (onlineScore N Φ z ⟨j, hj⟩) *
          ((z ⟨j, hj⟩).2 - onlineScore N Φ z ⟨j, hj⟩) else 0 := by
  induction t with
  | zero => simp [residSums]
  | succ t ih =>
      rw [Finset.sum_range_succ, ← ih]
      by_cases ht : t < N
      · simp only [residSums, ht, dif_pos, onlineScore, onlineRule]
      · simp only [residSums, dif_neg ht, add_zero]

/-- The terminal state is precisely the signed cumulative empirical residual. -/
lemma residSums_terminal (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (z : Fin N → X × ℝ) (ϕ : X → ℝ → ℝ) (b : Bool) :
    residSums N Φ z N ϕ b =
      ∑ t : Fin N, sgnB b * ϕ (z t).1 (onlineScore N Φ z t) *
        ((z t).2 - onlineScore N Φ z t) := by
  rw [residSums_eq_sum_range, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [t.isLt, dif_pos]

@[simp] lemma abs_sgnB (b : Bool) : |sgnB b| = 1 := by
  cases b <;> norm_num [sgnB]

/-- The negative test tracks the negative of the positive test's residual. -/
lemma residSums_false_eq_neg_true (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (z : Fin N → X × ℝ) (t : ℕ) (ϕ : X → ℝ → ℝ) :
    residSums N Φ z t ϕ false = -residSums N Φ z t ϕ true := by
  rw [residSums_eq_sum_range, residSums_eq_sum_range, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp [sgnB]

/-- A bounded test and bounded label/prediction give an increment of magnitude at most one. -/
lemma abs_increment_le_one (ϕ : X → ℝ → ℝ) (x : X) (y s : ℝ) (b : Bool)
    (hϕ : ϕ x s ∈ Set.Icc (-1 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    |sgnB b * ϕ x s * (y - s)| ≤ 1 := by
  have ht : |ϕ x s| ≤ 1 := abs_le.mpr hϕ
  have hr : |y - s| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hy.1, hs.2], by linarith [hy.2, hs.1]⟩
  rw [abs_mul, abs_mul, abs_sgnB, one_mul]
  calc
    |ϕ x s| * |y - s| ≤ 1 * |y - s| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    _ ≤ 1 := by simpa only [one_mul] using hr

/-- The crude terminal bound used when the learning rate is capped at one. -/
lemma abs_residSums_terminal_le (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (z : Fin N → X × ℝ) (ϕ : X → ℝ → ℝ) (b : Bool)
    (hϕ : ∀ x, ∀ s ∈ Set.Icc (0 : ℝ) 1, ϕ x s ∈ Set.Icc (-1 : ℝ) 1)
    (hz : ∀ t, (z t).2 ∈ Set.Icc (0 : ℝ) 1)
    (hs : ∀ t, onlineScore N Φ z t ∈ Set.Icc (0 : ℝ) 1) :
    |residSums N Φ z N ϕ b| ≤ N := by
  rw [residSums_terminal]
  calc
    |∑ t : Fin N, sgnB b * ϕ (z t).1 (onlineScore N Φ z t) *
        ((z t).2 - onlineScore N Φ z t)| ≤
      ∑ t : Fin N, |sgnB b * ϕ (z t).1 (onlineScore N Φ z t) *
        ((z t).2 - onlineScore N Φ z t)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact abs_increment_le_one ϕ (z t).1 (z t).2 (onlineScore N Φ z t) b
        (hϕ _ _ (hs t)) (hz t) (hs t)
    _ = N := by simp

end CalibratedMA.Randomized.OnlineState

end

-- Solutions.MainProcess
section

open MeasureTheory

namespace CalibratedMA.Randomized.MainProcess

variable {X : Type*}

abbrev Index (X : Type*) := (X → ℝ) ⊕ (Finset ℕ × Finset ℕ)

/-- The finite family tested by the concentration argument: original group
tests and represented partition/sign candidates. -/
noncomputable def family (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ)) : Finset (Index X) :=
  G.disjSum (MainCandidates.candidates (algM n δ ^ 2) (4 * algM n δ + 2))

lemma family_nonempty (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ)) :
    (family n δ G).Nonempty := by
  obtain ⟨ST, hST⟩ := MainCandidates.candidates_nonempty (algM n δ ^ 2)
    (4 * algM n δ + 2) (MainCandidatesRegularity.algM_sq_pos n δ) (by omega)
  exact ⟨Sum.inr ST, Finset.inr_mem_disjSum.mpr hST⟩

/-- A bounded predictable process. The current label is clamped so bounds hold
on every input, while values agree with the actual residual on admissible labels. -/
noncomputable def process (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ))
    (i : Index X) (t : Fin n) (ω : Fin n → X × ℝ) (z : X × ℝ) : ℝ :=
  let s := onlineRule n (algTests n δ G) ω t z.1
  match i with
  | .inl g => g z.1 * (clamp01 z.2 - s)
  | .inr ST =>
      let Γ := partitionOfIndexSet (algM n δ ^ 2) ST.1
      ∫ p, signTest (algM n δ ^ 2) ST.2 p * (clamp01 z.2 - p) ∂(roundMeasure Γ.1 Γ.2 s)

/-- Atomic rounding residuals are jointly measurable in the label and score;
the test need not be measurable away from the countable knot sequence. -/
lemma measurable_rounding_residual (M : ℕ) (γ : ℕ → ℝ) (h : ℝ → ℝ) :
    Measurable (fun w : ℝ × ℝ => ∫ p, h p * (w.1 - p) ∂(roundMeasure M γ w.2)) := by
  have hj : Measurable (fun w : ℝ × ℝ => roundIndex M γ w.2) :=
    (MainCandidatesRegularity.measurable_roundIndex M γ).comp measurable_snd
  have hw : Measurable (fun w : ℝ × ℝ => roundWeight M γ w.2) :=
    (MainCandidatesRegularity.measurable_roundWeight M γ).comp measurable_snd
  have hl : Measurable (fun w : ℝ × ℝ => γ (roundIndex M γ w.2)) :=
    (measurable_of_countable γ).comp hj
  have hr : Measurable (fun w : ℝ × ℝ => γ (roundIndex M γ w.2 + 1)) :=
    (measurable_of_countable (fun j : ℕ => γ (j + 1))).comp hj
  have hhl : Measurable (fun w : ℝ × ℝ => h (γ (roundIndex M γ w.2))) :=
    (measurable_of_countable (fun j : ℕ => h (γ j))).comp hj
  have hhr : Measurable (fun w : ℝ × ℝ => h (γ (roundIndex M γ w.2 + 1))) :=
    (measurable_of_countable (fun j : ℕ => h (γ (j + 1)))).comp hj
  have heq : (fun w : ℝ × ℝ => ∫ p, h p * (w.1 - p) ∂(roundMeasure M γ w.2)) =
      (fun w => (1 - roundWeight M γ w.2) *
          (h (γ (roundIndex M γ w.2)) * (w.1 - γ (roundIndex M γ w.2))) +
        roundWeight M γ w.2 *
          (h (γ (roundIndex M γ w.2 + 1)) * (w.1 - γ (roundIndex M γ w.2 + 1)))) := by
    funext w
    exact MainCandidatesRegularity.integral_roundMeasure_test M γ w.2 _
  rw [heq]
  exact ((measurable_const.sub hw).mul (hhl.mul (measurable_fst.sub hl))).add
    (hw.mul (hhr.mul (measurable_fst.sub hr)))

lemma bounded_residual (a y p : ℝ) (ha : a ∈ Set.Icc (-1 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    a * (y - p) ∈ Set.Icc (-1 : ℝ) 1 := by
  apply abs_le.mp
  rw [abs_mul]
  have hdiff : |y - p| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1, hp.2], by linarith [hy.2, hp.1]⟩
  simpa only [one_mul] using mul_le_mul (abs_le.mpr ha) hdiff
    (abs_nonneg (y - p)) (by norm_num : (0 : ℝ) ≤ 1)

lemma rounding_residual_mem (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ)
    (h : ℝ → ℝ) (hh : ∀ p, h p ∈ Set.Icc (-1 : ℝ) 1)
    (y s : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (∫ p, h p * (y - p) ∂(roundMeasure M γ s)) ∈ Set.Icc (-1 : ℝ) 1 := by
  exact MainCandidatesRegularity.liftTest_mem K M γ hΓ _
    (fun j hj => bounded_residual _ y _ (hh _) hy
      (MainCandidatesRegularity.grid_point_mem K M γ hΓ j hj)) s

/-- Each member of the process family is jointly measurable in the training
sequence and the current example. -/
lemma measurable_process [MeasurableSpace X] (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ))
    (hG : ∀ g ∈ G, Measurable g) (i : Index X) (hi : i ∈ family n δ G) (t : Fin n) :
    Measurable (fun w : (Fin n → X × ℝ) × (X × ℝ) => process n δ G i t w.1 w.2) := by
  have hpairs : Measurable (fun w : (Fin n → X × ℝ) × (X × ℝ) => (w.1, w.2.1)) :=
    measurable_fst.prodMk measurable_snd.fst
  have hs := (MainMeasurability.measurable_alg_onlineRule_joint n δ G hG t).comp hpairs
  have hy : Measurable (fun w : (Fin n → X × ℝ) × (X × ℝ) => clamp01 w.2.2) :=
    MainCandidatesRegularity.continuous_clamp01.measurable.comp measurable_snd.snd
  cases i with
  | inl g =>
    have hg : g ∈ G := Finset.inl_mem_disjSum.mp hi
    have h := ((hG g hg).comp measurable_snd.fst).mul (hy.sub hs)
    convert h using 1
    funext w
    simp only [process, Function.comp_apply, Pi.mul_apply, Pi.sub_apply]
  | inr ST =>
    have h := (measurable_rounding_residual
      (partitionOfIndexSet (algM n δ ^ 2) ST.1).1
      (partitionOfIndexSet (algM n δ ^ 2) ST.1).2
      (signTest (algM n δ ^ 2) ST.2)).comp (hy.prodMk hs)
    simpa only [process, Function.comp_def] using h

/-- Clamping the current label gives a global bound, regardless of the labels
appearing in the training sequence. -/
lemma process_mem (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ))
    (hG : ∀ g ∈ G, ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1)
    (i : Index X) (hi : i ∈ family n δ G) (t : Fin n)
    (ω : Fin n → X × ℝ) (z : X × ℝ) :
    process n δ G i t ω z ∈ Set.Icc (-1 : ℝ) 1 := by
  have hy := MainCandidatesRegularity.clamp01_mem z.2
  cases i with
  | inl g =>
    have hg : g ∈ G := Finset.inl_mem_disjSum.mp hi
    exact bounded_residual _ _ _ (hG g hg z.1) hy
      (MainMeasurability.onlineRule_mem n (algTests n δ G) ω t z.1)
  | inr ST =>
    have hST : ST ∈ MainCandidates.candidates (algM n δ ^ 2) (4 * algM n δ + 2) :=
      Finset.inr_mem_disjSum.mp hi
    obtain ⟨hS, hzero, hlast, _, _⟩ := (MainCandidates.mem_candidates _ _ ST).mp hST
    have hΓ := MainCandidatesGrid.partitionOfIndexSet_isGridPartition _ ST.1
      (MainCandidatesRegularity.algM_sq_pos n δ) hS hzero hlast
    exact rounding_residual_mem _ _ _ hΓ _
      (MainCandidatesRegularity.signTest_mem _ ST.2) _ _ hy

/-- The process at round `t` depends on the training sequence only before `t`. -/
lemma process_history (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ))
    (i : Index X) (t : Fin n) (ω ω' : Fin n → X × ℝ)
    (hhistory : ∀ s : Fin n, (s : ℕ) < (t : ℕ) → ω s = ω' s) (z : X × ℝ) :
    process n δ G i t ω z = process n δ G i t ω' z := by
  have h := OnlineState.onlineRule_history n (algTests n δ G) ω ω' t hhistory
  cases i <;> simp only [process, h]

lemma process_abs_le_one (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ))
    (hG : ∀ g ∈ G, ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1)
    (i : Index X) (hi : i ∈ family n δ G) (t : Fin n)
    (ω : Fin n → X × ℝ) (z : X × ℝ) : |process n δ G i t ω z| ≤ 1 :=
  abs_le.mpr (process_mem n δ G hG i hi t ω z)

end CalibratedMA.Randomized.MainProcess

end

-- Solutions.MainTransfer
section

open MeasureTheory

namespace CalibratedMA.Randomized.MainTransfer

variable {X : Type*} [MeasurableSpace X]

lemma abs_le_of_deviation (a b B ε : ℝ) (hdev : |a - b| ≤ ε) (hb : |b| ≤ B) :
    |a| ≤ B + ε := by
  have htri : |a| ≤ |a - b| + |b| := by
    have heq : a - b + b = a := by ring
    simpa only [heq] using abs_add_le (a - b) b
  linarith

/-- Deterministic transfer from the empirical guarantees and the finite-family
uniform deviation event to calibrated multiaccuracy of Algorithm 1. -/
lemma algorithm_cma_le (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, z.2 ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ)) (hn : 2 ≤ n)
    (hGm : ∀ g ∈ G, Measurable g)
    (hGb : ∀ g ∈ G, ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1)
    (ω : Fin n → X × ℝ) (hω : ∀ t, (ω t).2 ∈ Set.Icc (0 : ℝ) 1)
    (hΓ : IsGridPartition (algM n δ ^ 2) (algPartition n δ G ω).1
      (algPartition n δ G ω).2)
    (hcount : (algPartition n δ G ω).1 ≤ 4 * algM n δ + 2)
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hcal : ∀ h : ℝ → ℝ,
      (∀ j ≤ (algPartition n δ G ω).1,
        h ((algPartition n δ G ω).2 j) = 1 ∨ h ((algPartition n δ G ω).2 j) = -1) →
      |(1 / (n : ℝ)) * ∑ t : Fin n,
        (∫ p, h p * ((ω t).2 - p) ∂roundMeasure
          (algPartition n δ G ω).1 (algPartition n δ G ω).2
          (onlineScore n (algTests n δ G) ω t))| ≤ B)
    (hgroup : ∀ g ∈ G,
      |(1 / (n : ℝ)) * ∑ t : Fin n,
        g (ω t).1 * ((ω t).2 - onlineScore n (algTests n δ G) ω t)| ≤ B)
    (hgood : ∀ i ∈ MainProcess.family n δ G,
      |(∑ t : Fin n, ∫ z, MainProcess.process n δ G i t ω z ∂D) / (n : ℝ) -
        (∑ t : Fin n, MainProcess.process n δ G i t ω (ω t)) / (n : ℝ)| ≤ ε) :
    IsRandomizedPredictor (algorithm1 n δ G ω) ∧ CMA D (algorithm1 n δ G ω) G ≤ B + ε := by
  let Γ := algPartition n δ G ω
  let s : Fin n → X → ℝ := fun t => onlineRule n (algTests n δ G) ω t
  let Q := MainPopulation.mixture n Γ.1 Γ.2 s
  have hn1 : 1 ≤ n := by omega
  have hs (t : Fin n) : Measurable (s t) :=
    MainMeasurability.measurable_alg_onlineRule n δ G hGm ω t
  have hs_mem (t : Fin n) (x : X) : s t x ∈ Set.Icc (0 : ℝ) 1 :=
    MainMeasurability.onlineRule_mem n (algTests n δ G) ω t x
  have hQ : IsRandomizedPredictor Q :=
    MainPopulation.mixture_predictor (algM n δ ^ 2) Γ.1 n hn1 Γ.2 hΓ s hs
  change IsRandomizedPredictor Q ∧ CMA D Q G ≤ B + ε
  refine ⟨hQ, ?_⟩
  apply MainPopulation.CMA_le_of_residual_bounds D hD Q hQ G (B + ε) (add_nonneg hB hε)
  · intro g hg
    have hi : Sum.inl g ∈ MainProcess.family n δ G := Finset.inl_mem_disjSum.mpr hg
    have hpop_t (t : Fin n) :
        (∫ z, MainProcess.process n δ G (.inl g) t ω z ∂D) =
          ∫ z, ∫ p, g z.1 * (z.2 - p) ∂roundMeasure Γ.1 Γ.2 (s t z.1) ∂D := by
      apply integral_congr_ae
      filter_upwards [hD] with z hz
      change g z.1 * (clamp01 z.2 - s t z.1) = _
      rw [MainCandidatesRegularity.clamp01_eq_of_mem hz,
        MainPopulation.rounded_input_residual (algM n δ ^ 2) Γ.1 Γ.2 hΓ
          (s t z.1) z.2 (g z.1) (hs_mem t z.1)]
    have hobs_t (t : Fin n) : MainProcess.process n δ G (.inl g) t ω (ω t) =
        g (ω t).1 * ((ω t).2 - onlineScore n (algTests n δ G) ω t) := by
      change g (ω t).1 * (clamp01 (ω t).2 - s t (ω t).1) = _
      rw [MainCandidatesRegularity.clamp01_eq_of_mem (hω t)]
      rfl
    have hgm : Measurable (Function.uncurry (fun x (_ : ℝ) => g x)) :=
      (hGm g hg).comp measurable_fst
    have hmix := MainPopulation.mixture_residual D hD (algM n δ ^ 2) Γ.1 n hn1 Γ.2
      hΓ s hs (fun x (_ : ℝ) => g x) hgm (fun x _ _ => abs_le.mpr (hGb g hg x))
    have hpop : (∫ w, g w.1 * (w.2.1 - w.2.2) ∂jointLaw D Q) =
        (∑ t : Fin n, ∫ z, MainProcess.process n δ G (.inl g) t ω z ∂D) / (n : ℝ) := by
      rw [hmix]
      simp_rw [hpop_t]
      ring
    have hobs : |(∑ t : Fin n, MainProcess.process n δ G (.inl g) t ω (ω t)) /
        (n : ℝ)| ≤ B := by
      simp_rw [hobs_t]
      simpa only [div_eq_mul_inv, one_div, mul_comm, mul_one] using hgroup g hg
    rw [hpop]
    exact abs_le_of_deviation _ _ B ε (hgood (.inl g) hi) hobs
  · intro h hhm hsign
    obtain ⟨ST, hST, hrep⟩ := MainCandidates.exists_candidate_rounded_residual
      (algM n δ ^ 2) (4 * algM n δ + 2) Γ.1 Γ.2
      (MainCandidatesRegularity.algM_sq_pos n δ) hΓ hcount h
      (fun j _ => hsign (Γ.2 j))
    have hi : Sum.inr ST ∈ MainProcess.family n δ G := Finset.inr_mem_disjSum.mpr hST
    have hpop_t (t : Fin n) :
        (∫ z, MainProcess.process n δ G (.inr ST) t ω z ∂D) =
          ∫ z, ∫ p, h p * (z.2 - p) ∂roundMeasure Γ.1 Γ.2 (s t z.1) ∂D := by
      apply integral_congr_ae
      filter_upwards [hD] with z hz
      change (∫ p, signTest (algM n δ ^ 2) ST.2 p * (clamp01 z.2 - p) ∂roundMeasure
        (partitionOfIndexSet (algM n δ ^ 2) ST.1).1
        (partitionOfIndexSet (algM n δ ^ 2) ST.1).2 (s t z.1)) = _
      rw [MainCandidatesRegularity.clamp01_eq_of_mem hz]
      exact (hrep (s t z.1) z.2).symm
    have hobs_t (t : Fin n) : MainProcess.process n δ G (.inr ST) t ω (ω t) =
        ∫ p, h p * ((ω t).2 - p) ∂roundMeasure Γ.1 Γ.2
          (onlineScore n (algTests n δ G) ω t) := by
      change (∫ p, signTest (algM n δ ^ 2) ST.2 p * (clamp01 (ω t).2 - p) ∂roundMeasure
        (partitionOfIndexSet (algM n δ ^ 2) ST.1).1
        (partitionOfIndexSet (algM n δ ^ 2) ST.1).2 (s t (ω t).1)) = _
      rw [MainCandidatesRegularity.clamp01_eq_of_mem (hω t)]
      exact (hrep (s t (ω t).1) (ω t).2).symm
    have hhm' : Measurable (Function.uncurry (fun (_ : X) p => h p)) :=
      hhm.comp measurable_snd
    have hhbound : ∀ (_x : X), ∀ p ∈ Set.Icc (0 : ℝ) 1, |h p| ≤ 1 := by
      intro x p hp
      rcases hsign p with hp | hp <;> simp [hp]
    have hmix := MainPopulation.mixture_residual D hD (algM n δ ^ 2) Γ.1 n hn1 Γ.2
      hΓ s hs (fun (_ : X) p => h p) hhm' hhbound
    have hpop : (∫ w, h w.2.2 * (w.2.1 - w.2.2) ∂jointLaw D Q) =
        (∑ t : Fin n, ∫ z, MainProcess.process n δ G (.inr ST) t ω z ∂D) / (n : ℝ) := by
      rw [hmix]
      simp_rw [hpop_t]
      ring
    have hobs : |(∑ t : Fin n, MainProcess.process n δ G (.inr ST) t ω (ω t)) /
        (n : ℝ)| ≤ B := by
      simp_rw [hobs_t]
      simpa only [div_eq_mul_inv, one_div, mul_comm, mul_one, Γ] using
        hcal h (fun j _ => hsign ((algPartition n δ G ω).2 j))
    rw [hpop]
    exact (le_abs_self _).trans
      (abs_le_of_deviation _ _ B ε (hgood (.inr ST) hi) hobs)

end CalibratedMA.Randomized.MainTransfer

end

-- Solutions.MainSampleBounds
section

open MeasureTheory

namespace CalibratedMA.Randomized.MainSampleBounds

universe u

/-- Algorithm 1's empirical guarantees hold deterministically on every sample
with labels in the unit interval, with a universal constant. -/
theorem exists_empirical_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type u) (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ)),
        2 ≤ n → (∀ g ∈ G, ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) →
        ∀ (ω : Fin n → X × ℝ), (∀ t, (ω t).2 ∈ Set.Icc (0 : ℝ) 1) →
          IsGridPartition (algM n δ ^ 2) (algPartition n δ G ω).1
            (algPartition n δ G ω).2 ∧
          (algPartition n δ G ω).1 ≤ 4 * algM n δ + 2 ∧
          (∀ h : ℝ → ℝ,
            (∀ j ≤ (algPartition n δ G ω).1,
              h ((algPartition n δ G ω).2 j) = 1 ∨
                h ((algPartition n δ G ω).2 j) = -1) →
            |(1 / (n : ℝ)) * ∑ t : Fin n,
              (∫ p, h p * ((ω t).2 - p) ∂roundMeasure
                (algPartition n δ G ω).1 (algPartition n δ G ω).2
                (onlineScore n (algTests n δ G) ω t))| ≤
              C * (Real.sqrt (Real.log (2 * ((algTests n δ G).card : ℝ)) / n) +
                1 / (algM n δ : ℝ) ^ 2)) ∧
          (∀ g ∈ G,
            |(1 / (n : ℝ)) * ∑ t : Fin n,
              g (ω t).1 * ((ω t).2 - onlineScore n (algTests n δ G) ω t)| ≤
              C * (Real.sqrt (Real.log (2 * ((algTests n δ G).card : ℝ)) / n) +
                1 / (algM n δ : ℝ) ^ 2)) := by
  obtain ⟨Cl, hCl, hlearn⟩ := lemma_3_1.{u}
  obtain ⟨Cr, hCr, hround⟩ := lemma_3_4
  refine ⟨Cl + Cr, by positivity, ?_⟩
  intro X n δ G hn hG ω hω
  classical
  let m := algM n δ
  let Φ := algTests n δ G
  let S : Fin n → ℝ := onlineScore n Φ ω
  let ν := MainEmpirical.empiricalScores n S
  let Γ := algPartition n δ G ω
  have hn1 : 1 ≤ n := by omega
  have hm : 2 ≤ m := le_max_left _ _
  have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hK : 1 ≤ m ^ 2 := by nlinarith
  have hlearner := hlearn X n Φ hn1
    (MainCandidatesRegularity.algTests_nonempty n δ G)
    (fun ϕ hϕ x => MainCandidatesRegularity.algTests_continuous n δ G ϕ hϕ x)
    (fun ϕ hϕ x p _ => MainCandidatesRegularity.algTests_bounded n δ G hG ϕ hϕ x p)
  have hS : ∀ t, S t ∈ Set.Icc (0 : ℝ) 1 :=
    fun t => hlearner.2.1 ω t (ω t).1
  have hνprob : IsProbabilityMeasure ν := MainEmpirical.empiricalScores_probability n hn1 S
  have hνsupport : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0 :=
    MainEmpirical.empiricalScores_support n S hS
  have hρ : (1 : ℝ) / (m ^ 2 : ℕ) ≤ ((m : ℝ) ^ 2)⁻¹ := by
    simp only [Nat.cast_pow, one_div, le_refl]
  have hgreedy := hround ν hνprob hνsupport (m : ℝ) (m ^ 2) hmreal hK hρ
  have hΓ : IsGridPartition (m ^ 2) Γ.1 Γ.2 := hgreedy.1
  have hcount : Γ.1 ≤ 4 * m + 2 := by exact_mod_cast hgreedy.2.1
  have herr : RoundErr ν Γ.1 Γ.2 ≤ Cr / (m : ℝ) ^ 2 := hgreedy.2.2
  have hroot : 0 ≤ Real.sqrt (Real.log (2 * (Φ.card : ℝ)) / n) := Real.sqrt_nonneg _
  have hinv : 0 ≤ 1 / (m : ℝ) ^ 2 := by positivity
  refine ⟨hΓ, hcount, ?_, ?_⟩
  · intro h hh
    change ∀ j ≤ Γ.1, h (Γ.2 j) = 1 ∨ h (Γ.2 j) = -1 at hh
    have hlift : liftTest Γ.1 Γ.2 h ∈ liftedClass (m ^ 2) (4 * m + 2) :=
      MainCandidates.liftTest_mem_liftedClass (m ^ 2) (4 * m + 2) Γ.1 Γ.2 hK hΓ hcount h hh
    have htest : (fun (_ : X) s => liftTest Γ.1 Γ.2 h s) ∈ Φ := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨liftTest Γ.1 Γ.2 h, hlift, rfl⟩
    have hlearned := hlearner.2.2 ω hω _ htest
    have hhbound : ∀ j ≤ Γ.1, h (Γ.2 j) ∈ Set.Icc (-1 : ℝ) 1 := by
      intro j hj
      rcases hh j hj with heq | heq <;> simp [heq]
    have he := MainEmpirical.empirical_calibration_bound (m ^ 2) Γ.1 n hn1 Γ.2 hΓ
      S (fun t => (ω t).2) hS h hhbound
      (Cl * Real.sqrt (Real.log (2 * (Φ.card : ℝ)) / n)) hlearned
    change |(1 / (n : ℝ)) * ∑ t : Fin n,
      (∫ p, h p * ((ω t).2 - p) ∂roundMeasure Γ.1 Γ.2 (S t))| ≤
        (Cl + Cr) * (Real.sqrt (Real.log (2 * (Φ.card : ℝ)) / n) + 1 / (m : ℝ) ^ 2)
    apply he.trans
    apply (add_le_add (le_refl _) herr).trans
    have hcross₁ := mul_nonneg hCl.le hinv
    have hcross₂ := mul_nonneg hCr.le hroot
    simp only [div_eq_mul_inv, one_mul] at hcross₁ hcross₂ ⊢
    nlinarith only [hcross₁, hcross₂]
  · intro g hg
    have htest : (fun x (_ : ℝ) => g x) ∈ Φ := by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨g, hg, rfl⟩
    have hlearned := hlearner.2.2 ω hω _ htest
    apply hlearned.trans
    change Cl * Real.sqrt (Real.log (2 * (Φ.card : ℝ)) / n) ≤
      (Cl + Cr) * (Real.sqrt (Real.log (2 * (Φ.card : ℝ)) / n) + 1 / (m : ℝ) ^ 2)
    have hcross₁ := mul_nonneg (add_pos hCl hCr).le hinv
    have hcross₂ := mul_nonneg hCr.le hroot
    nlinarith only [hcross₁, hcross₂]

end CalibratedMA.Randomized.MainSampleBounds

end

-- Solutions.MainOptimization
section

namespace CalibratedMA.Randomized.MainOptimization

/-- The confidence logarithm dominates both one and `log n`. -/
lemma confidence_log_bounds (n : ℕ) (δ : ℝ) (hn : 2 ≤ n) (hδ : 0 < δ)
    (hδhalf : δ < 1 / 2) :
    1 ≤ Real.log (2 * (n : ℝ) / δ) ∧
      Real.log (n : ℝ) ≤ Real.log (2 * (n : ℝ) / δ) := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hfour : (4 : ℝ) ≤ 2 * n / δ := by
    apply (le_div_iff₀ hδ).2
    linarith
  have hnratio : (n : ℝ) ≤ 2 * n / δ := by
    apply (le_div_iff₀ hδ).2
    nlinarith
  refine ⟨?_, Real.log_le_log hnpos hnratio⟩
  apply (Real.le_log_iff_exp_le (by positivity : 0 < 2 * (n : ℝ) / δ)).2
  exact Real.exp_one_lt_three.le.trans (by linarith)

lemma algM_ge_two (n : ℕ) (δ : ℝ) : 2 ≤ algM n δ := le_max_left _ _

/-- The chosen integer scale is at least the balancing real scale. -/
lemma root_le_algM (n : ℕ) (δ : ℝ) :
    ((n : ℝ) / Real.log (2 * n / δ)) ^ (1 / 5 : ℝ) ≤ (algM n δ : ℝ) := by
  exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))

/-- The chosen integer scale never exceeds the sample size. -/
lemma algM_le_n (n : ℕ) (δ : ℝ) (hn : 2 ≤ n) (hδ : 0 < δ)
    (hδhalf : δ < 1 / 2) : algM n δ ≤ n := by
  have hL := (confidence_log_bounds n δ hn hδ hδhalf).1
  have hLpos : 0 < Real.log (2 * (n : ℝ) / δ) := by linarith
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hx : (n : ℝ) / Real.log (2 * n / δ) ≤ n := by
    apply (div_le_iff₀ hLpos).2
    nlinarith
  have hroot : ((n : ℝ) / Real.log (2 * n / δ)) ^ (1 / 5 : ℝ) ≤ n :=
    (Real.rpow_le_rpow (by positivity) hx (by norm_num)).trans
      (Real.rpow_le_self_of_one_le hnreal (by norm_num))
  exact max_le hn (Nat.ceil_le.mpr hroot)

/-- In the nontrivial regime, the integer scale is at most three times the real scale. -/
lemma algM_le_three_root (n : ℕ) (δ : ℝ) (hn : 2 ≤ n) (hδ : 0 < δ)
    (hδhalf : δ < 1 / 2) (hlarge : Real.log (2 * (n : ℝ) / δ) ≤ n) :
    (algM n δ : ℝ) ≤ 3 * (((n : ℝ) / Real.log (2 * n / δ)) ^ (1 / 5 : ℝ)) := by
  have hL := (confidence_log_bounds n δ hn hδ hδhalf).1
  have hLpos : 0 < Real.log (2 * (n : ℝ) / δ) := by linarith
  have hx : 1 ≤ (n : ℝ) / Real.log (2 * n / δ) := by
    apply (le_div_iff₀ hLpos).2
    simpa only [one_mul] using hlarge
  have ht : 1 ≤ ((n : ℝ) / Real.log (2 * n / δ)) ^ (1 / 5 : ℝ) :=
    Real.one_le_rpow hx (by norm_num)
  have hceil := Nat.ceil_lt_add_one (by linarith :
    0 ≤ ((n : ℝ) / Real.log (2 * n / δ)) ^ (1 / 5 : ℝ))
  rw [algM, Nat.cast_max, Nat.cast_ofNat]
  apply max_le <;> linarith

/-- The logarithmic complexity of the chosen grid is controlled by the confidence logarithm. -/
lemma log_grid_le (n : ℕ) (δ : ℝ) (hn : 2 ≤ n) (hδ : 0 < δ)
    (hδhalf : δ < 1 / 2) :
    Real.log (Real.exp 1 * (algM n δ : ℝ) ^ 2) ≤
      3 * Real.log (2 * (n : ℝ) / δ) := by
  obtain ⟨hL, hlogn⟩ := confidence_log_bounds n δ hn hδ hδhalf
  have hmreal : (2 : ℝ) ≤ algM n δ := by exact_mod_cast algM_ge_two n δ
  have hmpos : (0 : ℝ) < algM n δ := by linarith
  have hmn : (algM n δ : ℝ) ≤ n := by exact_mod_cast algM_le_n n δ hn hδ hδhalf
  have hlogm : Real.log (algM n δ : ℝ) ≤ Real.log (2 * (n : ℝ) / δ) :=
    (Real.log_le_log hmpos hmn).trans hlogn
  rw [Real.log_mul (Real.exp_ne_zero 1) (pow_ne_zero 2 (ne_of_gt hmpos)),
    Real.log_exp, Real.log_pow]
  norm_num
  linarith

/-- The two-fifths rate is the reciprocal square of the one-fifth balancing scale. -/
lemma inverse_root_sq (x : ℝ) (hx : 0 < x) :
    1 / (x ^ (1 / 5 : ℝ)) ^ 2 = (x⁻¹) ^ (2 / 5 : ℝ) := by
  have hp : (x ^ (1 / 5 : ℝ)) ^ 2 = x ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_mul_natCast hx.le]
    norm_num
  rw [hp, one_div, Real.inv_rpow hx.le]

/-- The stochastic error at the balancing scale is the square of the two-fifths rate. -/
lemma root_balance (x : ℝ) (hx : 0 < x) :
    x ^ (1 / 5 : ℝ) / x = ((x⁻¹) ^ (2 / 5 : ℝ)) ^ 2 := by
  have hp : ((x⁻¹) ^ (2 / 5 : ℝ)) ^ 2 = (x⁻¹) ^ (4 / 5 : ℝ) := by
    rw [← Real.rpow_mul_natCast (inv_nonneg.mpr hx.le)]
    norm_num
  rw [hp, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]
  rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hx]
  norm_num

/-- The deterministic grid error is at most the target rate. -/
lemma inverse_algM_sq_le_rate (n : ℕ) (δ : ℝ) (hn : 2 ≤ n) (hδ : 0 < δ)
    (hδhalf : δ < 1 / 2) :
    1 / (algM n δ : ℝ) ^ 2 ≤
      (Real.log (2 * (n : ℝ) / δ) / n) ^ (2 / 5 : ℝ) := by
  have hL := (confidence_log_bounds n δ hn hδ hδhalf).1
  have hLpos : 0 < Real.log (2 * (n : ℝ) / δ) := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx : 0 < (n : ℝ) / Real.log (2 * n / δ) := div_pos hnpos hLpos
  have ht := Real.rpow_pos_of_pos hx (1 / 5 : ℝ)
  have htm := root_le_algM n δ
  have hsq : (((n : ℝ) / Real.log (2 * n / δ)) ^ (1 / 5 : ℝ)) ^ 2 ≤
      (algM n δ : ℝ) ^ 2 := by nlinarith
  calc
    1 / (algM n δ : ℝ) ^ 2 ≤
        1 / (((n : ℝ) / Real.log (2 * n / δ)) ^ (1 / 5 : ℝ)) ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos ht) hsq
    _ = (Real.log (2 * (n : ℝ) / δ) / n) ^ (2 / 5 : ℝ) := by
      simpa only [inv_div] using inverse_root_sq _ hx

/-- The squared stochastic grid term is at most nine times the squared target rate. -/
lemma grid_complexity_div_le_rate_sq (n : ℕ) (δ : ℝ) (hn : 2 ≤ n) (hδ : 0 < δ)
    (hδhalf : δ < 1 / 2) (hlarge : Real.log (2 * (n : ℝ) / δ) ≤ n) :
    (algM n δ : ℝ) * Real.log (Real.exp 1 * (algM n δ : ℝ) ^ 2) / n ≤
      9 * ((Real.log (2 * (n : ℝ) / δ) / n) ^ (2 / 5 : ℝ)) ^ 2 := by
  have hL := (confidence_log_bounds n δ hn hδ hδhalf).1
  have hLpos : 0 < Real.log (2 * (n : ℝ) / δ) := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx : 0 < (n : ℝ) / Real.log (2 * n / δ) := div_pos hnpos hLpos
  have htm := algM_le_three_root n δ hn hδ hδhalf hlarge
  have hlog := log_grid_le n δ hn hδ hδhalf
  have hprod : (algM n δ : ℝ) * Real.log (Real.exp 1 * (algM n δ : ℝ) ^ 2) ≤
      (3 * (((n : ℝ) / Real.log (2 * n / δ)) ^ (1 / 5 : ℝ))) *
        (3 * Real.log (2 * (n : ℝ) / δ)) :=
    (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right htm (by positivity))
  calc
    _ ≤ (3 * (((n : ℝ) / Real.log (2 * n / δ)) ^ (1 / 5 : ℝ))) *
        (3 * Real.log (2 * (n : ℝ) / δ)) / n := div_le_div_of_nonneg_right hprod hnpos.le
    _ = 9 * (((n : ℝ) / Real.log (2 * n / δ)) ^ (1 / 5 : ℝ) /
        ((n : ℝ) / Real.log (2 * n / δ))) := by field_simp; ring
    _ = _ := by rw [root_balance _ hx, inv_div]

/-- The stochastic grid term is at most three times the target rate. -/
lemma sqrt_grid_complexity_le_rate (n : ℕ) (δ : ℝ) (hn : 2 ≤ n) (hδ : 0 < δ)
    (hδhalf : δ < 1 / 2) (hlarge : Real.log (2 * (n : ℝ) / δ) ≤ n) :
    Real.sqrt ((algM n δ : ℝ) * Real.log (Real.exp 1 * (algM n δ : ℝ) ^ 2) / n) ≤
      3 * (Real.log (2 * (n : ℝ) / δ) / n) ^ (2 / 5 : ℝ) := by
  have hL := (confidence_log_bounds n δ hn hδ hδhalf).1
  have hLpos : 0 < Real.log (2 * (n : ℝ) / δ) := by linarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [grid_complexity_div_le_rate_sq n δ hn hδ hδhalf hlarge]

/-- Universal-constant optimization of the integer grid used in Algorithm 1. -/
lemma optimized_grid_error (n : ℕ) (δ : ℝ) (hn : 2 ≤ n) (hδ : 0 < δ)
    (hδhalf : δ < 1 / 2) (hlarge : Real.log (2 * (n : ℝ) / δ) ≤ n) :
    Real.sqrt ((algM n δ : ℝ) * Real.log (Real.exp 1 * (algM n δ : ℝ) ^ 2) / n) +
      1 / (algM n δ : ℝ) ^ 2 ≤
      4 * (Real.log (2 * (n : ℝ) / δ) / n) ^ (2 / 5 : ℝ) := by
  linarith [sqrt_grid_complexity_le_rate n δ hn hδ hδhalf hlarge,
    inverse_algM_sq_le_rate n δ hn hδ hδhalf]

/-- In the complementary sample-size regime, the desired rate already exceeds one. -/
lemma one_le_rate_of_small (n : ℕ) (δ : ℝ) (hn : 0 < n)
    (hsmall : (n : ℝ) ≤ Real.log (2 * (n : ℝ) / δ)) :
    1 ≤ (Real.log (2 * (n : ℝ) / δ) / n) ^ (2 / 5 : ℝ) := by
  apply Real.one_le_rpow _ (by norm_num)
  apply (le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).2
  simpa only [one_mul] using hsmall

/-- A direct logarithmic bound for the polynomial counting bound from Equation (5). -/
lemma log_counting_bound (m q : ℕ) (hm : 2 ≤ m)
    (hq : q ≤ (4 * m + 3) * (2 * (m ^ 2 + 1)) ^ (4 * m + 3)) :
    Real.log (q : ℝ) ≤ 30 * m * Real.log (Real.exp 1 * (m : ℝ) ^ 2) := by
  have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg m
  have hgrid : Real.log (Real.exp 1 * (m : ℝ) ^ 2) = 1 + 2 * Real.log (m : ℝ) := by
    rw [Real.log_mul (Real.exp_ne_zero 1) (pow_ne_zero 2 (ne_of_gt hmpos)),
      Real.log_exp, Real.log_pow]
    norm_num
  rw [hgrid]
  by_cases hqzero : q = 0
  · simp only [hqzero, Nat.cast_zero, Real.log_zero]
    positivity
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero hqzero)
  have hbound : (q : ℝ) ≤ (4 * m + 3) * (2 * ((m : ℝ) ^ 2 + 1)) ^ (4 * m + 3) := by
    exact_mod_cast hq
  have hlogq := Real.log_le_log hqpos hbound
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlogq
  have hfirst : Real.log (4 * (m : ℝ) + 3) ≤ 5 * m := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 4 * (m : ℝ) + 3)
    linarith
  have hbase : Real.log (2 * ((m : ℝ) ^ 2 + 1)) ≤ 3 * (1 + 2 * Real.log (m : ℝ)) := by
    have hb : 2 * ((m : ℝ) ^ 2 + 1) ≤ 4 * (m : ℝ) ^ 2 := by nlinarith
    have h := Real.log_le_log (by positivity : 0 < 2 * ((m : ℝ) ^ 2 + 1)) hb
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (pow_ne_zero 2 (ne_of_gt hmpos)),
      Real.log_pow] at h
    have hfour := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at h hfour
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 4 * (m : ℝ) + 3 by positivity)
  have hsize : (4 * (m : ℝ) + 3) ≤ 6 * m := by linarith
  have hscaled' := mul_le_mul_of_nonneg_right hsize
    (show 0 ≤ 3 * (1 + 2 * Real.log (m : ℝ)) by positivity)
  push_cast at hlogq
  nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) by positivity) hlogm]

/-- Adding one to a possibly empty test class costs at most the confidence logarithm. -/
lemma log_card_succ_le (n g : ℕ) (δ : ℝ) (hn : 2 ≤ n) (hδ : 0 < δ)
    (hδhalf : δ < 1 / 2) :
    Real.log (2 * ((g : ℝ) + 1) / δ) ≤
      Real.log (2 * (g : ℝ) / δ) + Real.log (2 * (n : ℝ) / δ) := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL := (confidence_log_bounds n δ hn hδ hδhalf).1
  by_cases hg : g = 0
  · simp only [hg, Nat.cast_zero, zero_add, mul_one, mul_zero, zero_div, Real.log_zero]
    apply Real.log_le_log (by positivity : 0 < 2 / δ)
    exact div_le_div_of_nonneg_right (by linarith) hδ.le
  have hgone : (1 : ℝ) ≤ g := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hg)
  have hgpos : (0 : ℝ) < g := by linarith
  have hcomp : 2 * ((g : ℝ) + 1) / δ ≤ (2 * g / δ) * 2 := by
    apply (div_le_iff₀ hδ).2
    have heq : (2 * (g : ℝ) / δ * 2) * δ = 4 * g := by field_simp; ring
    rw [heq]
    linarith
  have h := Real.log_le_log (by positivity : 0 < 2 * ((g : ℝ) + 1) / δ) hcomp
  rw [Real.log_mul (by positivity : 2 * (g : ℝ) / δ ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)] at h
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at htwo
  linarith

/-- The square-root confidence term is dominated by the two-fifths rate when it is nontrivial. -/
lemma sqrt_confidence_le_rate (n : ℕ) (δ : ℝ) (hn : 2 ≤ n) (hδ : 0 < δ)
    (hδhalf : δ < 1 / 2) (hlarge : Real.log (2 * (n : ℝ) / δ) ≤ n) :
    Real.sqrt (Real.log (2 * (n : ℝ) / δ) / n) ≤
      (Real.log (2 * (n : ℝ) / δ) / n) ^ (2 / 5 : ℝ) := by
  have hL := (confidence_log_bounds n δ hn hδ hδhalf).1
  have hLpos : 0 < Real.log (2 * (n : ℝ) / δ) := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.sqrt_eq_rpow]
  apply Real.rpow_le_rpow_of_exponent_ge (div_pos hLpos hnpos) _ (by norm_num)
  exact (div_le_one hnpos).mpr hlarge

/-- The confidence term for a finite test class is nonnegative, including an empty class. -/
lemma log_test_card_nonneg (g : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    0 ≤ Real.log (2 * (g : ℝ) / δ) := by
  by_cases hg : g = 0
  · simp [hg]
  have hgpos : (1 : ℝ) ≤ g := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hg)
  apply Real.log_nonneg
  apply (le_div_iff₀ hδ).2
  linarith

/-- A union-cardinality logarithm splits without requiring either class to be nonempty. -/
lemma log_union_card_le (n g q : ℕ) (δ : ℝ) (hn : 2 ≤ n) (hδ : 0 < δ)
    (hδhalf : δ < 1 / 2) :
    Real.log (2 * ((g : ℝ) + q) / δ) ≤
      Real.log (2 * (g : ℝ) / δ) + Real.log (2 * (n : ℝ) / δ) + Real.log (q : ℝ) := by
  have hL := (confidence_log_bounds n δ hn hδ hδhalf).1
  by_cases hq : q = 0
  · simp only [hq, Nat.cast_zero, add_zero, Real.log_zero]
    linarith
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hq)
  have hqpos : (0 : ℝ) < q := by linarith
  have hcomp : 2 * ((g : ℝ) + q) / δ ≤ (2 * ((g : ℝ) + 1) / δ) * q := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hδ.le
    nlinarith [mul_nonneg (Nat.cast_nonneg g) (show 0 ≤ (q : ℝ) - 1 by linarith)]
  have h := Real.log_le_log (by positivity : 0 < 2 * ((g : ℝ) + q) / δ) hcomp
  rw [Real.log_mul (by positivity : 2 * ((g : ℝ) + 1) / δ ≠ 0) (ne_of_gt hqpos)] at h
  linarith [log_card_succ_le n g δ hn hδ hδhalf]

/-- The union of the given tests and the rounding candidates obeys the desired statistical rate. -/
lemma sqrt_union_card_le_rate (n g q : ℕ) (δ : ℝ) (hn : 2 ≤ n) (hδ : 0 < δ)
    (hδhalf : δ < 1 / 2) (hlarge : Real.log (2 * (n : ℝ) / δ) ≤ n)
    (hcount : Real.log (q : ℝ) ≤
      50 * (algM n δ : ℝ) * Real.log (Real.exp 1 * (algM n δ : ℝ) ^ 2)) :
    Real.sqrt (Real.log (2 * ((g : ℝ) + q) / δ) / n) ≤
      Real.sqrt (Real.log (2 * (g : ℝ) / δ) / n) +
        22 * (Real.log (2 * (n : ℝ) / δ) / n) ^ (2 / 5 : ℝ) := by
  have hL := (confidence_log_bounds n δ hn hδ hδhalf).1
  have hLpos : 0 < Real.log (2 * (n : ℝ) / δ) := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let R := (Real.log (2 * (n : ℝ) / δ) / n) ^ (2 / 5 : ℝ)
  let a := Real.sqrt (Real.log (2 * (g : ℝ) / δ) / n)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha_sq : a ^ 2 = Real.log (2 * (g : ℝ) / δ) / n :=
    Real.sq_sqrt (div_nonneg (log_test_card_nonneg g δ hδ hδhalf) hnpos.le)
  have hbase : Real.log (2 * (n : ℝ) / δ) / n ≤ R ^ 2 := by
    have h := sqrt_confidence_le_rate n δ hn hδ hδhalf hlarge
    have hs := Real.sq_sqrt (div_nonneg hLpos.le hnpos.le)
    change Real.sqrt (Real.log (2 * (n : ℝ) / δ) / n) ≤ R at h
    nlinarith [Real.sqrt_nonneg (Real.log (2 * (n : ℝ) / δ) / n)]
  have hgrid : (algM n δ : ℝ) * Real.log (Real.exp 1 * (algM n δ : ℝ) ^ 2) / n ≤
      9 * R ^ 2 := grid_complexity_div_le_rate_sq n δ hn hδ hδhalf hlarge
  have hqnorm : Real.log (q : ℝ) / n ≤ 450 * R ^ 2 := by
    have hc := div_le_div_of_nonneg_right hcount hnpos.le
    have hs := mul_le_mul_of_nonneg_left hgrid (show (0 : ℝ) ≤ 50 by norm_num)
    calc
      _ ≤ 50 * ((algM n δ : ℝ) * Real.log (Real.exp 1 * (algM n δ : ℝ) ^ 2) / n) := by
        simpa only [mul_div_assoc, mul_assoc] using hc
      _ ≤ _ := by linarith
  have htotal : Real.log (2 * ((g : ℝ) + q) / δ) / n ≤ a ^ 2 + 451 * R ^ 2 := by
    calc
      _ ≤ (Real.log (2 * (g : ℝ) / δ) + Real.log (2 * (n : ℝ) / δ) + Real.log (q : ℝ)) / n :=
        div_le_div_of_nonneg_right (log_union_card_le n g q δ hn hδ hδhalf) hnpos.le
      _ = Real.log (2 * (g : ℝ) / δ) / n +
          Real.log (2 * (n : ℝ) / δ) / n + Real.log (q : ℝ) / n := by ring
      _ ≤ _ := by rw [← ha_sq]; linarith
  change Real.sqrt (Real.log (2 * ((g : ℝ) + q) / δ) / n) ≤ a + 22 * R
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg ha hR, sq_nonneg R]

end CalibratedMA.Randomized.MainOptimization

end

-- Solutions.MainRates
section

namespace CalibratedMA.Randomized.MainRates

open MainCandidates MainOptimization

variable {X : Type*}

/-- The online family has at most one test per input test or candidate representation. -/
lemma algTests_card_le (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ)) :
    (algTests n δ G).card ≤ G.card +
      (candidates (algM n δ ^ 2) (4 * algM n δ + 2)).card := by
  classical
  have hm := algM_ge_two n δ
  have hK : 1 ≤ algM n δ ^ 2 := by nlinarith
  have hA : (liftedClass (algM n δ ^ 2) (4 * algM n δ + 2)).card ≤
      (candidates (algM n δ ^ 2) (4 * algM n δ + 2)).card := by
    rw [← candidates_image_eq_liftedClass _ _ hK]
    exact Finset.card_image_le
  unfold algTests testFamily
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_image_le (Finset.card_image_le.trans hA))

/-- The candidate count is positive, even when the supplied test class is empty. -/
lemma alg_candidates_card_pos (n : ℕ) (δ : ℝ) :
    0 < (candidates (algM n δ ^ 2) (4 * algM n δ + 2)).card := by
  have hm := algM_ge_two n δ
  exact Finset.card_pos.mpr (candidates_nonempty _ _ (by nlinarith) (by omega))

/-- The actual candidate count has the logarithmic complexity needed by the rate bound. -/
lemma log_alg_candidates_card_le (n : ℕ) (δ : ℝ) :
    Real.log (candidates (algM n δ ^ 2) (4 * algM n δ + 2)).card ≤
      50 * (algM n δ : ℝ) * Real.log (Real.exp 1 * (algM n δ : ℝ) ^ 2) := by
  have hm := algM_ge_two n δ
  have hK : 1 ≤ algM n δ ^ 2 := by nlinarith
  have hc := candidates_card_le_poly (algM n δ ^ 2) (4 * algM n δ + 2) hK
  have hp : (candidates (algM n δ ^ 2) (4 * algM n δ + 2)).card ≤
      (4 * algM n δ + 3) * (2 * (algM n δ ^ 2 + 1)) ^ (4 * algM n δ + 3) := by
    simpa only [Nat.add_assoc] using hc
  have hlog := log_counting_bound (algM n δ) _ hm hp
  have hmreal : (2 : ℝ) ≤ algM n δ := by exact_mod_cast hm
  have hgrid : 0 ≤ Real.log (Real.exp 1 * (algM n δ : ℝ) ^ 2) := by
    apply Real.log_nonneg
    have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
    nlinarith
  nlinarith [mul_nonneg (Nat.cast_nonneg (algM n δ)) hgrid]

/-- The confidence-free online complexity is bounded by the confidence-adjusted union complexity. -/
lemma sqrt_online_complexity_le (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ))
    (hn : 2 ≤ n) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hlarge : Real.log (2 * (n : ℝ) / δ) ≤ n) :
    Real.sqrt (Real.log (2 * ((algTests n δ G).card : ℝ)) / n) ≤
      Real.sqrt (Real.log (2 * (G.card : ℝ) / δ) / n) +
        22 * (Real.log (2 * (n : ℝ) / δ) / n) ^ (2 / 5 : ℝ) := by
  have hΦpos : (0 : ℝ) < (algTests n δ G).card := by
    exact_mod_cast (Finset.card_pos.mpr (MainCandidatesRegularity.algTests_nonempty n δ G))
  have hcard : ((algTests n δ G).card : ℝ) ≤ (G.card : ℝ) +
      (candidates (algM n δ ^ 2) (4 * algM n δ + 2)).card := by
    exact_mod_cast algTests_card_le n δ G
  have hcomp : 2 * ((algTests n δ G).card : ℝ) ≤
      2 * ((G.card : ℝ) + (candidates (algM n δ ^ 2) (4 * algM n δ + 2)).card) / δ := by
    apply (le_div_iff₀ hδ).2
    have hmul := mul_le_mul_of_nonneg_left (show δ ≤ 1 by linarith)
      (show 0 ≤ 2 * ((algTests n δ G).card : ℝ) by positivity)
    nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < 2 * ((algTests n δ G).card : ℝ)) hcomp
  exact (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n))).trans
    (sqrt_union_card_le_rate n G.card _ δ hn hδ hδhalf hlarge (log_alg_candidates_card_le n δ))

/-- The two-sided martingale radius is at most three times the normalized union complexity. -/
lemma sqrt_eight_mul_le (x : ℝ) : Real.sqrt (8 * x) ≤ 3 * Real.sqrt x := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg x)
  exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

/-- Complete deterministic numerical estimate for the main theorem's nontrivial regime. -/
lemma empirical_add_concentration_le (Cemp : ℝ) (hCemp : 0 < Cemp)
    (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ))
    (hn : 2 ≤ n) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hlarge : Real.log (2 * (n : ℝ) / δ) ≤ n) :
    Cemp * (Real.sqrt (Real.log (2 * ((algTests n δ G).card : ℝ)) / n) +
        1 / (algM n δ : ℝ) ^ 2) +
      Real.sqrt (8 * Real.log
        (2 * ((G.card : ℝ) + (candidates (algM n δ ^ 2) (4 * algM n δ + 2)).card) / δ) / n) ≤
      (24 * Cemp + 70) *
        (Real.sqrt (Real.log (2 * (G.card : ℝ) / δ) / n) +
          (Real.log (2 * (n : ℝ) / δ) / n) ^ (2 / 5 : ℝ)) := by
  let A := Real.sqrt (Real.log (2 * (G.card : ℝ) / δ) / n)
  let R := (Real.log (2 * (n : ℝ) / δ) / n) ^ (2 / 5 : ℝ)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hL := (confidence_log_bounds n δ hn hδ hδhalf).1
  have hLpos : 0 < Real.log (2 * (n : ℝ) / δ) := by linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hOnline : Real.sqrt (Real.log (2 * ((algTests n δ G).card : ℝ)) / n) ≤ A + 22 * R :=
    sqrt_online_complexity_le n δ G hn hδ hδhalf hlarge
  have hBias : 1 / (algM n δ : ℝ) ^ 2 ≤ R := inverse_algM_sq_le_rate n δ hn hδ hδhalf
  have hUnion : Real.sqrt (Real.log
      (2 * ((G.card : ℝ) + (candidates (algM n δ ^ 2) (4 * algM n δ + 2)).card) / δ) / n) ≤
      A + 22 * R :=
    sqrt_union_card_le_rate n G.card _ δ hn hδ hδhalf hlarge (log_alg_candidates_card_le n δ)
  have hEight := sqrt_eight_mul_le (Real.log
    (2 * ((G.card : ℝ) + (candidates (algM n δ ^ 2) (4 * algM n δ + 2)).card) / δ) / n)
  rw [← mul_div_assoc] at hEight
  have hEmp := mul_le_mul_of_nonneg_left (add_le_add hOnline hBias) hCemp.le
  change _ ≤ (24 * Cemp + 70) * (A + R)
  nlinarith [mul_nonneg hCemp.le hA, mul_nonneg hCemp.le hR]

lemma final_constant_ge_one (Cemp : ℝ) (hCemp : 0 < Cemp) :
    1 ≤ 24 * Cemp + 70 := by linarith

/-- The universal unit error bound suffices in the complementary sample-size regime. -/
lemma one_le_final_rate_of_small (Cemp : ℝ) (hCemp : 0 < Cemp)
    (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ)) (hn : 0 < n)
    (hsmall : (n : ℝ) ≤ Real.log (2 * (n : ℝ) / δ)) :
    1 ≤ (24 * Cemp + 70) *
      (Real.sqrt (Real.log (2 * (G.card : ℝ) / δ) / n) +
        (Real.log (2 * (n : ℝ) / δ) / n) ^ (2 / 5 : ℝ)) := by
  have hR := one_le_rate_of_small n δ hn hsmall
  have hA := Real.sqrt_nonneg (Real.log (2 * (G.card : ℝ) / δ) / n)
  have hC := final_constant_ge_one Cemp hCemp
  have hsum : 1 ≤ Real.sqrt (Real.log (2 * (G.card : ℝ) / δ) / n) +
      (Real.log (2 * (n : ℝ) / δ) / n) ^ (2 / 5 : ℝ) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 24 * Cemp + 70 by linarith)
  linarith

end CalibratedMA.Randomized.MainRates

end

-- Solutions.MainConcentration
section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CalibratedMA.Randomized.MainConcentration

lemma exp_le_chord (t y : ℝ) (hy : |y| ≤ 2) :
    Real.exp (t * y) ≤
      (Real.exp (-2*t) + Real.exp (2*t))/2 +
        y * ((Real.exp (2*t) - Real.exp (-2*t))/4) := by
  have hy' := abs_le.mp hy
  have h := convexOn_exp.2 (Set.mem_univ (-2*t)) (Set.mem_univ (2*t))
    (show 0 ≤ (2-y)/4 by linarith) (show 0 ≤ (2+y)/4 by linarith)
    (show (2-y)/4 + (2+y)/4 = 1 by ring)
  simp only [smul_eq_mul] at h
  have heq : t*y = (2-y)/4 * (-2*t) + (2+y)/4 * (2*t) := by ring
  rw [heq]
  exact h.trans_eq (by ring)

lemma condExp_exp_le {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → ℝ) (hY : @Measurable Ω ℝ mΩ _ Y) (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ 2)
    (hzero : μ[Y | m] =ᵐ[μ] 0) (t : ℝ) :
    μ[fun ω ↦ Real.exp (t * Y ω) | m] ≤ᵐ[μ] fun _ ↦ Real.exp (2*t^2) := by
  let : MeasurableSpace Ω := mΩ
  have hYi : Integrable Y μ := Integrable.of_mem_Icc (-2) 2 hY.aemeasurable <|
    hb.mono fun _ h ↦ abs_le.mp h
  have hEi : Integrable (fun ω ↦ Real.exp (t * Y ω)) μ :=
    integrable_exp_mul_of_mem_Icc hY.aemeasurable (hb.mono fun _ h ↦ abs_le.mp h)
  let a := (Real.exp (-2*t) + Real.exp (2*t))/2
  let b := (Real.exp (2*t) - Real.exp (-2*t))/4
  have hAi : Integrable (fun ω ↦ a + b * Y ω) μ :=
    (integrable_const a).add (hYi.const_mul b)
  have hle : (fun ω ↦ Real.exp (t * Y ω)) ≤ᵐ[μ] fun ω ↦ a + b * Y ω :=
    hb.mono fun ω h ↦ by simpa [a, b, mul_comm] using exp_le_chord t (Y ω) h
  have hce := condExp_mono hEi hAi (m := m) hle
  have ha := condExp_add (integrable_const a) (hYi.const_mul b) m
  have hmul := condExp_smul b Y m (μ := μ)
  have hcosh : a ≤ Real.exp (2*t^2) := by
    simpa [a, Real.cosh_eq, add_comm, show (2*t)^2/2 = 2*t^2 by ring]
      using Real.cosh_le_exp_half_sq (2*t)
  filter_upwards [hce, ha, hmul, hzero] with ω hce ha hmul hz
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ha hmul hz
  change μ[fun ω ↦ a + b * Y ω | m] ω =
    μ[fun _ ↦ a | m] ω + μ[fun ω ↦ b * Y ω | m] ω at ha
  change μ[fun ω ↦ b * Y ω | m] ω = b * μ[Y | m] ω at hmul
  rw [ha, condExp_const hm, hmul, hz, mul_zero, add_zero] at hce
  exact hce.trans hcosh

/-- A martingale MGF step that does not require the sample space to be standard Borel. -/
lemma subgaussian_add_of_condExp_zero {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (X Y : Ω → ℝ) (hXm : Measurable[m] X) (hY : @Measurable Ω ℝ mΩ _ Y)
    (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ 2) (hzero : μ[Y | m] =ᵐ[μ] 0)
    (c : ℝ≥0) (hX : HasSubgaussianMGF X c μ) :
    HasSubgaussianMGF (fun ω ↦ X ω + Y ω) (c + 4) μ := by
  let : MeasurableSpace Ω := mΩ
  have hEi (t : ℝ) : Integrable (fun ω ↦ Real.exp (t * Y ω)) μ :=
    integrable_exp_mul_of_mem_Icc hY.aemeasurable (hb.mono fun _ h ↦ abs_le.mp h)
  have hprod (t : ℝ) :
      Integrable (fun ω ↦ Real.exp (t * X ω) * Real.exp (t * Y ω)) μ := by
    refine (hX.integrable_exp_mul t).mul_bdd (c := Real.exp (|t| * 2)) (hEi t).aestronglyMeasurable ?_
    filter_upwards [hb] with ω h
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self (t * Y ω)).trans (by rw [abs_mul]; gcongr)
  refine ⟨fun t ↦ ?_, fun t ↦ ?_⟩
  · simpa only [mul_add, Real.exp_add] using hprod t
  · have hpull := condExp_mul_of_stronglyMeasurable_left
      (μ := μ) (m := m) ((measurable_const.mul hXm).exp.stronglyMeasurable)
      (hprod t) (hEi t)
    have hce := condExp_exp_le μ m hm Y hY hb hzero t
    have hle : μ[fun ω ↦ Real.exp (t * X ω) * Real.exp (t * Y ω) | m]
        ≤ᵐ[μ] fun ω ↦ Real.exp (t * X ω) * Real.exp (2*t^2) := by
      filter_upwards [hpull, hce] with ω hp hc
      change μ[fun ω ↦ Real.exp (t * X ω) * Real.exp (t * Y ω) | m] ω =
        Real.exp (t * X ω) * μ[fun ω ↦ Real.exp (t * Y ω) | m] ω at hp
      rw [hp]
      exact mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
    calc
      mgf (fun ω ↦ X ω + Y ω) μ t =
          ∫ ω, μ[fun ω ↦ Real.exp (t * X ω) * Real.exp (t * Y ω) | m] ω ∂μ := by
        rw [integral_condExp hm]
        simp only [mgf, mul_add, Real.exp_add]
      _ ≤ ∫ ω, Real.exp (t * X ω) * Real.exp (2*t^2) ∂μ :=
        integral_mono_ae integrable_condExp ((hX.integrable_exp_mul t).mul_const _) hle
      _ = mgf X μ t * Real.exp (2*t^2) := by rw [integral_mul_const]; rfl
      _ ≤ Real.exp ((c:ℝ)*t^2/2) * Real.exp (2*t^2) :=
        mul_le_mul_of_nonneg_right (hX.mgf_le t) (Real.exp_pos _).le
      _ = Real.exp ((↑(c+4):ℝ)*t^2/2) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

lemma subgaussian_sum_of_condExp_zero {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (m : ℕ → MeasurableSpace Ω) (n : ℕ)
    (hm : ∀ t < n, m t ≤ mΩ)
    (hY : ∀ t < n, Measurable (Y t))
    (hPast : ∀ t < n, Measurable[m t] (fun ω ↦ ∑ s ∈ Finset.range t, Y s ω))
    (hb : ∀ t < n, ∀ᵐ ω ∂μ, |Y t ω| ≤ 2)
    (hzero : ∀ t < n, μ[Y t | m t] =ᵐ[μ] 0) :
    HasSubgaussianMGF (fun ω ↦ ∑ t ∈ Finset.range n, Y t ω) (4*n) μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := ih (fun t ht ↦ hm t (by omega)) (fun t ht ↦ hY t (by omega))
      (fun t ht ↦ hPast t (by omega)) (fun t ht ↦ hb t (by omega))
      (fun t ht ↦ hzero t (by omega))
    have hs := subgaussian_add_of_condExp_zero μ (m n) (hm n (by omega))
      (fun ω ↦ ∑ s ∈ Finset.range n, Y s ω) (Y n) (hPast n (by omega))
      (hY n (by omega)) (hb n (by omega)) (hzero n (by omega)) (4*n) hi
    simpa only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one, mul_add, mul_one] using hs

end CalibratedMA.Randomized.MainConcentration

end

-- Solutions.MainConcentrationFin
section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CalibratedMA.Randomized.MainConcentration

lemma sum_range_extend_eq_fin_filter {n k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    (∑ t ∈ Finset.range k, if ht : t < n then f ⟨t, ht⟩ else 0) =
      ∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ t.val < k), f t := by
  classical
  apply Finset.sum_bij (fun t ht ↦ (⟨t, (Finset.mem_range.mp ht).trans_le hk⟩ : Fin n))
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.mem_range.mp ht
  · intro t ht s hs hts
    exact congrArg Fin.val hts
  · intro t ht
    refine ⟨t.val, Finset.mem_range.mpr (Finset.mem_filter.mp ht).2, ?_⟩
    rfl
  · intro t ht
    simp only [dif_pos ((Finset.mem_range.mp ht).trans_le hk)]

/-- Finite-index version of the conditional-mean-zero MGF bound. -/
lemma subgaussian_sum_fin_of_condExp_zero {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (Y : Fin n → Ω → ℝ)
    (m : Fin n → MeasurableSpace Ω)
    (hm : ∀ t, m t ≤ mΩ)
    (hY : ∀ t, Measurable (Y t))
    (hPast : ∀ t, Measurable[m t]
      (fun ω ↦ ∑ s ∈ Finset.univ.filter (fun s : Fin n ↦ s.val < t.val), Y s ω))
    (hb : ∀ t, ∀ᵐ ω ∂μ, |Y t ω| ≤ 2)
    (hzero : ∀ t, μ[Y t | m t] =ᵐ[μ] 0) :
    HasSubgaussianMGF (fun ω ↦ ∑ t : Fin n, Y t ω) (4*n) μ := by
  classical
  let Ye : ℕ → Ω → ℝ := fun t ω ↦ if ht : t < n then Y ⟨t, ht⟩ ω else 0
  let me : ℕ → MeasurableSpace Ω := fun t ↦ if ht : t < n then m ⟨t, ht⟩ else ⊥
  have hm' : ∀ t < n, me t ≤ mΩ := by
    intro t ht
    simpa only [me, dif_pos ht] using hm ⟨t, ht⟩
  have hY' : ∀ t < n, Measurable (Ye t) := by
    intro t ht
    simpa only [Ye, dif_pos ht] using hY ⟨t, ht⟩
  have hPast' : ∀ t < n, Measurable[me t] (fun ω ↦ ∑ s ∈ Finset.range t, Ye s ω) := by
    intro t ht
    have heq : (fun ω ↦ ∑ s ∈ Finset.range t, Ye s ω) =
        (fun ω ↦ ∑ s ∈ Finset.univ.filter (fun s : Fin n ↦ s.val < t), Y s ω) := by
      funext ω
      exact sum_range_extend_eq_fin_filter ht.le (fun s ↦ Y s ω)
    rw [heq]
    rw [show me t = m ⟨t, ht⟩ by exact dif_pos ht]
    exact hPast ⟨t, ht⟩
  have hb' : ∀ t < n, ∀ᵐ ω ∂μ, |Ye t ω| ≤ 2 := by
    intro t ht
    simpa only [Ye, dif_pos ht] using hb ⟨t, ht⟩
  have hz' : ∀ t < n, μ[Ye t | me t] =ᵐ[μ] 0 := by
    intro t ht
    simpa only [Ye, me, dif_pos ht] using hzero ⟨t, ht⟩
  have hs := subgaussian_sum_of_condExp_zero μ Ye me n hm' hY' hPast' hb' hz'
  have heq : (fun ω ↦ ∑ t ∈ Finset.range n, Ye t ω) = (fun ω ↦ ∑ t : Fin n, Y t ω) := by
    funext ω
    simpa using sum_range_extend_eq_fin_filter (le_refl n) (fun t ↦ Y t ω)
  rw [heq] at hs
  exact hs

end CalibratedMA.Randomized.MainConcentration

end

-- Solutions.MainConcentrationIID
section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CalibratedMA.Randomized.MainConcentration

lemma condExp_indep_pair {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → A) (V : Ω → B) (hU : Measurable U) (hV : Measurable V)
    (hind : IndepFun U V μ) (f : A × B → ℝ) (hf : Measurable f)
    (hb : ∀ z, |f z| ≤ 1) :
    μ[fun ω ↦ f (U ω, V ω) | MeasurableSpace.comap U inferInstance] =ᵐ[μ]
      fun ω ↦ ∫ b, f (U ω, b) ∂(μ.map V) := by
  have : IsProbabilityMeasure (μ.map U) := Measure.isProbabilityMeasure_map hU.aemeasurable
  have : IsProbabilityMeasure (μ.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  have hfm : Measurable (fun ω ↦ f (U ω, V ω)) := hf.comp (hU.prodMk hV)
  have hfi : Integrable (fun ω ↦ f (U ω, V ω)) μ :=
    Integrable.of_mem_Icc (-1) 1 hfm.aemeasurable
      (.of_forall fun ω ↦ abs_le.mp (hb (U ω, V ω)))
  have hgm : Measurable (fun a ↦ ∫ b, f (a,b) ∂(μ.map V)) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  have hgb (a : A) : |∫ b, f (a,b) ∂(μ.map V)| ≤ 1 := by
    simpa using norm_integral_le_of_norm_le_const
      (μ := μ.map V) (f := fun b ↦ f (a,b)) (C := 1) (.of_forall fun b ↦ by simpa only [Real.norm_eq_abs] using hb (a,b))
  have hgi : Integrable (fun ω ↦ ∫ b, f (U ω,b) ∂(μ.map V)) μ :=
    Integrable.of_mem_Icc (-1) 1 (hgm.comp hU).aemeasurable
      (.of_forall fun ω ↦ abs_le.mp (hgb (U ω)))
  have hfprod : Integrable f ((μ.map U).prod (μ.map V)) :=
    Integrable.of_mem_Icc (-1) 1 hf.aemeasurable (.of_forall fun z ↦ abs_le.mp (hb z))
  refine (ae_eq_condExp_of_forall_setIntegral_eq hU.comap_le hfi
    (fun s _ _ ↦ hgi.integrableOn) ?_
    ((hgm.comp (comap_measurable U)).stronglyMeasurable.aestronglyMeasurable)).symm
  rintro s ⟨t, ht, rfl⟩ _
  calc
    (∫ ω in U ⁻¹' t, (∫ b, f (U ω,b) ∂(μ.map V)) ∂μ) =
        ∫ a in t, (∫ b, f (a,b) ∂(μ.map V)) ∂(μ.map U) := by
      symm
      exact setIntegral_map ht hgm.aestronglyMeasurable hU.aemeasurable
    _ = ∫ z in t ×ˢ Set.univ, f z ∂((μ.map U).prod (μ.map V)) := by
      rw [setIntegral_prod f hfprod.integrableOn]
      simp
    _ = ∫ ω in (fun ω ↦ (U ω,V ω)) ⁻¹' (t ×ˢ Set.univ), f (U ω,V ω) ∂μ := by
      rw [← hind.map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable]
      exact setIntegral_map (ht.prod MeasurableSet.univ) hf.aestronglyMeasurable
        (hU.prodMk hV).aemeasurable
    _ = ∫ ω in U ⁻¹' t, f (U ω,V ω) ∂μ := by
      have hs : (fun ω ↦ (U ω,V ω)) ⁻¹' (t ×ˢ Set.univ) = U ⁻¹' t := by
        ext ω
        simp
      rw [hs]

lemma condExp_centered_indep_pair {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → A) (V : Ω → B) (hU : Measurable U) (hV : Measurable V)
    (hind : IndepFun U V μ) (f : A × B → ℝ) (hf : Measurable f)
    (hb : ∀ z, |f z| ≤ 1) :
    μ[fun ω ↦ (∫ b, f (U ω,b) ∂(μ.map V)) - f (U ω,V ω) |
      MeasurableSpace.comap U inferInstance] =ᵐ[μ] 0 := by
  have : IsProbabilityMeasure (μ.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  have hgm : Measurable (fun a ↦ ∫ b, f (a,b) ∂(μ.map V)) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  have hgb (a : A) : |∫ b, f (a,b) ∂(μ.map V)| ≤ 1 := by
    simpa using norm_integral_le_of_norm_le_const
      (μ := μ.map V) (f := fun b ↦ f (a,b)) (C := 1)
      (.of_forall fun b ↦ by simpa only [Real.norm_eq_abs] using hb (a,b))
  have hgi : Integrable (fun ω ↦ ∫ b, f (U ω,b) ∂(μ.map V)) μ :=
    Integrable.of_mem_Icc (-1) 1 (hgm.comp hU).aemeasurable
      (.of_forall fun ω ↦ abs_le.mp (hgb (U ω)))
  have hfi : Integrable (fun ω ↦ f (U ω,V ω)) μ :=
    Integrable.of_mem_Icc (-1) 1 (hf.comp (hU.prodMk hV)).aemeasurable
      (.of_forall fun ω ↦ abs_le.mp (hb (U ω,V ω)))
  have hsub := condExp_sub hgi hfi (MeasurableSpace.comap U inferInstance)
  have hce := condExp_indep_pair μ U V hU hV hind f hf hb
  have hmean := condExp_of_stronglyMeasurable hU.comap_le
    ((hgm.comp (comap_measurable U)).stronglyMeasurable) hgi
  filter_upwards [hsub, hce] with ω hs hc
  change μ[fun ω ↦ (∫ b, f (U ω,b) ∂μ.map V) - f (U ω,V ω) |
    MeasurableSpace.comap U inferInstance] ω =
    μ[fun ω ↦ ∫ b, f (U ω,b) ∂μ.map V | MeasurableSpace.comap U inferInstance] ω -
    μ[fun ω ↦ f (U ω,V ω) | MeasurableSpace.comap U inferInstance] ω at hs
  have hmeanω := congrFun hmean ω
  change μ[fun ω ↦ ∫ b, f (U ω,b) ∂μ.map V | MeasurableSpace.comap U inferInstance] ω =
    ∫ b, f (U ω,b) ∂μ.map V at hmeanω
  rw [hs, hmeanω, hc]
  simp

end CalibratedMA.Randomized.MainConcentration

end

-- Solutions.MainConcentrationPast
section

open MeasureTheory ProbabilityTheory

namespace CalibratedMA.Randomized.MainConcentration

/-- Keep coordinates strictly before `t`, filling the remaining coordinates by `a0`. -/
def pastFill {A : Type*} {n : ℕ} (a0 : A) (t : ℕ) (ω : Fin n → A) (i : Fin n) : A :=
  if i.val < t then ω i else a0

@[simp] lemma pastFill_apply_lt {A : Type*} {n : ℕ} (a0 : A) (t : ℕ)
    (ω : Fin n → A) (i : Fin n) (hi : i.val < t) : pastFill a0 t ω i = ω i :=
  if_pos hi

@[simp] lemma pastFill_apply_ge {A : Type*} {n : ℕ} (a0 : A) (t : ℕ)
    (ω : Fin n → A) (i : Fin n) (hi : t ≤ i.val) : pastFill a0 t ω i = a0 :=
  if_neg (not_lt.mpr hi)

lemma measurable_pastFill {A : Type*} [MeasurableSpace A] {n : ℕ} (a0 : A) (t : ℕ) :
    Measurable (pastFill (n := n) a0 t) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i.val < t
  · simpa only [pastFill, if_pos hi] using (measurable_pi_apply i)
  · simpa only [pastFill, if_neg hi] using (measurable_const : Measurable fun _ : Fin n → A ↦ a0)

lemma pastFill_pastFill {A : Type*} {n : ℕ} (a0 : A) (s t : ℕ) (hst : s ≤ t)
    (ω : Fin n → A) : pastFill a0 s (pastFill a0 t ω) = pastFill a0 s ω := by
  funext i
  by_cases hi : i.val < s
  · simp only [pastFill, if_pos hi, if_pos (lt_of_lt_of_le hi hst)]
  · simp only [pastFill, if_neg hi]

lemma pastSigma_le {A : Type*} [MeasurableSpace A] {n : ℕ} (a0 : A) (t : ℕ) :
    MeasurableSpace.comap (pastFill (n := n) a0 t) inferInstance ≤ (inferInstance : MeasurableSpace (Fin n → A)) :=
  (measurable_pastFill a0 t).comap_le

lemma measurable_pastFill_comap {A : Type*} [MeasurableSpace A] {n : ℕ}
    (a0 : A) (s t : ℕ) (hst : s ≤ t) :
    Measurable[MeasurableSpace.comap (pastFill (n := n) a0 t) inferInstance]
      (pastFill a0 s) := by
  have h := (measurable_pastFill (n := n) a0 s).comp (comap_measurable (pastFill a0 t))
  simpa only [Function.comp_def, pastFill_pastFill a0 s t hst] using h

lemma measurable_eval_past {A : Type*} [MeasurableSpace A] {n : ℕ}
    (a0 : A) (t : ℕ) (i : Fin n) (hi : i.val < t) :
    Measurable[MeasurableSpace.comap (pastFill (n := n) a0 t) inferInstance]
      (fun ω : Fin n → A ↦ ω i) := by
  have h := (measurable_pi_apply i).comp (comap_measurable (pastFill a0 t))
  simpa only [Function.comp_def, pastFill_apply_lt a0 t _ i hi] using h

lemma indepFun_pastFill_eval {A : Type*} [MeasurableSpace A] {n : ℕ}
    (D : Measure A) [IsProbabilityMeasure D] (a0 : A) (t : Fin n) :
    IndepFun (pastFill a0 t.val) (fun ω : Fin n → A ↦ ω t)
      (Measure.pi fun _ : Fin n ↦ D) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun i ↦ i.val < t.val
  let rebuild : (S → A) → (Fin n → A) := fun p i ↦ if h : i ∈ S then p ⟨i,h⟩ else a0
  have hrec : Measurable rebuild := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i ∈ S
    · simpa only [rebuild, dif_pos hi] using (measurable_pi_apply (⟨i,hi⟩ : S))
    · simpa only [rebuild, dif_neg hi] using (measurable_const : Measurable fun _ : S → A ↦ a0)
  have hind : iIndepFun (fun i (ω : Fin n → A) ↦ ω i) (Measure.pi fun _ : Fin n ↦ D) :=
    iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
  have hdisj : Disjoint S {t} := by simp [S, Finset.disjoint_singleton_right]
  have hcomp := (hind.indepFun_finset S {t} hdisj (fun i ↦ measurable_pi_apply i)).comp hrec
    (measurable_pi_apply (⟨t,Finset.mem_singleton_self t⟩ : ({t} : Finset (Fin n))))
  change IndepFun (fun ω i ↦ if i.val < t.val then ω i else a0)
    (fun ω : Fin n → A ↦ ω t) (Measure.pi fun _ : Fin n ↦ D)
  simpa [rebuild, S, Function.comp_def] using hcomp

end CalibratedMA.Randomized.MainConcentration

end

-- Solutions.MainConcentrationTail
section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CalibratedMA.Randomized.MainConcentrationTail

lemma measure_abs_gt_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {V : Ω → ℝ} {c : ℝ≥0}
    (hV : HasSubgaussianMGF V c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε < |V ω|} ≤ 2 * Real.exp (-ε^2 / (2*(c:ℝ))) := by
  have hsub : {ω | ε < |V ω|} ⊆ {ω | ε ≤ V ω} ∪ {ω | ε ≤ -V ω} := by
    intro ω hω
    have hω' : ε ≤ |V ω| := le_of_lt hω
    by_cases h : 0 ≤ V ω
    · exact Or.inl (by change ε ≤ V ω; simpa only [abs_of_nonneg h] using hω')
    · exact Or.inr (by change ε ≤ -V ω; simpa only [abs_of_neg (lt_of_not_ge h)] using hω')
  calc
    _ ≤ μ.real ({ω | ε ≤ V ω} ∪ {ω | ε ≤ -V ω}) := measureReal_mono hsub
    _ ≤ μ.real {ω | ε ≤ V ω} + μ.real {ω | ε ≤ -V ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-ε^2 / (2*(c:ℝ))) + Real.exp (-ε^2 / (2*(c:ℝ))) :=
      add_le_add (hV.measure_ge_le hε) (hV.neg.measure_ge_le hε)
    _ = _ := by ring

lemma measure_exists_abs_gt_le {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Finset I) (V : I → Ω → ℝ)
    (c : ℝ≥0) (hV : ∀ i ∈ F, HasSubgaussianMGF (V i) c μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ∃ i ∈ F, ε < |V i ω|} ≤
      2 * (F.card:ℝ) * Real.exp (-ε^2 / (2*(c:ℝ))) := by
  have heq : {ω | ∃ i ∈ F, ε < |V i ω|} = ⋃ i ∈ F, {ω | ε < |V i ω|} := by
    ext ω; simp
  rw [heq]
  calc
    _ ≤ ∑ i ∈ F, μ.real {ω | ε < |V i ω|} := measureReal_biUnion_finset_le F _
    _ ≤ ∑ _i ∈ F, 2 * Real.exp (-ε^2 / (2*(c:ℝ))) :=
      Finset.sum_le_sum fun i hi ↦ measure_abs_gt_le μ (hV i hi) hε
    _ = _ := by simp; ring

/-- Uniform two-sided concentration for a finite family with variance proxy `4*n`. -/
lemma finite_subgaussian_deviation {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Finset I) (V : I → Ω → ℝ)
    (hF : F.Nonempty) (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hV : ∀ i ∈ F, HasSubgaussianMGF (V i) (4*(n:ℝ≥0)) μ) :
    μ {ω | ∃ i ∈ F,
      Real.sqrt (8*Real.log (2*(F.card:ℝ)/δ)/(n:ℝ)) < |V i ω|/(n:ℝ)} ≤
      ENNReal.ofReal δ := by
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hcard : 0 < (F.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hF)
  have hcard1 : 1 ≤ (F.card:ℝ) := by exact_mod_cast (Finset.card_pos.mpr hF)
  have hratio : 1 < 2*(F.card:ℝ)/δ := (lt_div_iff₀ hδ).mpr (by linarith)
  have hlog : 0 < Real.log (2*(F.card:ℝ)/δ) := Real.log_pos hratio
  let r := Real.sqrt (8*Real.log (2*(F.card:ℝ)/δ)/(n:ℝ))
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r^2 = 8*Real.log (2*(F.card:ℝ)/δ)/(n:ℝ) := Real.sq_sqrt (by positivity)
  have hexponent : -((n:ℝ)*r)^2/(2*(↑(4*(n:ℝ≥0)):ℝ)) =
      -Real.log (2*(F.card:ℝ)/δ) := by
    push_cast
    rw [mul_pow, hrsq]
    field_simp
    ring
  have hexp : 2*(F.card:ℝ)*Real.exp (-((n:ℝ)*r)^2/(2*(↑(4*(n:ℝ≥0)):ℝ))) = δ := by
    rw [hexponent, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have hbound := measure_exists_abs_gt_le μ F V (4*(n:ℝ≥0)) hV
    (show 0 ≤ (n:ℝ)*r by positivity)
  rw [hexp] at hbound
  have hsub : {ω | ∃ i ∈ F, r < |V i ω|/(n:ℝ)} ⊆
      {ω | ∃ i ∈ F, (n:ℝ)*r < |V i ω|} := by
    rintro ω ⟨i, hi, h⟩
    exact ⟨i, hi, by simpa only [mul_comm] using (lt_div_iff₀ hnR).mp h⟩
  calc
    _ ≤ μ {ω | ∃ i ∈ F, (n:ℝ)*r < |V i ω|} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | ∃ i ∈ F, (n:ℝ)*r < |V i ω|}) :=
      (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hbound

end CalibratedMA.Randomized.MainConcentrationTail

end

-- Solutions.MainConcentrationOnline
section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CalibratedMA.Randomized.MainConcentration

noncomputable def onlineIncrement {A : Type*} [MeasurableSpace A] {n : ℕ}
    (D : Measure A) (f : Fin n → (Fin n → A) → A → ℝ) (t : Fin n)
    (ω : Fin n → A) : ℝ := (∫ a, f t ω a ∂D) - f t ω (ω t)

lemma measurable_onlineIncrement {A : Type*} [MeasurableSpace A] {n : ℕ}
    (D : Measure A) [IsProbabilityMeasure D]
    (f : Fin n → (Fin n → A) → A → ℝ)
    (hf : ∀ t, Measurable (Function.uncurry (f t))) (t : Fin n) :
    Measurable (onlineIncrement D f t) := by
  exact (hf t).stronglyMeasurable.integral_prod_right.measurable.sub
    ((hf t).comp (measurable_id.prodMk (measurable_pi_apply t)))

lemma onlineIncrement_abs_le {A : Type*} [MeasurableSpace A] {n : ℕ}
    (D : Measure A) [IsProbabilityMeasure D]
    (f : Fin n → (Fin n → A) → A → ℝ)
    (hb : ∀ t ω a, |f t ω a| ≤ 1) (t : Fin n) (ω : Fin n → A) :
    |onlineIncrement D f t ω| ≤ 2 := by
  have hmean : |∫ a, f t ω a ∂D| ≤ 1 := by
    simpa using norm_integral_le_of_norm_le_const (μ := D)
      (f := f t ω) (C := 1) (.of_forall fun a ↦ by
        simpa only [Real.norm_eq_abs] using hb t ω a)
  exact (abs_sub _ _).trans (by linarith [hb t ω (ω t)])

lemma onlineIncrement_pastFill {A : Type*} [MeasurableSpace A] {n : ℕ}
    (D : Measure A) (f : Fin n → (Fin n → A) → A → ℝ)
    (hpast : ∀ t ω ω', (∀ i : Fin n, i.val < t.val → ω i = ω' i) →
      ∀ a, f t ω a = f t ω' a)
    (a0 : A) (s t : Fin n) (hst : s.val < t.val) (ω : Fin n → A) :
    onlineIncrement D f s (pastFill a0 t.val ω) = onlineIncrement D f s ω := by
  have hfp (a : A) : f s (pastFill a0 t.val ω) a = f s ω a := by
    apply hpast
    intro i hi
    exact pastFill_apply_lt a0 t.val ω i (lt_trans hi hst)
  simp only [onlineIncrement, hfp, pastFill_apply_lt a0 t.val ω s hst]

lemma onlineIncrement_condExp_zero {A : Type*} [MeasurableSpace A] {n : ℕ}
    (D : Measure A) [IsProbabilityMeasure D]
    (f : Fin n → (Fin n → A) → A → ℝ)
    (hf : ∀ t, Measurable (Function.uncurry (f t)))
    (hb : ∀ t ω a, |f t ω a| ≤ 1)
    (hpast : ∀ t ω ω', (∀ i : Fin n, i.val < t.val → ω i = ω' i) →
      ∀ a, f t ω a = f t ω' a)
    (a0 : A) (t : Fin n) :
    (Measure.pi fun _ : Fin n ↦ D)[onlineIncrement D f t |
      MeasurableSpace.comap (pastFill a0 t.val) inferInstance] =ᵐ[
        Measure.pi fun _ : Fin n ↦ D] 0 := by
  have hfp (ω : Fin n → A) (a : A) : f t (pastFill a0 t.val ω) a = f t ω a := by
    apply hpast
    intro i hi
    exact pastFill_apply_lt a0 t.val ω i hi
  have h := condExp_centered_indep_pair (Measure.pi fun _ : Fin n ↦ D)
    (pastFill a0 t.val) (fun ω : Fin n → A ↦ ω t)
    (measurable_pastFill a0 t.val) (measurable_pi_apply t)
    (indepFun_pastFill_eval D a0 t) (Function.uncurry (f t)) (hf t)
    (fun z ↦ hb t z.1 z.2)
  rw [(measurePreserving_eval (fun _ : Fin n ↦ D) t).map_eq] at h
  change (Measure.pi fun _ : Fin n ↦ D)[fun ω ↦
    (∫ a, f t ω a ∂D) - f t ω (ω t) |
      MeasurableSpace.comap (pastFill a0 t.val) inferInstance] =ᵐ[_] 0
  simpa only [Function.uncurry_apply_pair, hfp] using h

lemma online_sum_subgaussian {A : Type*} [MeasurableSpace A] {n : ℕ}
    (D : Measure A) [IsProbabilityMeasure D]
    (f : Fin n → (Fin n → A) → A → ℝ)
    (hf : ∀ t, Measurable (Function.uncurry (f t)))
    (hb : ∀ t ω a, |f t ω a| ≤ 1)
    (hpast : ∀ t ω ω', (∀ i : Fin n, i.val < t.val → ω i = ω' i) →
      ∀ a, f t ω a = f t ω' a) :
    HasSubgaussianMGF (fun ω ↦ ∑ t : Fin n, onlineIncrement D f t ω) (4*n)
      (Measure.pi fun _ : Fin n ↦ D) := by
  classical
  obtain ⟨a0⟩ := nonempty_of_isProbabilityMeasure D
  refine subgaussian_sum_fin_of_condExp_zero (Measure.pi fun _ : Fin n ↦ D)
    (onlineIncrement D f) (fun t ↦ MeasurableSpace.comap (pastFill a0 t.val) inferInstance)
    (fun t ↦ pastSigma_le a0 t.val) (measurable_onlineIncrement D f hf) ?_
    (fun t ↦ .of_forall (onlineIncrement_abs_le D f hb t))
    (onlineIncrement_condExp_zero D f hf hb hpast a0)
  intro t
  refine Finset.measurable_fun_sum _ fun s hs ↦ ?_
  have hst : s.val < t.val := (Finset.mem_filter.mp hs).2
  have hm := (measurable_onlineIncrement D f hf s).comp
    (comap_measurable (pastFill a0 t.val))
  simpa only [Function.comp_def, onlineIncrement_pastFill D f hpast a0 s t hst] using hm

/-- A finite-class online-to-batch bound for arbitrary measurable iid examples. -/
lemma finite_online_to_batch {A I : Type*} [MeasurableSpace A] {n : ℕ}
    (D : Measure A) [IsProbabilityMeasure D] (F : Finset I)
    (f : I → Fin n → (Fin n → A) → A → ℝ)
    (hF : F.Nonempty) (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hf : ∀ i ∈ F, ∀ t, Measurable (Function.uncurry (f i t)))
    (hb : ∀ i ∈ F, ∀ t ω a, |f i t ω a| ≤ 1)
    (hpast : ∀ i ∈ F, ∀ t ω ω',
      (∀ s : Fin n, s.val < t.val → ω s = ω' s) →
        ∀ a, f i t ω a = f i t ω' a) :
    (Measure.pi fun _ : Fin n ↦ D) {ω | ∃ i ∈ F,
      Real.sqrt (8*Real.log (2*(F.card:ℝ)/δ)/(n:ℝ)) <
        |(∑ t : Fin n, ∫ a, f i t ω a ∂D)/(n:ℝ) -
          (∑ t : Fin n, f i t ω (ω t))/(n:ℝ)|} ≤ ENNReal.ofReal δ := by
  have h := MainConcentrationTail.finite_subgaussian_deviation
    (Measure.pi fun _ : Fin n ↦ D) F
    (fun i ω ↦ ∑ t : Fin n, onlineIncrement D (f i) t ω)
    hF n hn δ hδ hδ1
    (fun i hi ↦ online_sum_subgaussian D (f i) (hf i hi) (hb i hi) (hpast i hi))
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  simpa only [onlineIncrement, Finset.sum_sub_distrib, ← sub_div,
    abs_div, abs_of_pos hnR] using h

end CalibratedMA.Randomized.MainConcentration

end

-- Solutions.MainEvents
section

open MeasureTheory

namespace CalibratedMA.Randomized.MainEvents

variable {X : Type*} [MeasurableSpace X]

noncomputable def deviationRadius (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ)) : ℝ :=
  Real.sqrt (8 * Real.log (2 * ((MainProcess.family n δ G).card : ℝ) / δ) / (n : ℝ))

def UniformDeviation (D : Measure (X × ℝ)) (n : ℕ) (δ : ℝ)
    (G : Finset (X → ℝ)) (ω : Fin n → X × ℝ) : Prop :=
  ∀ i ∈ MainProcess.family n δ G,
    |(∑ t : Fin n, ∫ z, MainProcess.process n δ G i t ω z ∂D) / (n : ℝ) -
      (∑ t : Fin n, MainProcess.process n δ G i t ω (ω t)) / (n : ℝ)| ≤
        deviationRadius n δ G

omit [MeasurableSpace X] in
lemma family_card (n : ℕ) (δ : ℝ) (G : Finset (X → ℝ)) :
    (MainProcess.family n δ G).card = G.card +
      (MainCandidates.candidates (algM n δ ^ 2) (4 * algM n δ + 2)).card :=
  Finset.card_disjSum G _

lemma measure_not_uniformDeviation_le (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (G : Finset (X → ℝ))
    (hG : ∀ g ∈ G, Measurable g ∧ ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1)
    (n : ℕ) (hn : 2 ≤ n) (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ < 1/2) :
    (Measure.pi fun _ : Fin n ↦ D) {ω | ¬ UniformDeviation D n δ G ω} ≤
      ENNReal.ofReal δ := by
  have h := MainConcentration.finite_online_to_batch D (MainProcess.family n δ G)
    (MainProcess.process n δ G) (MainProcess.family_nonempty n δ G) (by omega)
    δ hδ (by linarith)
    (fun i hi t ↦ MainProcess.measurable_process n δ G (fun g hg ↦ (hG g hg).1) i hi t)
    (fun i hi t ω z ↦ MainProcess.process_abs_le_one n δ G
      (fun g hg ↦ (hG g hg).2) i hi t ω z)
    (fun i _hi t ω ω' hh z ↦ MainProcess.process_history n δ G i t ω ω' hh z)
  simpa only [UniformDeviation, deviationRadius, not_forall, not_le, exists_prop] using h

lemma training_labels_ae (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, z.2 ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Fin n ↦ D), ∀ t : Fin n,
      (ω t).2 ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro t
  exact (measurePreserving_eval (fun _ : Fin n ↦ D) t).quasiMeasurePreserving.ae hD

lemma measure_not_labels_and_uniformDeviation_le
    (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, z.2 ∈ Set.Icc (0 : ℝ) 1)
    (G : Finset (X → ℝ))
    (hG : ∀ g ∈ G, Measurable g ∧ ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1)
    (n : ℕ) (hn : 2 ≤ n) (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ < 1/2) :
    (Measure.pi fun _ : Fin n ↦ D)
      {ω | ¬ ((∀ t : Fin n, (ω t).2 ∈ Set.Icc (0 : ℝ) 1) ∧
        UniformDeviation D n δ G ω)} ≤ ENNReal.ofReal δ := by
  have hnull := ae_iff.mp (training_labels_ae D hD n)
  have heq : {ω | ¬ ((∀ t : Fin n, (ω t).2 ∈ Set.Icc (0 : ℝ) 1) ∧
      UniformDeviation D n δ G ω)} =
      {ω | ¬ (∀ t : Fin n, (ω t).2 ∈ Set.Icc (0 : ℝ) 1)} ∪
        {ω | ¬ UniformDeviation D n δ G ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, not_and_or]
  rw [heq]
  calc
    _ ≤ (Measure.pi fun _ : Fin n ↦ D)
        {ω | ¬ (∀ t : Fin n, (ω t).2 ∈ Set.Icc (0 : ℝ) 1)} +
        (Measure.pi fun _ : Fin n ↦ D) {ω | ¬ UniformDeviation D n δ G ω} :=
      measure_union_le _ _
    _ = (Measure.pi fun _ : Fin n ↦ D) {ω | ¬ UniformDeviation D n δ G ω} := by
      rw [hnull, zero_add]
    _ ≤ ENNReal.ofReal δ := measure_not_uniformDeviation_le D G hG n hn δ hδ hδhalf

end CalibratedMA.Randomized.MainEvents

end

-- Solutions.MainAssembly
section

open MeasureTheory

universe u

open CalibratedMA.Randomized

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type u) [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D],
        (∀ᵐ z ∂D, z.2 ∈ Set.Icc (0 : ℝ) 1) →
        ∀ G : Finset (X → ℝ), (∀ g ∈ G, Measurable g ∧ ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) →
        ∀ n : ℕ, 2 ≤ n → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
          (Measure.pi fun _ : Fin n => D)
              {ω | ¬ (IsRandomizedPredictor (algorithm1 n δ G ω) ∧
                  CMA D (algorithm1 n δ G ω) G ≤
                    C * (Real.sqrt (Real.log (2 * (G.card : ℝ) / δ) / n) +
                      (Real.log (2 * (n : ℝ) / δ) / n) ^ (2 / 5 : ℝ)))} ≤
            ENNReal.ofReal δ := by
  obtain ⟨Cemp, hCemp, hemp⟩ := MainSampleBounds.exists_empirical_bound.{u}
  refine ⟨24 * Cemp + 70, by positivity, ?_⟩
  intro X _ D _ hD G hG n hn δ hδ hδhalf
  have hbad := MainEvents.measure_not_labels_and_uniformDeviation_le D hD G hG n hn δ hδ hδhalf
  apply le_trans (measure_mono ?_) hbad
  intro ω hfail
  by_contra hgood
  simp only [Set.mem_ofPred_eq, not_not] at hgood
  obtain ⟨hω, hdev⟩ := hgood
  obtain ⟨hΓ, hcount, hcal, hgroup⟩ := hemp X n δ G hn (fun g hg => (hG g hg).2) ω hω
  let B := Cemp * (Real.sqrt (Real.log (2 * ((algTests n δ G).card : ℝ)) / n) +
    1 / (algM n δ : ℝ) ^ 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hε : 0 ≤ MainEvents.deviationRadius n δ G := Real.sqrt_nonneg _
  have htransfer := MainTransfer.algorithm_cma_le D hD n δ G hn
    (fun g hg => (hG g hg).1) (fun g hg => (hG g hg).2) ω hω hΓ hcount
    B (MainEvents.deviationRadius n δ G) hB hε hcal hgroup hdev
  apply hfail
  refine ⟨htransfer.1, ?_⟩
  by_cases hlarge : Real.log (2 * (n : ℝ) / δ) ≤ n
  · apply htransfer.2.trans
    have hrate := MainRates.empirical_add_concentration_le Cemp hCemp n δ G hn hδ hδhalf hlarge
    simpa only [B, MainEvents.deviationRadius, MainEvents.family_card, Nat.cast_add] using hrate
  · exact (MainPopulation.CMA_le_one D hD _ htransfer.1 G hG).trans
      (MainRates.one_le_final_rate_of_small Cemp hCemp n δ G (by omega) (le_of_not_ge hlarge))

end
