-- Prove2me | solution 1 for EntropyLocalCoord.Leader.infoMeasure_prob_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:56:34.99281+00:00
-- url     : https://prove2.me/submissions/0e7cf593-23d6-478e-8794-512c801f0f85

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Model
import Definitions.Def_EntropyLocalCoord_Leader_Information
import Theorems.Thm_EntropyLocalCoord_Leader_infoCDF_mono

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace EntropyLocalCoord.Dev.Support

open EntropyLocalCoord.Leader

/-- If `C` is independent of `D ≥ F` and `Y` is `D`-measurable, then `E[Y | F ⊔ C] = E[Y | F]`. -/
theorem condExp_sup_indep {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] {F C D : MeasurableSpace Ω} (hF : F ≤ m0) (hC : C ≤ m0)
    (hD : D ≤ m0) (hFD : F ≤ D) (hind : Indep C D P) (Y : Ω → ℝ)
    (hY : StronglyMeasurable[D] Y) (hYi : Integrable Y P) :
    P[Y | F ⊔ C] =ᵐ[P] P[Y | F] := by
  have hFC : F ⊔ C ≤ m0 := sup_le hF hC
  -- key: for D-measurable integrable h and C-measurable t, ∫_t h = P t * ∫ h
  have key : ∀ (h : Ω → ℝ), StronglyMeasurable[D] h → Integrable h P →
      ∀ t, MeasurableSet[C] t → ∫ ω in t, h ω ∂P = P.real t * ∫ ω, h ω ∂P := by
    intro h hh hhi t ht
    have e := condExp_indep_eq hD hC hh hind.symm
    rw [← setIntegral_condExp hC hhi ht, setIntegral_congr_ae (hC t ht) (g := fun _ => ∫ ω, h ω ∂P)
      (by filter_upwards [e] with ω hω _ using hω)]
    simp [Measure.real, setIntegral_const, mul_comm]
  have hg : StronglyMeasurable[F] (P[Y | F]) := stronglyMeasurable_condExp
  have hgi : Integrable (P[Y | F]) P := integrable_condExp
  have hgm : AEStronglyMeasurable[F ⊔ C] (P[Y | F]) P :=
    ⟨P[Y | F], hg.mono le_sup_left, Filter.EventuallyEq.rfl⟩
  have hFm : ∀ s, MeasurableSet[F] s → MeasurableSet[D] s := fun s hs => hFD s hs
  -- the π-system of rectangles
  let Pi : Set (Set Ω) := {S | ∃ s t, MeasurableSet[F] s ∧ MeasurableSet[C] t ∧ S = s ∩ t}
  have hPi : IsPiSystem Pi := by
    rintro _ ⟨s, t, hs, ht, rfl⟩ _ ⟨s', t', hs', ht', rfl⟩ _
    exact ⟨s ∩ s', t ∩ t', hs.inter hs', ht.inter ht', by ext; simp; tauto⟩
  have hgen : F ⊔ C = MeasurableSpace.generateFrom Pi := by
    refine le_antisymm (sup_le ?_ ?_) ?_
    · intro s hs
      exact MeasurableSpace.measurableSet_generateFrom ⟨s, Set.univ, hs, MeasurableSet.univ, by simp⟩
    · intro t ht
      exact MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, t, MeasurableSet.univ, ht, by simp⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨s, t, hs, ht, rfl⟩
      exact (le_sup_left (a := F) (b := C) s hs).inter (le_sup_right (a := F) (b := C) t ht)
  have hset : ∀ S, MeasurableSet[F ⊔ C] S → ∫ ω in S, P[Y | F] ω ∂P = ∫ ω in S, Y ω ∂P := by
    intro S hS
    refine MeasurableSpace.induction_on_inter (m := F ⊔ C)
      (C := fun S _ => ∫ ω in S, P[Y | F] ω ∂P = ∫ ω in S, Y ω ∂P) hgen hPi ?_ ?_ ?_ ?_ S hS
    · simp
    · rintro _ ⟨s, t, hs, ht, rfl⟩
      have hts : MeasurableSet[m0] s := hF s hs
      have htt : MeasurableSet[m0] t := hC t ht
      have rect : ∀ h : Ω → ℝ, StronglyMeasurable[D] h → Integrable h P →
          ∫ ω in s ∩ t, h ω ∂P = P.real t * ∫ ω in s, h ω ∂P := by
        intro h hh hhi
        have e1 : ∫ ω in s ∩ t, h ω ∂P = ∫ ω in t, s.indicator h ω ∂P := by
          rw [integral_indicator hts, Measure.restrict_restrict hts, Set.inter_comm]
        rw [e1, key _ ((hh.indicator (hFm s hs))) (hhi.indicator hts) t ht,
          integral_indicator hts]
      rw [rect _ (hg.mono hFD) hgi, rect _ hY hYi, setIntegral_condExp hF hYi hs]
    · intro S hS ih
      have hS' : MeasurableSet[m0] S := hFC S hS
      have a1 := integral_add_compl hS' hgi
      have a2 := integral_add_compl hS' hYi
      have a3 : ∫ ω, P[Y | F] ω ∂P = ∫ ω, Y ω ∂P := integral_condExp hF
      linarith
    · intro f hd hf ih
      have hf' : ∀ i, MeasurableSet[m0] (f i) := fun i => hFC _ (hf i)
      rw [integral_iUnion hf' hd hgi.integrableOn, integral_iUnion hf' hd hYi.integrableOn]
      exact tsum_congr ih
  exact (ae_eq_condExp_of_forall_setIntegral_eq hFC hYi (fun s _ _ => hgi.integrableOn)
    (fun s hs _ => hset s hs) hgm).symm

section General

variable {Ω β : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace β] [MeasurableSingletonClass β]
  (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → β)

lemma condProb_nonneg_le {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (hX : Measurable[mΩ] X) (b : β) :
    ∀ᵐ ω ∂P, 0 ≤ condProb m P X b ω ∧ condProb m P X b ω ≤ 1 := by
  have hint : Integrable ((X ⁻¹' {b}).indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator (hX (measurableSet_singleton b))
  have h0 : 0 ≤ᵐ[P] P[(X ⁻¹' {b}).indicator (fun _ => (1 : ℝ)) | m] :=
    condExp_nonneg (Filter.Eventually.of_forall (fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω))
  have h1 : P[(X ⁻¹' {b}).indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[P] P[(fun _ => (1 : ℝ)) | m] :=
    condExp_mono hint (integrable_const _)
      (Filter.Eventually.of_forall (fun ω => Set.indicator_le_self' (fun _ _ => zero_le_one) ω))
  rw [condExp_const hm] at h1
  filter_upwards [h0, h1] with ω a b
  exact ⟨a, b⟩

lemma condProb_of_not_mem_range (m : MeasurableSpace Ω) (b : β) (hb : b ∉ Set.range X) :
    condProb m P X b = 0 := by
  have : X ⁻¹' {b} = ∅ := by
    ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    exact fun h => hb ⟨ω, h⟩
  unfold condProb
  rw [this, Set.indicator_empty]
  exact condExp_zero

lemma integrable_negMulLog_condProb {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (hX : Measurable[mΩ] X)
    (b : β) : Integrable (fun ω => Real.negMulLog (condProb m P X b ω)) P := by
  have hsm : AEStronglyMeasurable[mΩ] (condProb m P X b) P :=
    (stronglyMeasurable_condExp (m := m) (f := (X ⁻¹' {b}).indicator (fun _ => (1 : ℝ)))
      (μ := P)).mono hm |>.aestronglyMeasurable
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (Real.continuous_negMulLog.comp_aestronglyMeasurable hsm) ?_
  filter_upwards [condProb_nonneg_le P X hm hX b] with ω ⟨h0, h1⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.negMulLog_nonneg h0 h1)]
  have := Real.negMulLog_le_one_sub_self h0
  linarith

/-- `H(X | m) · log 2` as a finite sum of integrals (for finite-valued measurable `X`). -/
lemma condEntropy_mul_log (hfin : (Set.range X).Finite) {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hX : Measurable[mΩ] X) :
    condEntropy m P X * Real.log 2 =
      ∑ b ∈ hfin.toFinset, ∫ ω, Real.negMulLog (condProb m P X b ω) ∂P := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold condEntropy
  rw [div_mul_cancel₀ _ hlog, ← integral_finsetSum]
  · congr 1
    ext ω
    apply finsum_eq_sum_of_support_subset
    intro b hb
    simp only [Function.mem_support] at hb
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra h
    apply hb
    simp [condProb_of_not_mem_range P X m b h]
  · intro b _
    exact integrable_negMulLog_condProb P X hm hX b


lemma condEntropy_congr (hfin : (Set.range X).Finite) (hX : Measurable[mΩ] X)
    {m₁ m₂ : MeasurableSpace Ω} (h1 : m₁ ≤ mΩ) (h2 : m₂ ≤ mΩ)
    (h : ∀ b, condProb m₁ P X b =ᵐ[P] condProb m₂ P X b) :
    condEntropy m₁ P X = condEntropy m₂ P X := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  refine mul_right_cancel₀ hlog ?_
  rw [condEntropy_mul_log P X hfin h1 hX, condEntropy_mul_log P X hfin h2 hX]
  refine Finset.sum_congr rfl (fun b _ => integral_congr_ae ?_)
  filter_upwards [h b] with ω hω
  simp [hω]

end General

section Binary

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)

/-- A mean-zero `±1`-valued variable has entropy `1` bit. -/
theorem entropy_binary (hX : Measurable[mΩ] X) (hb : ∀ ω, X ω = 1 ∨ X ω = -1)
    (hmean : ∫ ω, X ω ∂P = 0) : entropy P X = 1 := by
  have hS : MeasurableSet (X ⁻¹' {(1 : ℝ)}) := hX (measurableSet_singleton _)
  have hXeq : X = fun ω => 2 * ((X ⁻¹' {(1 : ℝ)}).indicator (fun _ => (1 : ℝ)) ω) - 1 := by
    funext ω
    rcases hb ω with h | h <;> simp [h, Set.indicator] <;> norm_num
  have hp : P.real (X ⁻¹' {(1 : ℝ)}) = 1 / 2 := by
    rw [hXeq] at hmean
    rw [integral_sub ((integrable_const (1 : ℝ)).indicator hS |>.const_mul 2) (integrable_const _),
      integral_const_mul, integral_indicator_const _ hS] at hmean
    simp at hmean
    linarith
  have hm : X ⁻¹' {(-1 : ℝ)} = (X ⁻¹' {(1 : ℝ)})ᶜ := by
    ext ω; rcases hb ω with h | h <;> simp [h] <;> norm_num
  have hq : P.real (X ⁻¹' {(-1 : ℝ)}) = 1 / 2 := by
    rw [hm, probReal_compl_eq_one_sub hS, hp]; norm_num
  unfold entropy
  have hsupp : (Function.support fun b : ℝ => Real.negMulLog (P.real (X ⁻¹' {b}))) ⊆
      (({1, -1} : Finset ℝ) : Set ℝ) := by
    intro b hb'
    simp only [Function.mem_support] at hb'
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra h
    push_neg at h
    apply hb'
    have : X ⁻¹' {b} = ∅ := by
      ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hω; rcases hb ω with h' | h' <;> [exact h.1 (hω.symm.trans h'); exact h.2 (hω.symm.trans h')]
    simp [this]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_pair (by norm_num), hp, hq]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have : Real.negMulLog (1 / 2 : ℝ) = Real.log 2 / 2 := by
    simp [Real.negMulLog, Real.log_inv]; ring
  rw [this]; field_simp; ring

end Binary

section Prefix

variable {Ω : Type*} {k : ℕ} {α : Fin k → Type*} [∀ l, MeasurableSpace (α l)]
  (Z : ∀ l, Ω → α l)

lemma sourceSigma_mono {T T' : Finset (Fin k)} (h : T ⊆ T') : sourceSigma Z T ≤ sourceSigma Z T' :=
  iSup_mono' (fun j => ⟨j, iSup_mono' (fun hj => ⟨h hj, le_rfl⟩)⟩)

lemma sourceSigma_le {mΩ : MeasurableSpace Ω} (hZ : ∀ l, Measurable (Z l)) (T : Finset (Fin k)) :
    sourceSigma Z T ≤ mΩ :=
  iSup₂_le (fun l _ => (hZ l).comap_le)

lemma prefixSigma_succ (j : Fin k) :
    prefixSigma Z ((j : ℕ) + 1) = MeasurableSpace.comap (Z j) inferInstance ⊔ prefixSigma Z j := by
  have : (Finset.univ.filter (fun l : Fin k => (l : ℕ) < (j : ℕ) + 1)) =
      insert j (Finset.univ.filter (fun l : Fin k => (l : ℕ) < (j : ℕ))) := by
    ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h; by_cases hl : l = j
      · exact Or.inl hl
      · right; have := Fin.val_ne_of_ne hl; omega
    · rintro (rfl | h); omega; omega
  simp only [prefixSigma, sourceSigma, this, Finset.iSup_insert]

end Prefix

section Indep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {k : ℕ} {α : Fin k → Type*}
  [∀ l, MeasurableSpace (α l)] (P : Measure Ω) [IsProbabilityMeasure P] (Z : ∀ l, Ω → α l)

lemma indep_comap_sourceSigma (hmeas : ∀ l, Measurable (Z l)) (hZ : iIndepFun Z P) (j : Fin k) (T : Finset (Fin k)) (hj : j ∉ T) :
    Indep (MeasurableSpace.comap (Z j) inferInstance) (sourceSigma Z T) P := by
  have h := indep_iSup_of_disjoint (m := fun l => MeasurableSpace.comap (Z l) inferInstance)
    (μ := P) (fun l => ?_) hZ (S := {j}) (T := (T : Set (Fin k))) (by simpa using hj)
  · simpa [sourceSigma] using h
  · exact (hmeas l).comap_le

end Indep


/-- Source `j` unused by `X` (which is `σ(Z_B)`-measurable) does not change conditional
probabilities of `X`. -/
theorem condProb_succ_eq {n k : ℕ} {S : InformationSkeleton n k} (π : CoordinationProfile S)
    (i : Fin n) (j : Fin k) (hj : j ∉ S.B i) (b : ℝ) :
    condProb (prefixSigma π.Z ((j : ℕ) + 1)) π.P (π.X i) b =ᵐ[π.P]
      condProb (prefixSigma π.Z (j : ℕ)) π.P (π.X i) b := by
  classical
  set T : Finset (Fin k) := S.B i ∪ Finset.univ.filter (fun l : Fin k => (l : ℕ) < (j : ℕ)) with hT
  have hjT : j ∉ T := by simp [hT, hj]
  have hZ := π.Z_measurable
  have hind := indep_comap_sourceSigma π.P π.Z hZ π.Z_indep j T hjT
  have hXm : Measurable[π.mΩ] (π.X i) := (π.X_measurable i).mono (sourceSigma_le π.Z hZ _) le_rfl
  have hDmeas : Measurable[sourceSigma π.Z T] (π.X i) :=
    (π.X_measurable i).mono (sourceSigma_mono π.Z Finset.subset_union_left) le_rfl
  have hY : StronglyMeasurable[sourceSigma π.Z T]
      ((π.X i ⁻¹' {b}).indicator (fun _ => (1 : ℝ))) :=
    (measurable_const.indicator (hDmeas (measurableSet_singleton b))).stronglyMeasurable
  have hYi : Integrable ((π.X i ⁻¹' {b}).indicator (fun _ => (1 : ℝ))) π.P :=
    (integrable_const (1 : ℝ)).indicator (hXm (measurableSet_singleton b))
  have := condExp_sup_indep π.P (F := prefixSigma π.Z (j : ℕ))
    (C := MeasurableSpace.comap (π.Z j) inferInstance) (D := sourceSigma π.Z T)
    (sourceSigma_le π.Z hZ _) (hZ j).comap_le (sourceSigma_le π.Z hZ _)
    (sourceSigma_mono π.Z Finset.subset_union_right) hind _ hY hYi
  unfold condProb
  rw [prefixSigma_succ, sup_comm]
  exact this

end EntropyLocalCoord.Dev.Support

namespace EntropyLocalCoord.Leader

open EntropyLocalCoord.Dev.Support in
theorem chk_infoMeasure_prob_support {n k : ℕ} (S : InformationSkeleton n k)
    (π : CoordinationProfile S) (hπ : π.IsBinary) (i : Fin n) :
    (∀ j, 0 ≤ infoMeasure π.P π.Z (π.X i) j) ∧
      ∑ j, infoMeasure π.P π.Z (π.X i) j = 1 ∧
      ∀ j, j ∉ S.B i → infoMeasure π.P π.Z (π.X i) j = 0 := by
  have hZ := π.Z_measurable
  have hXm : Measurable[π.mΩ] (π.X i) := (π.X_measurable i).mono (sourceSigma_le π.Z hZ _) le_rfl
  have hfin : (Set.range (π.X i)).Finite := by
    refine (Set.toFinite ({1, -1} : Set ℝ)).subset ?_
    rintro _ ⟨ω, rfl⟩
    rcases hπ i ω with h | h <;> simp [h]
  have hXu : Measurable[sourceSigma π.Z Finset.univ] (π.X i) :=
    (π.X_measurable i).mono (sourceSigma_mono π.Z (Finset.subset_univ _)) le_rfl
  obtain ⟨hmono, h0, hk, -⟩ := infoCDF_mono π.P π.Z hZ (π.X i) hfin hXu
  have hH : entropy π.P (π.X i) = 1 :=
    entropy_binary π.P (π.X i) hXm (hπ i) (π.mean_zero i)
  refine ⟨fun j => ?_, ?_, fun j hj => ?_⟩
  · unfold infoMeasure
    have := hmono (Set.mem_Iic.mpr (Nat.succ_le_of_lt j.2)) (Set.mem_Iic.mpr j.2.le)
    have := @hmono (j : ℕ) (Set.mem_Iic.mpr j.2.le) ((j : ℕ) + 1)
      (Set.mem_Iic.mpr (Nat.succ_le_of_lt j.2)) (Nat.le_succ _)
    linarith
  · unfold infoMeasure
    rw [Fin.sum_univ_eq_sum_range (fun n => infoCDF π.P π.Z (π.X i) (n + 1) -
      infoCDF π.P π.Z (π.X i) n) k, Finset.sum_range_sub (infoCDF π.P π.Z (π.X i)) k, h0, hk, hH]
    ring
  · unfold infoMeasure infoCDF mutualInfo
    rw [condEntropy_congr π.P (π.X i) hfin hXm (sourceSigma_le π.Z hZ _) (sourceSigma_le π.Z hZ _)
      (condProb_succ_eq π i j hj)]
    ring

end EntropyLocalCoord.Leader
end

theorem solution : type_of% @EntropyLocalCoord.Leader.chk_infoMeasure_prob_support := @EntropyLocalCoord.Leader.chk_infoMeasure_prob_support
