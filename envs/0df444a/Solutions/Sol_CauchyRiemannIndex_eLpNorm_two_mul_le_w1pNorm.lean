-- Prove2me | solution 1 for CauchyRiemannIndex.eLpNorm_two_mul_le_w1pNorm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T11:01:49.428357+00:00
-- url     : https://prove2.me/submissions/91804ac9-85a7-4fcf-b072-9c4d76163a7d

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Operator.Prod

-- ===== Scratch/CR411Bridge.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-- Matrices as continuous linear maps of `ℝ²ⁿ`, continuously in the matrix. -/
def matCLM (n : ℕ) : Mat n →ₗ[ℝ] (Vec n →L[ℝ] Vec n) :=
  (LinearMap.toContinuousLinearMap : (Vec n →ₗ[ℝ] Vec n) ≃ₗ[ℝ] (Vec n →L[ℝ] Vec n)).toLinearMap ∘ₗ
    (Matrix.toEuclideanLin : Mat n ≃ₗ[ℝ] (Vec n →ₗ[ℝ] Vec n)).toLinearMap

lemma matCLM_apply (A : Mat n) (v : Vec n) : matCLM n A v = Matrix.toEuclideanLin A v := rfl

lemma continuous_matCLM : Continuous (matCLM n) := LinearMap.continuous_of_finiteDimensional _

/-- A uniform operator bound for a continuous `1`-periodic matrix loop. -/
lemma exists_bound_loop (Sinf : ℝ → Mat n) (hc : Continuous Sinf) (hper : Function.Periodic Sinf 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t (v : Vec n), ‖Matrix.toEuclideanLin (Sinf t) v‖ ≤ M * ‖v‖ := by
  have hg : Continuous fun t => matCLM n (Sinf t) := continuous_matCLM.comp hc
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t v => ?_⟩
  obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ one_pos t
  rw [← matCLM_apply, hty]
  calc ‖matCLM n (Sinf y) v‖ ≤ ‖matCLM n (Sinf y)‖ * ‖v‖ := (matCLM n (Sinf y)).le_opNorm v
    _ ≤ max C 0 * ‖v‖ := by
      gcongr
      exact (hC y (Set.Ico_subset_Icc_self hy)).trans (le_max_left _ _)

lemma exists_bound_mat (A : Mat n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (v : Vec n), ‖Matrix.toEuclideanLin A v‖ ≤ M * ‖v‖ :=
  ⟨‖matCLM n A‖, norm_nonneg _, fun v => (matCLM n A).le_opNorm v⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A continuous map on `ℝ × ℝ` vanishing for large `|s|` is in `L^p` of the strip. -/
lemma memLp_of_vanish {E : Type*} [NormedAddCommGroup E] (g : ℝ × ℝ → E) (hg : Continuous g)
    (R : ℝ) (hR : ∀ s t, R < |s| → g (s, t) = 0) : MemLp g p cylMeasure := by
  set K : Set (ℝ × ℝ) := Set.Icc (-R) R ×ˢ Set.Icc 0 1 with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKm : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hae : K.indicator g =ᵐ[cylMeasure] g := by
    unfold cylMeasure
    refine ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_Ico) ?_
    rintro ⟨s, t⟩ ⟨-, ht⟩
    by_cases hx : (s, t) ∈ K
    · simp [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have : R < |s| := by
        by_contra h
        push_neg at h
        exact hx ⟨abs_le.1 h, Set.Ico_subset_Icc_self ht⟩
      exact (hR s t this).symm
  refine (memLp_congr_ae hae).1 ((memLp_indicator_iff_restrict hKm).2 ?_)
  haveI : IsFiniteMeasure (cylMeasure.restrict K) := by
    refine isFiniteMeasure_restrict.2 (ne_of_lt (lt_of_le_of_lt ?_ (hKc.measure_lt_top (μ := (volume : Measure (ℝ × ℝ))))))
    exact Measure.le_iff'.1 Measure.restrict_le_self K
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hg.continuousOn
  exact MemLp.of_bound hg.aestronglyMeasurable C (ae_restrict_of_forall_mem hKm hC)

lemma partialS_eq_zero {u : ℝ × ℝ → Vec n} (R : ℝ) (hR : ∀ s t, R < |s| → u (s, t) = 0)
    {s t : ℝ} (hs : R < |s|) : partialS u (s, t) = 0 := by
  have hU : IsOpen {x : ℝ × ℝ | R < |x.1|} := isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : u =ᶠ[𝓝 (s, t)] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hs) fun x hx => hR x.1 x.2 hx
  simp [partialS, hev.fderiv_eq]

lemma partialT_eq_zero {u : ℝ × ℝ → Vec n} (R : ℝ) (hR : ∀ s t, R < |s| → u (s, t) = 0)
    {s t : ℝ} (hs : R < |s|) : partialT u (s, t) = 0 := by
  have hU : IsOpen {x : ℝ × ℝ | R < |x.1|} := isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : u =ᶠ[𝓝 (s, t)] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hs) fun x hx => hR x.1 x.2 hx
  simp [partialT, hev.fderiv_eq]

lemma IsTestSection.continuous {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : Continuous u :=
  hu.1.continuous

lemma IsTestSection.continuous_partialS {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    Continuous (partialS u) :=
  (hu.1.continuous_fderiv (by simp)).clm_apply continuous_const

lemma IsTestSection.continuous_partialT {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    Continuous (partialT u) :=
  (hu.1.continuous_fderiv (by simp)).clm_apply continuous_const

lemma IsTestSection.memLp {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : MemLp u p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish u hu.continuous R hR

lemma IsTestSection.memLp_partialS {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    MemLp (partialS u) p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish _ hu.continuous_partialS R fun s t hs => partialS_eq_zero R hR hs

lemma IsTestSection.memLp_partialT {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    MemLp (partialT u) p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish _ hu.continuous_partialT R fun s t hs => partialT_eq_zero R hR hs

lemma IsTestSection.sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    IsTestSection (u - v) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  obtain ⟨R₂, h₂⟩ := hv.2.2
  refine ⟨ContDiff.sub hu.1 hv.1, fun s t => by simp [hu.2.1, hv.2.1], max R₁ R₂, fun s t hs => ?_⟩
  simp [h₁ s t (lt_of_le_of_lt (le_max_left _ _) hs), h₂ s t (lt_of_le_of_lt (le_max_right _ _) hs)]

lemma IsTestSection.add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    IsTestSection (u + v) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  obtain ⟨R₂, h₂⟩ := hv.2.2
  refine ⟨ContDiff.add hu.1 hv.1, fun s t => by simp [hu.2.1, hv.2.1], max R₁ R₂, fun s t hs => ?_⟩
  simp [h₁ s t (lt_of_le_of_lt (le_max_left _ _) hs), h₂ s t (lt_of_le_of_lt (le_max_right _ _) hs)]

lemma IsTestSection.smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    IsTestSection (c • u) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  refine ⟨ContDiff.const_smul c hu.1, fun s t => by simp [hu.2.1], R₁, fun s t hs => ?_⟩
  simp [h₁ s t hs]

lemma isTestSection_zero : IsTestSection (0 : ℝ × ℝ → Vec n) :=
  ⟨contDiff_const, fun _ _ => rfl, 0, fun _ _ _ => rfl⟩

lemma partialS_add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialS (u + v) = partialS u + partialS v := by
  funext x
  simp only [partialS, Pi.add_apply]
  rw [fderiv_add ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialT_add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialT (u + v) = partialT u + partialT v := by
  funext x
  simp only [partialT, Pi.add_apply]
  rw [fderiv_add ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialS_sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialS (u - v) = partialS u - partialS v := by
  funext x
  simp only [partialS, Pi.sub_apply]
  rw [fderiv_sub ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialT_sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialT (u - v) = partialT u - partialT v := by
  funext x
  simp only [partialT, Pi.sub_apply]
  rw [fderiv_sub ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialS_smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    partialS (c • u) = c • partialS u := by
  funext x
  simp only [partialS, Pi.smul_apply]
  rw [fderiv_const_smul ((hu.1.differentiable (by simp)) x)]
  rfl

lemma partialT_smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    partialT (c • u) = c • partialT u := by
  funext x
  simp only [partialT, Pi.smul_apply]
  rw [fderiv_const_smul ((hu.1.differentiable (by simp)) x)]
  rfl

lemma partialS_zero : partialS (0 : ℝ × ℝ → Vec n) = 0 := by
  funext x; simp [partialS]

lemma partialT_zero : partialT (0 : ℝ × ℝ → Vec n) = 0 := by
  funext x; simp [partialT]

end

end CauchyRiemannIndex

-- ===== Scratch/IPSob.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

instance ips_haar : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

/-! ### Periodic integrals over five periods (copied from `CRLocPer`) -/

def ipsS (k : ℤ) : Set (ℝ × ℝ) := univ ×ˢ Ico (k : ℝ) (k + 1)

lemma ipsS_floor {k : ℤ} {x : ℝ × ℝ} (h : x ∈ ipsS k) : ⌊x.2⌋ = k :=
  Int.floor_eq_iff.2 ⟨h.2.1, h.2.2⟩

lemma ips_shift (G : ℝ × ℝ → ℝ≥0∞) (hG : ∀ s t, G (s, t + 1) = G (s, t)) (k : ℤ) :
    ∫⁻ x in ipsS k, G x = ∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, G x := by
  set e : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.addRight (k : ℝ))
  have he : ∀ x : ℝ × ℝ, e x = (x.1, x.2 + k) := fun x => rfl
  have hGk : ∀ x : ℝ × ℝ, G (e x) = G x := by
    rintro ⟨s, t⟩
    have hp : Function.Periodic (fun t => G (s, t)) 1 := fun t => hG s t
    have := hp.int_mul k t
    rw [he]
    simpa using this
  have mp : MeasurePreserving e (volume : Measure (ℝ × ℝ)) volume :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (measurePreserving_add_right (volume : Measure ℝ) (k : ℝ))
  have hpre : e ⁻¹' ipsS k = univ ×ˢ Ico (0 : ℝ) 1 := by
    ext ⟨s, t⟩
    simp only [ipsS, mem_preimage, he, mem_prod, mem_univ, true_and, mem_Ico]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have h := mp.setLIntegral_comp_preimage_emb e.measurableEmbedding G (ipsS k)
  rw [hpre] at h
  rw [← h]
  exact setLIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Ico)
    (fun x _ => hGk x)

lemma ips_five (G : ℝ × ℝ → ℝ≥0∞) (hG : ∀ s t, G (s, t + 1) = G (s, t)) :
    ∫⁻ x in univ ×ˢ Ico (-2 : ℝ) 3, G x ≤ 5 * ∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, G x := by
  have hsub : univ ×ˢ Ico (-2 : ℝ) 3 ⊆ ⋃ k ∈ Finset.Icc (-2 : ℤ) 2, ipsS k := by
    rintro ⟨s, t⟩ ⟨-, h1, h2⟩
    simp only [mem_iUnion, Finset.mem_Icc, exists_prop]
    refine ⟨⌊t⌋, ⟨?_, ?_⟩, ?_⟩
    · exact Int.le_floor.2 (by push_cast; linarith)
    · have : ⌊t⌋ < 3 := Int.floor_lt.2 (by push_cast; linarith)
      omega
    · exact ⟨mem_univ _, Int.floor_le t, Int.lt_floor_add_one t⟩
  have hd : (↑(Finset.Icc (-2 : ℤ) 2) : Set ℤ).PairwiseDisjoint ipsS := by
    intro k _ j _ hkj
    exact Set.disjoint_left.2 fun x hk hj => hkj (by rw [← ipsS_floor hk, ← ipsS_floor hj])
  have hm : ∀ k ∈ Finset.Icc (-2 : ℤ) 2, MeasurableSet (ipsS k) :=
    fun k _ => MeasurableSet.univ.prod measurableSet_Ico
  calc ∫⁻ x in univ ×ˢ Ico (-2 : ℝ) 3, G x
      ≤ ∫⁻ x in ⋃ k ∈ Finset.Icc (-2 : ℤ) 2, ipsS k, G x := lintegral_mono_set hsub
    _ = ∑ k ∈ Finset.Icc (-2 : ℤ) 2, ∫⁻ x in ipsS k, G x := lintegral_biUnion_finset hd hm G
    _ = ∑ k ∈ Finset.Icc (-2 : ℤ) 2, ∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, G x :=
        Finset.sum_congr rfl fun k _ => ips_shift G hG k
    _ = 5 * ∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, G x := by
        rw [Finset.sum_const, nsmul_eq_mul]
        congr 1

lemma ips_fderiv_per {u : ℝ × ℝ → Vec n} (hper : ∀ s t, u (s, t + 1) = u (s, t)) (s t : ℝ) :
    fderiv ℝ u (s, t + 1) = fderiv ℝ u (s, t) := by
  have hfun : (fun y : ℝ × ℝ => u (y + ((0 : ℝ), (1 : ℝ)))) = u := by
    funext ⟨a, b⟩
    simp only [Prod.mk_add_mk, add_zero, hper]
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := ((s, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ))
  rw [hfun, Prod.mk_add_mk, add_zero] at h
  exact h.symm

lemma ips_fderiv_le {u : ℝ × ℝ → Vec n} (x : ℝ × ℝ) :
    ‖fderiv ℝ u x‖ ≤ ‖partialS u x‖ + ‖partialT u x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv : fderiv ℝ u x v = v.1 • partialS u x + v.2 • partialT u x := by
    simp only [partialS, partialT, ← map_smul, ← map_add]
    congr 1; ext <;> simp
  rw [hv]
  calc ‖v.1 • partialS u x + v.2 • partialT u x‖
      ≤ ‖v.1‖ * ‖partialS u x‖ + ‖v.2‖ * ‖partialT u x‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
    _ ≤ ‖v‖ * ‖partialS u x‖ + ‖v‖ * ‖partialT u x‖ := by
        gcongr
        · exact norm_fst_le v
        · exact norm_snd_le v
    _ = ‖v‖ * (‖partialS u x‖ + ‖partialT u x‖) := by ring
    _ = (‖partialS u x‖ + ‖partialT u x‖) * ‖v‖ := by ring

/-! ### Elementary inequalities -/

lemma ips_young {a b P : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hP : 1 < P) :
    a ^ (P - 1) * b ≤ a ^ P + b ^ P := by
  have hP' : (P - 1) + 1 ≠ 0 := by linarith
  rcases le_total a b with h | h
  · have h1 : a ^ (P - 1) ≤ b ^ (P - 1) := Real.rpow_le_rpow ha h (by linarith)
    have h2 : b ^ (P - 1) * b = b ^ P := by
      rw [← Real.rpow_add_one' hb hP']; congr 1; ring
    have : a ^ (P - 1) * b ≤ b ^ P := by
      rw [← h2]; exact mul_le_mul_of_nonneg_right h1 hb
    linarith [Real.rpow_nonneg ha P]
  · have h2 : a ^ (P - 1) * a = a ^ P := by
      rw [← Real.rpow_add_one' ha hP']; congr 1; ring
    have : a ^ (P - 1) * b ≤ a ^ P := by
      rw [← h2]; exact mul_le_mul_of_nonneg_left h (Real.rpow_nonneg ha _)
    linarith [Real.rpow_nonneg hb P]

/-! ### The cut-off in `t` -/

/-- A smooth cut-off in `t`, equal to `1` on `[0, 1]` and supported in `[-3/2, 5/2]`. -/
def ipsχ : ContDiffBump (1 / 2 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

lemma ipsχ_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : ipsχ t = 1 := by
  apply ipsχ.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  change -1 ≤ t - 1 / 2 ∧ t - 1 / 2 ≤ 1
  constructor <;> linarith

lemma ipsχ_tsupport : tsupport (ipsχ : ℝ → ℝ) ⊆ Ico (-2 : ℝ) 3 := by
  rw [ipsχ.tsupport_eq]
  intro t ht
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at ht
  change -2 ≤ t - 1 / 2 ∧ t - 1 / 2 ≤ 2 at ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

lemma ipsχ_deriv_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, ‖fderiv ℝ (ipsχ : ℝ → ℝ) t‖ ≤ M := by
  have hc : Continuous (fderiv ℝ (ipsχ : ℝ → ℝ)) :=
    (ipsχ.contDiff (n := 1)).continuous_fderiv (by simp)
  have hs : HasCompactSupport (fderiv ℝ (ipsχ : ℝ → ℝ)) := ipsχ.hasCompactSupport.fderiv (𝕜 := ℝ)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max C 0, le_max_right _ _, fun t => (hC t).trans (le_max_left _ _)⟩

end

end CauchyRiemannIndex

-- ===== Scratch/IPSob2.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

lemma ips_enorm_rpow {E : Type*} [NormedAddCommGroup E] (v : E) {P : ℝ} (hP : 0 ≤ P) :
    ENNReal.ofReal (‖v‖ ^ P) = ‖v‖ₑ ^ P := by
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hP, ofReal_norm_eq_enorm]

lemma ips_v_contDiff {u : ℝ × ℝ → Vec n} (hu : ContDiff ℝ 1 u) {P : ℝ} (hP : 1 < P) :
    ContDiff ℝ 1 (fun x : ℝ × ℝ => ipsχ x.2 * ‖u x‖ ^ P) :=
  ((ipsχ.contDiff).comp contDiff_snd).mul (hu.norm_rpow hP)

lemma ips_v_compact {u : ℝ × ℝ → Vec n} (R : ℝ) (hR : ∀ s t, R < |s| → u (s, t) = 0)
    {P : ℝ} (hP : 1 < P) :
    HasCompactSupport (fun x : ℝ × ℝ => ipsχ x.2 * ‖u x‖ ^ P) := by
  refine HasCompactSupport.intro (K := Icc (-R) R ×ˢ Icc (-2 : ℝ) 3)
    (isCompact_Icc.prod isCompact_Icc) fun x hx => ?_
  obtain ⟨s, t⟩ := x
  by_cases hs : R < |s|
  · simp only [hR s t hs, norm_zero, Real.zero_rpow (by linarith : P ≠ 0), mul_zero]
  · have ht : t ∉ Icc (-2 : ℝ) 3 := by
      intro ht
      exact hx ⟨abs_le.1 (not_lt.1 hs), ht⟩
    have : t ∉ tsupport (ipsχ : ℝ → ℝ) := fun h => ht (Ico_subset_Icc_self (ipsχ_tsupport h))
    simp only [image_eq_zero_of_notMem_tsupport this, zero_mul]

lemma ips_dv_le {u : ℝ × ℝ → Vec n} (hu : ContDiff ℝ 1 u) {P : ℝ} (hP : 1 < P) {M : ℝ}
    (hM : ∀ t : ℝ, ‖fderiv ℝ (ipsχ : ℝ → ℝ) t‖ ≤ M) (x : ℝ × ℝ) :
    ‖fderiv ℝ (fun x : ℝ × ℝ => ipsχ x.2 * ‖u x‖ ^ P) x‖ ≤
      P * ‖u x‖ ^ (P - 1) * (‖partialS u x‖ + ‖partialT u x‖) + M * ‖u x‖ ^ P := by
  have h1 : HasFDerivAt (fun x : ℝ × ℝ => ipsχ x.2)
      ((fderiv ℝ (ipsχ : ℝ → ℝ) x.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) x :=
    ((ipsχ.contDiff (n := 1)).differentiable one_ne_zero x.2).hasFDerivAt.comp x
      (hasFDerivAt_snd)
  have h2 : HasFDerivAt (fun x : ℝ × ℝ => ‖u x‖ ^ P)
      (fderiv ℝ (fun x : ℝ × ℝ => ‖u x‖ ^ P) x) x :=
    ((hu.differentiable one_ne_zero).norm_rpow hP x).hasFDerivAt
  have h3 : fderiv ℝ (fun x : ℝ × ℝ => ipsχ x.2 * ‖u x‖ ^ P) x =
      ipsχ x.2 • fderiv ℝ (fun x : ℝ × ℝ => ‖u x‖ ^ P) x +
        (‖u x‖ ^ P) • (fderiv ℝ (ipsχ : ℝ → ℝ) x.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ) :=
    (h1.mul h2).fderiv
  rw [h3]
  have hc0 : 0 ≤ ipsχ x.2 := ipsχ.nonneg
  have hc1 : ipsχ x.2 ≤ 1 := ipsχ.le_one
  have hd : ‖fderiv ℝ (fun x : ℝ × ℝ => ‖u x‖ ^ P) x‖ ≤
      P * ‖u x‖ ^ (P - 1) * (‖partialS u x‖ + ‖partialT u x‖) := by
    refine (norm_fderiv_norm_rpow_le (hu.differentiable one_ne_zero) hP).trans ?_
    gcongr
    exact ips_fderiv_le x
  have hc : ‖(fderiv ℝ (ipsχ : ℝ → ℝ) x.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)‖ ≤ M := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖fderiv ℝ (ipsχ : ℝ → ℝ) x.2‖ * ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖
        ≤ M * 1 := by
          gcongr
          · exact (norm_nonneg _).trans (hM 0)
          · exact hM x.2
          · exact ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
      _ = M := mul_one M
  have hu0 : 0 ≤ ‖u x‖ ^ P := Real.rpow_nonneg (norm_nonneg _) _
  calc ‖ipsχ x.2 • fderiv ℝ (fun x : ℝ × ℝ => ‖u x‖ ^ P) x +
        (‖u x‖ ^ P) • (fderiv ℝ (ipsχ : ℝ → ℝ) x.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)‖
      ≤ ‖ipsχ x.2 • fderiv ℝ (fun x : ℝ × ℝ => ‖u x‖ ^ P) x‖ +
        ‖(‖u x‖ ^ P) • (fderiv ℝ (ipsχ : ℝ → ℝ) x.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)‖ :=
        norm_add_le _ _
    _ = ipsχ x.2 * ‖fderiv ℝ (fun x : ℝ × ℝ => ‖u x‖ ^ P) x‖ +
        ‖u x‖ ^ P * ‖(fderiv ℝ (ipsχ : ℝ → ℝ) x.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hc0, Real.norm_of_nonneg hu0]
    _ ≤ 1 * (P * ‖u x‖ ^ (P - 1) * (‖partialS u x‖ + ‖partialT u x‖)) + ‖u x‖ ^ P * M := by
        gcongr
    _ = _ := by ring

lemma ips_real_bound {a b c P M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hP : 1 < P)
    (hM : 0 ≤ M) :
    P * a ^ (P - 1) * (b + c) + M * a ^ P ≤ (2 * P + M) * (a ^ P + b ^ P + c ^ P) := by
  have h1 := ips_young ha hb hP
  have h2 := ips_young ha hc hP
  have hbP := Real.rpow_nonneg hb P
  have hcP := Real.rpow_nonneg hc P
  have haP := Real.rpow_nonneg ha P
  have hP0 : 0 ≤ P := by linarith
  have e : P * a ^ (P - 1) * (b + c) = P * (a ^ (P - 1) * b) + P * (a ^ (P - 1) * c) := by ring
  rw [e]
  have k1 : P * (a ^ (P - 1) * b) ≤ P * (a ^ P + b ^ P) := mul_le_mul_of_nonneg_left h1 hP0
  have k2 : P * (a ^ (P - 1) * c) ≤ P * (a ^ P + c ^ P) := mul_le_mul_of_nonneg_left h2 hP0
  nlinarith

lemma ips_finrank : NNReal.HolderConjugate (Module.finrank ℝ (ℝ × ℝ)) 2 := by
  have : (Module.finrank ℝ (ℝ × ℝ) : ℝ≥0) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]; norm_num
  rw [this]; exact NNReal.HolderConjugate.two_two

/-- The main estimate in lintegral form. -/
lemma ips_main (P : ℝ) (hP : 1 < P) : ∃ B : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
    ∫⁻ x, ‖u x‖ₑ ^ (2 * P) ∂cylMeasure ≤
      ((B : ℝ≥0∞) * (∫⁻ x, ‖u x‖ₑ ^ P ∂cylMeasure + ∫⁻ x, ‖partialS u x‖ₑ ^ P ∂cylMeasure +
        ∫⁻ x, ‖partialT u x‖ₑ ^ P ∂cylMeasure)) ^ (2 : ℝ) := by
  obtain ⟨M, hM0, hM⟩ := ipsχ_deriv_bound
  set K : ℝ≥0 := eLpNormLESNormFDerivOneConst (volume : Measure (ℝ × ℝ)) (2 : ℝ≥0)
  refine ⟨K * 5 * (2 * P + M).toNNReal, fun u hu => ?_⟩
  obtain ⟨R, hR⟩ := hu.2.2
  have hu1 : ContDiff ℝ 1 u := hu.1.of_le (by simp)
  have hP0 : 0 ≤ P := by linarith
  set v : ℝ × ℝ → ℝ := fun x => ipsχ x.2 * ‖u x‖ ^ P with hv_def
  have hGNS : eLpNorm v (2 : ℝ≥0) volume ≤ K * eLpNorm (fderiv ℝ v) 1 volume :=
    eLpNorm_le_eLpNorm_fderiv_one volume (ips_v_contDiff hu1 hP) (ips_v_compact R hR hP)
      ips_finrank
  -- left-hand side
  have hL : ∫⁻ x, ‖u x‖ₑ ^ (2 * P) ∂cylMeasure ≤ ∫⁻ x, ‖v x‖ₑ ^ (2 : ℝ) := by
    unfold cylMeasure
    calc ∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, ‖u x‖ₑ ^ (2 * P)
        = ∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, ‖v x‖ₑ ^ (2 : ℝ) := by
          refine setLIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Ico) ?_
          rintro ⟨s, t⟩ ⟨-, ht⟩
          have hv : v (s, t) = ‖u (s, t)‖ ^ P := by
            simp only [hv_def, ipsχ_one ht.1 ht.2.le, one_mul]
          show ‖u (s, t)‖ₑ ^ (2 * P) = ‖v (s, t)‖ₑ ^ (2 : ℝ)
          rw [hv, Real.enorm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
            ips_enorm_rpow _ hP0, ← ENNReal.rpow_mul, mul_comm]
      _ ≤ ∫⁻ x, ‖v x‖ₑ ^ (2 : ℝ) := setLIntegral_le_lintegral _ _
  have hL2 : ∫⁻ x, ‖v x‖ₑ ^ (2 : ℝ) = eLpNorm v (2 : ℝ≥0) volume ^ (2 : ℝ) := by
    rw [eLpNorm_nnreal_eq_lintegral (by norm_num), ← ENNReal.rpow_mul]
    norm_num
  -- the derivative
  set C₀ : ℝ := 2 * P + M
  set H : ℝ × ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal C₀ *
    (‖u x‖ₑ ^ P + ‖partialS u x‖ₑ ^ P + ‖partialT u x‖ₑ ^ P) with hH
  have hpt : ∀ x, ‖fderiv ℝ v x‖ₑ ≤ H x := by
    intro x
    have h1 := ips_dv_le hu1 hP hM x
    have h2 := ips_real_bound (norm_nonneg (u x)) (norm_nonneg (partialS u x))
      (norm_nonneg (partialT u x)) hP hM0
    rw [← ofReal_norm_eq_enorm, hH]
    simp only
    rw [← ips_enorm_rpow _ hP0, ← ips_enorm_rpow _ hP0, ← ips_enorm_rpow _ hP0,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (h1.trans h2)
  have hsupp : Function.support (fun x => ‖fderiv ℝ v x‖ₑ) ⊆ univ ×ˢ Ico (-2 : ℝ) 3 := by
    intro x hx
    refine ⟨mem_univ _, ?_⟩
    by_contra hx2
    apply hx
    have hx' : x ∉ tsupport v := by
      intro h
      have h' := tsupport_mul_subset_left h
      have h'' : x ∈ (Prod.snd) ⁻¹' tsupport (ipsχ : ℝ → ℝ) :=
        tsupport_comp_subset_preimage (ipsχ : ℝ → ℝ) continuous_snd h'
      exact hx2 (ipsχ_tsupport h'')
    show ‖fderiv ℝ v x‖ₑ = 0
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx', ← ofReal_norm_eq_enorm, norm_zero, ENNReal.ofReal_zero]
  have hper : ∀ s t, H (s, t + 1) = H (s, t) := by
    intro s t
    simp only [hH, partialS, partialT, ips_fderiv_per hu.2.1, hu.2.1]
  have mu : Measurable fun x => ‖u x‖ₑ ^ P :=
    (measurable_enorm.comp hu.continuous.measurable).pow_const P
  have ms : Measurable fun x => ‖partialS u x‖ₑ ^ P :=
    (measurable_enorm.comp hu.continuous_partialS.measurable).pow_const P
  have mt : Measurable fun x => ‖partialT u x‖ₑ ^ P :=
    (measurable_enorm.comp hu.continuous_partialT.measurable).pow_const P
  have hD : eLpNorm (fderiv ℝ v) 1 volume ≤ 5 * (ENNReal.ofReal C₀ *
      (∫⁻ x, ‖u x‖ₑ ^ P ∂cylMeasure + ∫⁻ x, ‖partialS u x‖ₑ ^ P ∂cylMeasure +
        ∫⁻ x, ‖partialT u x‖ₑ ^ P ∂cylMeasure)) := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← setLIntegral_eq_of_support_subset hsupp]
    calc ∫⁻ x in univ ×ˢ Ico (-2 : ℝ) 3, ‖fderiv ℝ v x‖ₑ
        ≤ ∫⁻ x in univ ×ˢ Ico (-2 : ℝ) 3, H x := lintegral_mono hpt
      _ ≤ 5 * ∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, H x := ips_five H hper
      _ = _ := by
        congr 1
        simp only [hH]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right _ mt,
          lintegral_add_right _ ms]
        rfl
  calc ∫⁻ x, ‖u x‖ₑ ^ (2 * P) ∂cylMeasure
      ≤ eLpNorm v (2 : ℝ≥0) volume ^ (2 : ℝ) := hL.trans hL2.le
    _ ≤ ((K : ℝ≥0∞) * eLpNorm (fderiv ℝ v) 1 volume) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hGNS (by norm_num)
    _ ≤ ((K : ℝ≥0∞) * (5 * (ENNReal.ofReal C₀ *
      (∫⁻ x, ‖u x‖ₑ ^ P ∂cylMeasure + ∫⁻ x, ‖partialS u x‖ₑ ^ P ∂cylMeasure +
        ∫⁻ x, ‖partialT u x‖ₑ ^ P ∂cylMeasure)))) ^ (2 : ℝ) := by
        gcongr
    _ = _ := by
        congr 1
        rw [ENNReal.coe_mul, ENNReal.coe_mul]
        simp only [ENNReal.ofReal, C₀]
        push_cast
        ring


lemma ips_pow {f : ℝ × ℝ → Vec n} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) :
    ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂cylMeasure = eLpNorm f p cylMeasure ^ p.toReal := by
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, ← ENNReal.rpow_mul, one_div,
    inv_mul_cancel₀ hP.ne', ENNReal.rpow_one]

theorem ips_sobolev (n : ℕ) (p : ℝ≥0∞) (hp : 1 < p) (hp' : p ≠ ⊤) :
    ∃ C : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      eLpNorm u (2 * p) cylMeasure ≤ C * w1pNorm p u := by
  set P := p.toReal with hPdef
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hP1 : 1 < P := by
    have := ENNReal.toReal_strict_mono hp' hp
    simpa [hPdef] using this
  have hP0 : 0 < P := by linarith
  obtain ⟨B, hB⟩ := ips_main (n := n) P hP1
  refine ⟨(3 * B) ^ (1 / P), fun u hu => ?_⟩
  have h2p0 : 2 * p ≠ 0 := mul_ne_zero two_ne_zero hp0
  have h2pt : 2 * p ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hp'
  have h2P : (2 * p).toReal = 2 * P := by rw [ENNReal.toReal_mul]; simp [hPdef]
  set N := w1pNorm p u
  have hI : ∫⁻ x, ‖u x‖ₑ ^ P ∂cylMeasure + ∫⁻ x, ‖partialS u x‖ₑ ^ P ∂cylMeasure +
      ∫⁻ x, ‖partialT u x‖ₑ ^ P ∂cylMeasure ≤ 3 * N ^ P := by
    rw [hPdef, ips_pow hp0 hp', ips_pow hp0 hp', ips_pow hp0 hp']
    have e1 : eLpNorm u p cylMeasure ≤ N := by
      simp only [N, w1pNorm]; rw [add_assoc]; exact le_self_add
    have e2 : eLpNorm (partialS u) p cylMeasure ≤ N := by
      simp only [N, w1pNorm]; exact le_add_right le_add_self
    have e3 : eLpNorm (partialT u) p cylMeasure ≤ N := by
      simp only [N, w1pNorm]; exact le_add_self
    have k1 := ENNReal.rpow_le_rpow e1 hP0.le
    have k2 := ENNReal.rpow_le_rpow e2 hP0.le
    have k3 := ENNReal.rpow_le_rpow e3 hP0.le
    calc _ ≤ N ^ p.toReal + N ^ p.toReal + N ^ p.toReal := by gcongr
      _ = 3 * N ^ p.toReal := by ring
  have hmain : ∫⁻ x, ‖u x‖ₑ ^ (2 * P) ∂cylMeasure ≤ ((B : ℝ≥0∞) * (3 * N ^ P)) ^ (2 : ℝ) :=
    (hB u hu).trans (ENNReal.rpow_le_rpow (by gcongr) (by norm_num))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2p0 h2pt, h2P]
  calc (∫⁻ x, ‖u x‖ₑ ^ (2 * P) ∂cylMeasure) ^ (1 / (2 * P))
      ≤ (((B : ℝ≥0∞) * (3 * N ^ P)) ^ (2 : ℝ)) ^ (1 / (2 * P)) :=
        ENNReal.rpow_le_rpow hmain (by positivity)
    _ = ((3 * B : ℝ≥0) : ℝ≥0∞) ^ (1 / P) * N := by
        rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / (2 * P)) = 1 / P by field_simp,
          show (B : ℝ≥0∞) * (3 * N ^ P) = ((3 * B : ℝ≥0) : ℝ≥0∞) * N ^ P by push_cast; ring,
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          show P * (1 / P) = 1 by field_simp, ENNReal.rpow_one]
    _ = _ := by
        rw [ENNReal.coe_rpow_of_nonneg _ (by positivity)]

end

end CauchyRiemannIndex

-- ===== Scratch/IPSobSol.lean =====
open MeasureTheory
open scoped ENNReal NNReal

open CauchyRiemannIndex in
theorem solution (n : ℕ) (p : ℝ≥0∞) (hp : 1 < p) (hp' : p ≠ ⊤) :
    ∃ C : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      eLpNorm u (2 * p) cylMeasure ≤ C * w1pNorm p u :=
  ips_sobolev n p hp hp'
