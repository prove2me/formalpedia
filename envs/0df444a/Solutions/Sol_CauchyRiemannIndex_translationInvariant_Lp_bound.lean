-- Prove2me | solution 1 for CauchyRiemannIndex.translationInvariant_Lp_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T20:56:53.291322+00:00
-- url     : https://prove2.me/submissions/9317a733-be38-450d-b113-0e2e8d3bfa17

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Theorems.Thm_CauchyRiemannIndex_translationInvariant_slab_L2_bound
import Theorems.Thm_CauchyRiemannIndex_lintegral_rpow_le_slab_L2_add_derivatives
import Theorems.Thm_CauchyRiemannIndex_translationInvariant_derivative_estimate
import Mathlib.Analysis.MeanInequalitiesPow

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

-- ===== Scratch/CRLpParent.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-- A natural number `N ≥ 1` with `A N^{-P} ≤ 1/2`. -/
lemma crlp_exists_nat (A : ℝ≥0∞) (hA : A ≠ ⊤) (P : ℝ) (hP : 1 ≤ P) :
    ∃ N : ℕ, 1 ≤ N ∧ A * (N : ℝ≥0∞) ^ (-P) ≤ 2⁻¹ := by
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hA)
  refine ⟨N + 1, by omega, ?_⟩
  set M : ℝ≥0∞ := ((N + 1 : ℕ) : ℝ≥0∞) with hM
  have h1 : (1 : ℝ≥0∞) ≤ M := by rw [hM]; exact_mod_cast (by omega : 1 ≤ N + 1)
  have hM0 : M ≠ 0 := (lt_of_lt_of_le zero_lt_one h1).ne'
  have hpow : M ≤ M ^ P := by
    calc M = M ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
      _ ≤ M ^ P := ENNReal.rpow_le_rpow_of_exponent_le h1 hP
  have h2A : 2 * A ≤ M := by
    rw [hM]; refine le_trans hN.le ?_; exact_mod_cast (by omega : N ≤ N + 1)
  rw [ENNReal.rpow_neg]
  calc A * (M ^ P)⁻¹ ≤ A * M⁻¹ := by gcongr
    _ ≤ 2⁻¹ * M * M⁻¹ := by
        gcongr
        calc A = 2⁻¹ * (2 * A) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
          _ ≤ 2⁻¹ * M := by gcongr
    _ ≤ 2⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hM0 (by rw [hM]; exact ENNReal.natCast_ne_top _),
          mul_one]

lemma crlp_eLpNorm_rpow {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (g : ℝ × ℝ → Vec n) :
    eLpNorm g p cylMeasure ^ p.toReal = ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂cylMeasure := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, one_div,
    ENNReal.rpow_inv_rpow (ENNReal.toReal_ne_zero.mpr ⟨hp0, hpt⟩)]

theorem crlp_main (n : ℕ) (p : ℝ≥0∞) (hp : 2 ≤ p) (hp' : p ≠ ⊤)
    (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf) :
    ∃ c : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      eLpNorm u p cylMeasure ≤ c * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) p cylMeasure := by
  set P := p.toReal with hPdef
  have hP2 : 2 ≤ P := by
    have := ENNReal.toReal_mono hp' hp
    simpa using this
  have hP0 : 0 < P := by linarith
  have hp1 : (1 : ℝ≥0∞) < p := lt_of_lt_of_le (by norm_num) hp
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp1).ne'
  haveI : Fact (1 ≤ p) := ⟨hp1.le⟩
  obtain ⟨K, hK⟩ := translationInvariant_slab_L2_bound n P hP2 Sinf hS hnd
  obtain ⟨c, hc⟩ := translationInvariant_derivative_estimate n p hp1 hp' Sinf hS.1 hS.2.1
  set A : ℝ≥0∞ := 3 ^ (P - 1) * (2 * (2 ^ (P - 1) * (c : ℝ≥0∞) ^ P)) with hA
  have hAtop : A ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp))
      (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp))
        (ENNReal.rpow_ne_top_of_nonneg hP0.le (by simp))))
  obtain ⟨N, hN1, hN⟩ := crlp_exists_nat A hAtop P (by linarith)
  set ε : ℝ≥0∞ := A * (N : ℝ≥0∞) ^ (-P) with hε
  set M : ℝ≥0∞ := 3 ^ (P - 1) * ((N : ℝ≥0∞) ^ (P - 1) * K) + ε with hMdef
  have hMtop : M ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp))
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)) (by simp)),
      ne_top_of_le_ne_top (by simp) hN⟩
  have h2Mtop : (2 * M) ^ (1 / P) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.mul_ne_top (by simp) hMtop)
  refine ⟨((2 * M) ^ (1 / P)).toNNReal, fun u hu => ?_⟩
  rw [ENNReal.coe_toNNReal h2Mtop]
  set f := crOp (fun x : ℝ × ℝ => Sinf x.2) u with hf
  set X := ∫⁻ x, ‖u x‖ₑ ^ P ∂cylMeasure with hXdef
  set F := ∫⁻ x, ‖f x‖ₑ ^ P ∂cylMeasure with hFdef
  have hXe : eLpNorm u p cylMeasure ^ P = X := crlp_eLpNorm_rpow hp0 hp' u
  have hFe : eLpNorm f p cylMeasure ^ P = F := crlp_eLpNorm_rpow hp0 hp' f
  have hXtop : X ≠ ⊤ := by
    rw [← hXe]
    exact ENNReal.rpow_ne_top_of_nonneg hP0.le (hu.memLp (p := p)).eLpNorm_lt_top.ne
  -- the slab term
  have hslab : ∫⁻ s : ℝ, (∫⁻ x in Set.Icc s (s + 1 / (N : ℝ)) ×ˢ Set.Ico (0 : ℝ) 1,
      ‖u x‖ₑ ^ (2 : ℝ)) ^ (P / 2) ≤ K * F := by
    refine le_trans (lintegral_mono fun s => ?_) (hK u hu)
    refine ENNReal.rpow_le_rpow (lintegral_mono_set ?_) (by positivity)
    refine Set.prod_mono (Set.Icc_subset_Icc le_rfl ?_) le_rfl
    have : (1 : ℝ) / N ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hN1)]; exact_mod_cast hN1
    linarith
  -- the derivative terms
  have hw := hc u hu
  have hDgen : ∀ g : ℝ × ℝ → Vec n, eLpNorm g p cylMeasure ≤ w1pNorm p u →
      ∫⁻ x, ‖g x‖ₑ ^ P ∂cylMeasure ≤ 2 ^ (P - 1) * ((c : ℝ≥0∞) ^ P * F + (c : ℝ≥0∞) ^ P * X) := by
    intro g hg
    rw [← crlp_eLpNorm_rpow hp0 hp' g]
    calc eLpNorm g p cylMeasure ^ P
        ≤ ((c : ℝ≥0∞) * eLpNorm f p cylMeasure + (c : ℝ≥0∞) * eLpNorm u p cylMeasure) ^ P :=
          ENNReal.rpow_le_rpow (hg.trans hw) hP0.le
      _ ≤ 2 ^ (P - 1) * (((c : ℝ≥0∞) * eLpNorm f p cylMeasure) ^ P +
            ((c : ℝ≥0∞) * eLpNorm u p cylMeasure) ^ P) :=
          ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by linarith)
      _ = 2 ^ (P - 1) * ((c : ℝ≥0∞) ^ P * F + (c : ℝ≥0∞) ^ P * X) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hP0.le, ENNReal.mul_rpow_of_nonneg _ _ hP0.le,
            hFe, hXe]
  have hDs := hDgen (partialS u) (by
    unfold w1pNorm; exact le_trans le_add_self (le_add_right le_rfl))
  have hDt := hDgen (partialT u) (by unfold w1pNorm; exact le_add_self)
  have hCbox := lintegral_rpow_le_slab_L2_add_derivatives n P hP2 N hN1 u
    (hu.1.of_le (by exact_mod_cast le_top))
  have hmain : X ≤ M * F + ε * X := by
    refine le_trans hCbox ?_
    calc (3 : ℝ≥0∞) ^ (P - 1) * ((N : ℝ≥0∞) ^ (P - 1) *
            (∫⁻ s : ℝ, (∫⁻ x in Set.Icc s (s + 1 / (N : ℝ)) ×ˢ Set.Ico (0 : ℝ) 1,
              ‖u x‖ₑ ^ (2 : ℝ)) ^ (P / 2)) +
          (N : ℝ≥0∞) ^ (-P) * (∫⁻ x, ‖partialS u x‖ₑ ^ P ∂cylMeasure +
            ∫⁻ x, ‖partialT u x‖ₑ ^ P ∂cylMeasure))
        ≤ (3 : ℝ≥0∞) ^ (P - 1) * ((N : ℝ≥0∞) ^ (P - 1) * (K * F) +
          (N : ℝ≥0∞) ^ (-P) * (2 ^ (P - 1) * ((c : ℝ≥0∞) ^ P * F + (c : ℝ≥0∞) ^ P * X) +
            2 ^ (P - 1) * ((c : ℝ≥0∞) ^ P * F + (c : ℝ≥0∞) ^ P * X))) := by
          gcongr
          all_goals first | exact hslab | exact add_le_add hDs hDt
      _ = M * F + ε * X := by
          rw [hMdef, hε, hA]
          ring_nf
  have hhalf : X ≤ M * F + 2⁻¹ * X := le_trans hmain (by gcongr)
  have hX2 : 2⁻¹ * X ≤ M * F := by
    have hne : 2⁻¹ * X ≠ ⊤ := ENNReal.mul_ne_top (by simp) hXtop
    refine ENNReal.le_of_add_le_add_right hne ?_
    calc 2⁻¹ * X + 2⁻¹ * X = X := by
          rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
      _ ≤ M * F + 2⁻¹ * X := hhalf
  have hXF : X ≤ 2 * M * F := by
    calc X = 2 * (2⁻¹ * X) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
      _ ≤ 2 * (M * F) := by gcongr
      _ = 2 * M * F := (mul_assoc _ _ _).symm
  -- take `P`-th roots
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp', eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp']
  rw [← hPdef, ← hXdef, ← hFdef, ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  exact ENNReal.rpow_le_rpow hXF (by positivity)

end

end CauchyRiemannIndex

open CauchyRiemannIndex in
theorem solution (n : ℕ) (p : ENNReal) (hp : 2 ≤ p) (hp' : p ≠ ⊤)
    (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf) :
    ∃ c : NNReal, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      MeasureTheory.eLpNorm u p cylMeasure ≤
        c * MeasureTheory.eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) p cylMeasure :=
  crlp_main n p hp hp' Sinf hS hnd
