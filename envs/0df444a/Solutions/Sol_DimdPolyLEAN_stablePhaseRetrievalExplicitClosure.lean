-- Prove2me | solution 1 for DimdPolyLEAN.stablePhaseRetrievalExplicitClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:01:13.553024+00:00
-- url     : https://prove2.me/submissions/bec592cd-f7da-4586-bd56-5fc26b394d37

module
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Auxiliary
public import Theorems.Thm_DimdPolyLEAN_stablePhaseRetrievalExplicitRange
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open scoped BigOperators
noncomputable section
namespace DimdPolyLEAN
private theorem explicitGaussianL2DistanceSq_nonneg
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ) :
    0 ≤ explicitGaussianL2DistanceSq P Q :=
  MeasureTheory.integral_nonneg fun _ => sq_nonneg _
private theorem explicitModulusDistanceSq_nonneg
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ) :
    0 ≤ explicitModulusDistanceSq P Q :=
  MeasureTheory.integral_nonneg fun _ => sq_nonneg _
private theorem sqrt_integral_norm_sq_eq_lpNorm
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (F : (Fin d -> ℂ) -> E)
    (hF : MeasureTheory.AEStronglyMeasurable F (explicitGamma d)) :
    Real.sqrt (∫ z, ‖F z‖ ^ 2 ∂ explicitGamma d) =
      MeasureTheory.lpNorm F 2 (explicitGamma d) := by
  have htwo : (2 : NNReal) ≠ 0 := by norm_num
  have hlp := MeasureTheory.lpNorm_nnreal_eq_integral_norm_rpow
    (μ := explicitGamma d) (p := (2 : NNReal)) (f := F) htwo hF
  change
    Real.sqrt (∫ z, ‖F z‖ ^ 2 ∂ explicitGamma d) =
      MeasureTheory.lpNorm F (↑(2 : NNReal)) (explicitGamma d)
  rw [hlp]
  change
    Real.sqrt (∫ z, ‖F z‖ ^ 2 ∂ explicitGamma d) =
      (∫ z, ‖F z‖ ^ (2 : ℝ) ∂ explicitGamma d) ^ ((2 : ℝ)⁻¹)
  rw [show (∫ z, ‖F z‖ ^ (2 : ℝ) ∂ explicitGamma d) =
      ∫ z, ‖F z‖ ^ 2 ∂ explicitGamma d by
    simp_all]
  rw [Real.sqrt_eq_rpow]
  norm_num
private theorem sqrt_explicitGaussianL2DistanceSq_eq_lpNorm
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ)
    (hPQ : MeasureTheory.AEStronglyMeasurable (fun z => P z - Q z)
      (explicitGamma d)) :
    Real.sqrt (explicitGaussianL2DistanceSq P Q) =
      MeasureTheory.lpNorm (fun z => P z - Q z) 2 (explicitGamma d) := by
  simpa [explicitGaussianL2DistanceSq] using
    sqrt_integral_norm_sq_eq_lpNorm (d := d) (fun z => P z - Q z) hPQ
private theorem sqrt_explicitModulusDistanceSq_eq_lpNorm
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ)
    (hPQ : MeasureTheory.AEStronglyMeasurable
      (fun z => ‖P z‖ - ‖Q z‖) (explicitGamma d)) :
    Real.sqrt (explicitModulusDistanceSq P Q) =
      MeasureTheory.lpNorm (fun z => ‖P z‖ - ‖Q z‖) 2
        (explicitGamma d) := by
  simpa [explicitModulusDistanceSq, Real.norm_eq_abs, sq_abs] using
    sqrt_integral_norm_sq_eq_lpNorm (d := d)
      (fun z => ‖P z‖ - ‖Q z‖) hPQ
private theorem memLp_of_explicitHermitePoly
    {d : ℕ} (hd : 0 < d) {κ : Fin d -> ℕ} {Q : (Fin d -> ℂ) -> ℂ}
    (hQ : Q ∈ Set.range (explicitEvalPkappa κ)) :
    MeasureTheory.MemLp Q 2 (explicitGamma d) := by
  rcases hQ with ⟨F, rfl⟩
  exact memLp_two_evalPkappa hd κ F
private theorem explicitClosure_subset_explicitSequentialClosure
    {d : ℕ} (κ : Fin d -> ℕ) :
    explicitClosureOfHermitePolys κ ⊆ explicitSequentialClosureOfHermitePolys κ := by
  classical
  intro Q hQ
  rcases hQ with ⟨hQ_mem, hQ_closure⟩
  refine ⟨hQ_mem, ?_⟩
  rw [mem_closure_iff_seq_limit] at hQ_closure
  rcases hQ_closure with ⟨fn, hfn_mem, hfn_lim⟩
  choose Qn hQn_poly hQn_tail using hfn_mem
  choose hQn_mem hQn_toLp using fun n => hQn_tail n
  refine ⟨Qn, hQn_poly, ?_⟩
  have hdist :
      Filter.Tendsto (fun n => dist (fn n) (hQ_mem.toLp Q))
        Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_iff_dist_tendsto_zero.mp hfn_lim
  have hsqrt :
      ∀ n, Real.sqrt (explicitGaussianL2DistanceSq (Qn n) Q) =
        dist (fn n) (hQ_mem.toLp Q) := by
    intro n
    rw [← hQn_toLp n, MeasureTheory.Lp.dist_def]
    have hsub_mem : MeasureTheory.MemLp (fun z => Qn n z - Q z) 2 (explicitGamma d) :=
      (hQn_mem n).sub hQ_mem
    have hae :
        (⇑((hQn_mem n).toLp (Qn n)) - ⇑(hQ_mem.toLp Q) : (Fin d -> ℂ) -> ℂ)
          =ᵐ[explicitGamma d] fun z => Qn n z - Q z :=
      ((hQn_mem n).coeFn_toLp.sub hQ_mem.coeFn_toLp)
    have heLp :
        MeasureTheory.eLpNorm
            (⇑((hQn_mem n).toLp (Qn n)) - ⇑(hQ_mem.toLp Q)) 2 (explicitGamma d) =
          MeasureTheory.eLpNorm (fun z => Qn n z - Q z) 2 (explicitGamma d) :=
      MeasureTheory.eLpNorm_congr_ae hae
    rw [sqrt_explicitGaussianL2DistanceSq_eq_lpNorm (Qn n) Q hsub_mem.aestronglyMeasurable,
      ← MeasureTheory.toReal_eLpNorm hsub_mem.aestronglyMeasurable, heLp]
  have hsqrt_tendsto :
      Filter.Tendsto
        (fun n => Real.sqrt (explicitGaussianL2DistanceSq (Qn n) Q))
        Filter.atTop (nhds (0 : ℝ)) := by simpa [hsqrt] using hdist
  have hsq :
      (fun n => explicitGaussianL2DistanceSq (Qn n) Q) =
        fun n => (Real.sqrt (explicitGaussianL2DistanceSq (Qn n) Q)) ^ 2 :=
    funext fun n => (Real.sq_sqrt (explicitGaussianL2DistanceSq_nonneg (Qn n) Q)).symm
  rw [hsq]
  simpa using hsqrt_tendsto.pow 2
private theorem explicitPhaseOptimized_bound_of_l2_closure
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (P Q : (Fin d -> ℂ) -> ℂ) (C_P : ℝ)
    (hC_P_pos : 0 < C_P)
    (hP_mem : MeasureTheory.MemLp P 2 (explicitGamma d))
    (hQ_mem : MeasureTheory.MemLp Q 2 (explicitGamma d))
    (Qn : ℕ -> (Fin d -> ℂ) -> ℂ)
    (hQn_poly : ∀ n, Qn n ∈ Set.range (explicitEvalPkappa κ))
    (hQn_lim :
      Filter.Tendsto
        (fun n => explicitGaussianL2DistanceSq (Qn n) Q)
        Filter.atTop (nhds (0 : ℝ)))
    (hfinite :
      ∀ n, ∃ θ : ℂ, ‖θ‖ = 1 ∧
        explicitGaussianL2DistanceSq P (fun z => θ * Qn n z) ≤
          C_P ^ 2 * explicitModulusDistanceSq P (Qn n)) :
    explicitPhaseOptimizedDistanceSq P Q ≤
      C_P ^ 2 * explicitModulusDistanceSq P Q := by
  let δ : ℕ -> ℝ := fun n => Real.sqrt (explicitGaussianL2DistanceSq (Qn n) Q)
  let M : ℝ := explicitModulusDistanceSq P Q
  have hM_nonneg : 0 ≤ M := explicitModulusDistanceSq_nonneg P Q
  have hδ_tendsto : Filter.Tendsto δ Filter.atTop (nhds (0 : ℝ)) := by simpa [δ] using hQn_lim.sqrt
  have hbound_n :
      ∀ n,
        explicitPhaseOptimizedDistanceSq P Q ≤
          (C_P * (Real.sqrt M + δ n) + δ n) ^ 2 := by
    intro n
    rcases hfinite n with ⟨θ, hθ, hθ_bound⟩
    have hQn_mem : MeasureTheory.MemLp (Qn n) 2 (explicitGamma d) :=
      memLp_of_explicitHermitePoly hd (hQn_poly n)
    have hθQ_mem : MeasureTheory.MemLp (fun z => θ * Q z) 2 (explicitGamma d) := by
      refine MeasureTheory.MemLp.ae_eq ?_ (hQ_mem.const_smul θ)
      filter_upwards with z
      simp only [Pi.smul_apply, smul_eq_mul]
    have hθQn_mem :
        MeasureTheory.MemLp (fun z => θ * Qn n z) 2 (explicitGamma d) := by
      refine MeasureTheory.MemLp.ae_eq ?_ (hQn_mem.const_smul θ)
      filter_upwards with z
      simp only [Pi.smul_apply, smul_eq_mul]
    have hPQθ_mem : MeasureTheory.MemLp (fun z => P z - θ * Q z) 2
        (explicitGamma d) :=
      hP_mem.sub hθQ_mem
    have hPQnθ_mem : MeasureTheory.MemLp (fun z => P z - θ * Qn n z) 2
        (explicitGamma d) :=
      hP_mem.sub hθQn_mem
    have hQnQ_mem : MeasureTheory.MemLp (fun z => Qn n z - Q z) 2
        (explicitGamma d) :=
      hQn_mem.sub hQ_mem
    have hphase_tri :
        Real.sqrt (explicitGaussianL2DistanceSq P (fun z => θ * Q z)) ≤
          Real.sqrt (explicitGaussianL2DistanceSq P (fun z => θ * Qn n z)) +
            δ n := by
      rw [sqrt_explicitGaussianL2DistanceSq_eq_lpNorm P (fun z => θ * Q z)
          hPQθ_mem.aestronglyMeasurable,
        sqrt_explicitGaussianL2DistanceSq_eq_lpNorm P (fun z => θ * Qn n z)
          hPQnθ_mem.aestronglyMeasurable]
      have hdecomp :
          (fun z => P z - θ * Q z) =
            fun z => (P z - θ * Qn n z) + θ * (Qn n z - Q z) := by
        funext z
        ring
      rw [hdecomp]
      have htri :=
        MeasureTheory.lpNorm_add_le
          (p := (2 : ENNReal))
          (μ := explicitGamma d)
          (f := fun z => P z - θ * Qn n z)
          (g := fun z => θ * (Qn n z - Q z))
          hPQnθ_mem (by norm_num)
      have hscale :
          MeasureTheory.lpNorm (fun z => θ * (Qn n z - Q z)) 2
              (explicitGamma d) =
            MeasureTheory.lpNorm (fun z => Qn n z - Q z) 2
              (explicitGamma d) := by
        rw [show (fun z => θ * (Qn n z - Q z)) =
            θ • (fun z => Qn n z - Q z) by rfl]
        rw [MeasureTheory.lpNorm_const_smul]
        simp [hθ]
      rw [hscale] at htri
      have hδ_eq :
          MeasureTheory.lpNorm (fun z => Qn n z - Q z) 2 (explicitGamma d) =
            δ n := by
              rw [← sqrt_explicitGaussianL2DistanceSq_eq_lpNorm (Qn n) Q
                hQnQ_mem.aestronglyMeasurable]
      rw [hδ_eq] at htri
      rw [show (fun z => P z - θ * Qn n z + θ * (Qn n z - Q z)) =
          (fun z => P z - θ * Qn n z) + fun z => θ * (Qn n z - Q z) from rfl]
      exact htri
    have hfinite_sqrt :
        Real.sqrt (explicitGaussianL2DistanceSq P (fun z => θ * Qn n z)) ≤
          C_P * Real.sqrt (explicitModulusDistanceSq P (Qn n)) := by
      have hsqrt := Real.sqrt_le_sqrt hθ_bound
      have hsimp :
          Real.sqrt (C_P ^ 2 * explicitModulusDistanceSq P (Qn n)) =
            C_P * Real.sqrt (explicitModulusDistanceSq P (Qn n)) := by
        rw [Real.sqrt_mul (sq_nonneg C_P), Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hC_P_pos)]
      simpa [hsimp] using hsqrt
    have hmod_tri :
        Real.sqrt (explicitModulusDistanceSq P (Qn n)) ≤ Real.sqrt M + δ n := by
      have hmodQ_mem :
          MeasureTheory.MemLp (fun z => ‖P z‖ - ‖Q z‖) 2
            (explicitGamma d) :=
        hP_mem.norm.sub hQ_mem.norm
      have hmodQn_mem :
          MeasureTheory.MemLp (fun z => ‖P z‖ - ‖Qn n z‖) 2
            (explicitGamma d) :=
        hP_mem.norm.sub hQn_mem.norm
      have hnormdiff_mem :
          MeasureTheory.MemLp (fun z => ‖Q z‖ - ‖Qn n z‖) 2
            (explicitGamma d) :=
        hQ_mem.norm.sub hQn_mem.norm
      rw [sqrt_explicitModulusDistanceSq_eq_lpNorm P (Qn n) hmodQn_mem.aestronglyMeasurable,
        sqrt_explicitModulusDistanceSq_eq_lpNorm P Q hmodQ_mem.aestronglyMeasurable]
      change
        MeasureTheory.lpNorm (fun z => ‖P z‖ - ‖Qn n z‖) 2 (explicitGamma d) ≤
          MeasureTheory.lpNorm (fun z => ‖P z‖ - ‖Q z‖) 2 (explicitGamma d) +
            δ n
      have hdecomp :
          (fun z => ‖P z‖ - ‖Qn n z‖) =
            fun z => (‖P z‖ - ‖Q z‖) + (‖Q z‖ - ‖Qn n z‖) := by
        simp_all
      rw [hdecomp]
      have htri :=
        MeasureTheory.lpNorm_add_le
          (p := (2 : ENNReal))
          (μ := explicitGamma d)
          (f := fun z => ‖P z‖ - ‖Q z‖)
          (g := fun z => ‖Q z‖ - ‖Qn n z‖)
          hmodQ_mem (by norm_num)
      have hsecond :
          MeasureTheory.lpNorm (fun z => ‖Q z‖ - ‖Qn n z‖) 2
              (explicitGamma d) ≤
            MeasureTheory.lpNorm (fun z => Qn n z - Q z) 2 (explicitGamma d) := by
        calc
          MeasureTheory.lpNorm (fun z => ‖Q z‖ - ‖Qn n z‖) 2 (explicitGamma d)
              ≤ MeasureTheory.lpNorm (fun z => ‖Qn n z - Q z‖) 2
                  (explicitGamma d) := by
                refine MeasureTheory.lpNorm_mono_real hQnQ_mem.norm ?_
                intro z
                have h := abs_norm_sub_norm_le (Q z) (Qn n z)
                simpa [Real.norm_eq_abs, norm_sub_rev] using h
          _ = MeasureTheory.lpNorm (fun z => Qn n z - Q z) 2
                (explicitGamma d) := by rw [MeasureTheory.lpNorm_norm hQnQ_mem.aestronglyMeasurable]
      have hδ_eq :
          MeasureTheory.lpNorm (fun z => Qn n z - Q z) 2 (explicitGamma d) =
            δ n := by
              rw [← sqrt_explicitGaussianL2DistanceSq_eq_lpNorm (Qn n) Q
                hQnQ_mem.aestronglyMeasurable]
      rw [hδ_eq] at hsecond
      exact htri.trans (add_le_add_right hsecond _)
    have hsqrt_total :
        Real.sqrt (explicitGaussianL2DistanceSq P (fun z => θ * Q z)) ≤
          C_P * (Real.sqrt M + δ n) + δ n := by
      calc
        Real.sqrt (explicitGaussianL2DistanceSq P (fun z => θ * Q z))
            ≤ Real.sqrt (explicitGaussianL2DistanceSq P (fun z => θ * Qn n z)) +
                δ n :=
              hphase_tri
        _ ≤ C_P * Real.sqrt (explicitModulusDistanceSq P (Qn n)) + δ n :=
              add_le_add hfinite_sqrt le_rfl
        _ ≤ C_P * (Real.sqrt M + δ n) + δ n :=
              add_le_add (mul_le_mul_of_nonneg_left hmod_tri (le_of_lt hC_P_pos)) le_rfl
    have hphase_inf :
        explicitPhaseOptimizedDistanceSq P Q ≤
          explicitGaussianL2DistanceSq P (fun z => θ * Q z) := by
      have hbdd :
          BddBelow (Set.range fun θ' : UnitPhase =>
            explicitGaussianL2DistanceSq P (fun z => θ'.1 * Q z)) := by
        refine ⟨0, ?_⟩
        rintro r ⟨θ', rfl⟩
        exact explicitGaussianL2DistanceSq_nonneg P (fun z => θ'.1 * Q z)
      exact csInf_le hbdd ⟨⟨θ, hθ⟩, rfl⟩
    have htarget_sq :
        explicitGaussianL2DistanceSq P (fun z => θ * Q z) ≤
          (C_P * (Real.sqrt M + δ n) + δ n) ^ 2 := by
      let B : ℝ := C_P * (Real.sqrt M + δ n) + δ n
      have hB_nonneg : 0 ≤ B := by
        have hδ_nonneg : 0 ≤ δ n := Real.sqrt_nonneg _
        have hsqrtM_nonneg : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
        dsimp [B]
        nlinarith only [hC_P_pos, hδ_nonneg, hsqrtM_nonneg]
      have hg_nonneg :
          0 ≤ explicitGaussianL2DistanceSq P (fun z => θ * Q z) :=
        explicitGaussianL2DistanceSq_nonneg P (fun z => θ * Q z)
      have habs :
          |Real.sqrt (explicitGaussianL2DistanceSq P (fun z => θ * Q z))| ≤ |B| := by
        simpa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hB_nonneg, B]
          using hsqrt_total
      have hsquares :
          Real.sqrt (explicitGaussianL2DistanceSq P (fun z => θ * Q z)) ^ 2 ≤
            B ^ 2 :=
        (sq_le_sq).2 habs
      simpa [B, Real.sq_sqrt hg_nonneg] using hsquares
    exact hphase_inf.trans htarget_sq
  have hlim_rhs :
      Filter.Tendsto
        (fun n => (C_P * (Real.sqrt M + δ n) + δ n) ^ 2)
        Filter.atTop (nhds (C_P ^ 2 * M)) := by
    have hinner :
        Filter.Tendsto (fun n => C_P * (Real.sqrt M + δ n) + δ n)
          Filter.atTop (nhds (C_P * (Real.sqrt M + 0) + 0)) :=
      ((tendsto_const_nhds.add hδ_tendsto).const_mul C_P).add hδ_tendsto
    have hpow := hinner.pow 2
    convert hpow using 1
    ring_nf
    rw [Real.sq_sqrt hM_nonneg]
  have hconst :
      Filter.Tendsto (fun _ : ℕ => explicitPhaseOptimizedDistanceSq P Q)
        Filter.atTop (nhds (explicitPhaseOptimizedDistanceSq P Q)) :=
    tendsto_const_nhds
  exact le_of_tendsto_of_tendsto hconst hlim_rhs (Filter.Eventually.of_forall hbound_n)
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (P : (Fin d -> ℂ) -> ℂ) (hP : P ∈ Set.range (explicitEvalPkappa κ)) :
    ∃ C_P : ℝ, 0 < C_P ∧
      ∀ Q : (Fin d -> ℂ) -> ℂ, Q ∈ explicitClosureOfHermitePolys κ →
        explicitPhaseOptimizedDistanceSq P Q ≤
          C_P ^ 2 * explicitModulusDistanceSq P Q := by
  rcases stablePhaseRetrievalExplicitRange hd κ P hP with ⟨C_P, hC_P_pos, hfinite⟩
  have hP_mem : MeasureTheory.MemLp P 2 (explicitGamma d) :=
    memLp_of_explicitHermitePoly hd hP
  refine ⟨C_P, hC_P_pos, ?_⟩
  intro Q hQ
  have hQ_seq := explicitClosure_subset_explicitSequentialClosure κ hQ
  rcases hQ_seq with ⟨hQ_mem, Qn, hQn_poly, hQn_lim⟩
  exact explicitPhaseOptimized_bound_of_l2_closure hd κ P Q C_P hC_P_pos hP_mem
    hQ_mem Qn hQn_poly hQn_lim (fun n => by
      rcases hfinite (Qn n) (hQn_poly n) with ⟨θ, hθ, hbound⟩
      exact ⟨θ, hθ, by
        simpa [explicitGaussianL2DistanceSq, explicitModulusDistanceSq] using hbound⟩)
end DimdPolyLEAN
