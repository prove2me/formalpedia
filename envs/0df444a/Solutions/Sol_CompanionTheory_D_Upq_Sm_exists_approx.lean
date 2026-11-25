-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.exists_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:04:33.735797+00:00
-- url     : https://prove2.me/submissions/adc2c7a3-80dc-4132-946f-434a6a34f886

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Theorems.Thm_CompanionTheory_D_Upq_Sm_integral_mem_of_isClosed
import Theorems.Thm_CompanionTheory_D_Upq_Sm_isCompact_supp
import Theorems.Thm_CompanionTheory_D_Upq_Sm_integrable_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_continuous_orbit
import Theorems.Thm_CompanionTheory_D_Upq_Sm_norm_integral_dsW_le
import Theorems.Thm_CompanionTheory_D_Upq_Sm_isSm_of_mem_orbSpan
import Theorems.Thm_CompanionTheory_D_Upq_Sm_apply_mem_orbSpan
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_sub
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
variable {hG : IsMatGroup G}
variable [CompleteSpace H]
namespace CompanionTheory.D.Upq.Sm
theorem _root_.solution (hG : IsMatGroup G) (h : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖)
    {w : H} (hw : IsSm G σ w) (hd : Dense (orbSpan G σ w : Set H)) {x : H} (hx : IsSm G σ x)
    {ι : Type} [Fintype ι] {W : ι → List (Mat n)} (hW : ∀ i, LieW G (W i)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ y ∈ orbSpan G σ w, ∀ i, ‖dsW σ (W i) (x - y)‖ < δ := by
  let J : H → ι → H := fun v i => dsW σ (W i) v
  let S₀ : Submodule ℂ (ι → H) :=
    { carrier := J '' orbSpan G σ w
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, add_mem ha hb, funext fun i => dsW_add h (isSm_of_mem_orbSpan h hw ha)
          (isSm_of_mem_orbSpan h hw hb) (hW i)⟩
      zero_mem' := ⟨0, zero_mem _, funext fun i => by
        have := dsW_smul h (IsSm.zero (G := G) (σ := σ)) 0 (hW i)
        simpa using this⟩
      smul_mem' := by
        rintro c _ ⟨a, ha, rfl⟩
        exact ⟨c • a, Submodule.smul_mem _ c ha, funext fun i =>
          dsW_smul h (isSm_of_mem_orbSpan h hw ha) c (hW i)⟩ }
  let S := S₀.topologicalClosure
  have hS : IsClosed (S : Set (ι → H)) := S₀.isClosed_topologicalClosure
  have hJc : ∀ v, IsSm G σ v → Continuous fun g : MG G hG => J (σ g.mat v) := fun v hv =>
    continuous_pi fun i => continuous_orbit h hv (hW i)
  have key : ∀ φ : Mat n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ g : MG G hG, φ g.mat • J (σ g.mat x) ∂haar ∈ S := by
    intro φ hφ hc
    let C : ℝ := ∑ i, ∫ g : MG G hG, ‖LW (W i) φ g.mat‖ ∂haar
    have hC0 : ∀ i, 0 ≤ ∫ g : MG G hG, ‖LW (W i) φ g.mat‖ ∂haar := fun i =>
      integral_nonneg fun _ => norm_nonneg _
    have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => hC0 i
    rw [← SetLike.mem_coe, ← hS.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 (hd x) (ε / (C + 1)) (by positivity)
    have hys := isSm_of_mem_orbSpan h hw hy
    refine ⟨∫ g : MG G hG, φ g.mat • J (σ g.mat y) ∂haar,
      integral_mem_of_isClosed S hS fun g => ?_, ?_⟩
    · exact S.smul_of_tower_mem _ (S₀.le_topologicalClosure ⟨_, apply_mem_orbSpan h g.mem hy, rfl⟩)
    · rw [dist_eq_norm, ← integral_sub (integrable_smul hφ.continuous hc (hJc x hx))
        (integrable_smul hφ.continuous hc (hJc y hys))]
      have e : (fun g : MG G hG => φ g.mat • J (σ g.mat x) - φ g.mat • J (σ g.mat y)) =
          fun g => φ g.mat • J (σ g.mat (x - y)) := by
        ext g i
        simp only [J, Pi.sub_apply, Pi.smul_apply, map_sub]
        rw [dsW_sub h (hx.apply h g.mem) (hys.apply h g.mem) (hW i), smul_sub]
      rw [e]
      have hle : ‖∫ g : MG G hG, φ g.mat • J (σ g.mat (x - y)) ∂haar‖ ≤ C * ‖x - y‖ := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
        have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => H) i).integral_comp_comm
          (integrable_smul hφ.continuous hc (hJc _ (hx.sub hys)))
        simp only [ContinuousLinearMap.proj_apply, Pi.smul_apply] at this
        rw [← this]
        refine (norm_integral_dsW_le h hiso (hx.sub hys) hφ hc (hW i)).trans ?_
        exact mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i)) (norm_nonneg _)
      rw [dist_eq_norm, lt_div_iff₀ (by positivity)] at hxy
      nlinarith [norm_nonneg (x - y)]
  have hJx : J x ∈ S := by
    rw [← SetLike.mem_coe, ← hS.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    have hc1 : ContinuousAt (fun g : MG G hG => J (σ g.mat x)) 1 := (hJc x hx).continuousAt
    have h1 : J (σ (1 : MG G hG).mat x) = J x := by
      change J (σ 1 x) = J x
      rw [h.map_one]; rfl
    have hnb : {g : MG G hG | dist (J (σ g.mat x)) (J x) < ε / 2} ∈ 𝓝 (1 : MG G hG) := by
      rw [← h1]
      exact Metric.tendsto_nhds.1 hc1 _ (by positivity)
    rw [MG.isClosedEmbedding_mat.isInducing.nhds_eq_comap, mem_comap] at hnb
    obtain ⟨U, hU, hUs⟩ := hnb
    obtain ⟨φ, hφU, hc, hφ, hr, hφ1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hU
    have hφ0 : ∀ g, 0 ≤ φ g := fun g => (hr ⟨g, rfl⟩).1
    have hφ' : Continuous fun g : MG G hG => φ g.mat := hφ.continuous.comp MG.continuous_mat
    have hc' : HasCompactSupport fun g : MG G hG => φ g.mat :=
      HasCompactSupport.intro (isCompact_supp hc) fun g hg => image_eq_zero_of_notMem_tsupport hg
    set c : ℝ := ∫ g : MG G hG, φ g.mat ∂haar with hcdef
    have hcpos : 0 < c := hφ'.integral_pos_of_hasCompactSupport_nonneg_nonzero hc'
      (fun g => hφ0 _) (x := 1) (by rw [hφ1]; exact one_ne_zero)
    refine ⟨c⁻¹ • ∫ g : MG G hG, φ g.mat • J (σ g.mat x) ∂haar,
      S.smul_of_tower_mem _ (key φ hφ hc), ?_⟩
    have e : J x - c⁻¹ • ∫ g : MG G hG, φ g.mat • J (σ g.mat x) ∂haar =
        c⁻¹ • ∫ g : MG G hG, φ g.mat • (J x - J (σ g.mat x)) ∂haar := by
      simp_rw [smul_sub]
      rw [integral_sub (integrable_smul hφ.continuous hc continuous_const)
        (integrable_smul hφ.continuous hc (hJc x hx)), integral_smul_const, smul_sub, smul_smul,
        inv_mul_cancel₀ hcpos.ne', one_smul]
    have hle : ‖∫ g : MG G hG, φ g.mat • (J x - J (σ g.mat x)) ∂haar‖ ≤ c * (ε / 2) := by
      rw [hcdef, ← integral_mul_const]
      refine norm_integral_le_of_norm_le
        ((hφ'.integrable_of_hasCompactSupport hc').mul_const _) (Eventually.of_forall fun g => ?_)
      rw [norm_smul, Real.norm_of_nonneg (hφ0 _)]
      by_cases hg : g.mat ∈ tsupport φ
      · refine mul_le_mul_of_nonneg_left ?_ (hφ0 _)
        have : dist (J (σ g.mat x)) (J x) < ε / 2 := hUs (hφU hg)
        rw [dist_comm, dist_eq_norm] at this
        exact this.le
      · rw [image_eq_zero_of_notMem_tsupport hg, zero_mul, zero_mul]
    rw [dist_eq_norm, e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hcpos.le)]
    calc c⁻¹ * _ ≤ c⁻¹ * (c * (ε / 2)) := mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hcpos.le)
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := Metric.mem_closure_iff.1
    (show J x ∈ closure (S₀ : Set (ι → H)) from hJx) δ hδ
  refine ⟨y, hy, fun i => ?_⟩
  rw [dsW_sub h hx (isSm_of_mem_orbSpan h hw hy) (hW i)]
  rw [dist_eq_norm] at hxy
  exact (norm_le_pi_norm (J x - J y) i).trans_lt hxy
end CompanionTheory.D.Upq.Sm
