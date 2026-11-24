-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.hasDerivAt_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:41:38.330784+00:00
-- url     : https://prove2.me/submissions/d4692a5f-368c-4b57-ab44-e8ec65b7c989

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Theorems.Thm_CompanionTheory_D_Upq_Sm_hasDerivAt_integral_cpt
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ex_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_continuous_ex
import Theorems.Thm_CompanionTheory_D_Upq_Sm_contDiff_Lx
import Theorems.Thm_CompanionTheory_D_Upq_Sm_tsupport_Lx
import Theorems.Thm_CompanionTheory_D_Upq_Sm_hasDerivAt_Lx
import Theorems.Thm_CompanionTheory_D_Upq_Sm_isCompact_supp
import Theorems.Thm_CompanionTheory_D_Upq_Sm_continuous_orbit
import Theorems.Thm_CompanionTheory_D_Upq_Sm_apply_integral
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul


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
theorem _root_.solution (h : RepOn G σ) {v : H} (hv : IsSm G σ v) {X : Mat n} (hX : ∀ t, ex X t ∈ G)
    {ψ : Mat n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    HasDerivAt (fun t => σ (ex X t) (∫ g : MG G hG, ψ g.mat • σ g.mat v ∂haar))
      (∫ g : MG G hG, Lx X ψ g.mat • σ g.mat v ∂haar) 0 := by
  have hf : Continuous fun g : MG G hG => σ g.mat v :=
    continuous_orbit h hv (W := []) fun _ h => by simp at h
  have e : ∀ t, σ (ex X t) (∫ g : MG G hG, ψ g.mat • σ g.mat v ∂haar) =
      ∫ g : MG G hG, ψ (ex X (-t) * g.mat) • σ g.mat v ∂haar := fun t => by
    rw [apply_integral _ hψ.continuous hc hf, ← integral_mul_left_eq_self
      (fun g : MG G hG => ψ (ex X (-t) * g.mat) • σ g.mat v) (MG.mk hG (ex X t) (hX t))]
    congr 1
    ext1 g
    rw [MG.mat_mul, MG.mat_mk, ← Matrix.mul_assoc, ← ex_add, neg_add_cancel, ex_zero,
      Matrix.one_mul, h.apply_mul (hX t) g.mem]
  simp_rw [e]
  have hγ : Continuous fun p : ℝ × MG G hG => ex X (-p.1) * p.2.mat :=
    ((continuous_ex X).comp continuous_fst.neg).matrix_mul (MG.continuous_mat.comp continuous_snd)
  let m : ℝ × MG G hG → MG G hG := fun p => MG.mk hG (ex X p.1) (hX _) * p.2
  have hm : Continuous m :=
    (MG.continuous_iff.2 ((continuous_ex X).comp continuous_fst)).mul continuous_snd
  have hK := (isCompact_Icc.prod (isCompact_supp (hG := hG) hc) :
    IsCompact (Icc (-1 : ℝ) 1 ×ˢ _)).image hm
  have hout : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ a : MG G hG,
      a ∉ m '' (Icc (-1 : ℝ) 1 ×ˢ (MG.mat ⁻¹' tsupport ψ)) → ex X (-t) * a.mat ∉ tsupport ψ := by
    intro t ht a ha hs
    refine ha ⟨(t, MG.mk hG (ex X (-t)) (hX _) * a), ⟨ht, hs⟩, MG.ext ?_⟩
    simp only [m, MG.mat_mul, MG.mat_mk]
    rw [← Matrix.mul_assoc, ← ex_add, add_neg_cancel, ex_zero, Matrix.one_mul]
  have := hasDerivAt_integral_cpt (μ := (haar : Measure (MG G hG)))
    (F := fun t g => ψ (ex X (-t) * g.mat) • σ g.mat v)
    (F' := fun t g => Lx X ψ (ex X (-t) * g.mat) • σ g.mat v)
    (fun t => (hψ.continuous.comp (hγ.comp (Continuous.prodMk_right t))).smul hf)
    (((contDiff_Lx X hψ).continuous.comp hγ).smul (hf.comp continuous_snd))
    (fun t a => (hasDerivAt_Lx X a.mat hψ t).smul_const _) hK
    (fun a ha => by
      rw [image_eq_zero_of_notMem_tsupport (hout 0 (by norm_num) a ha), zero_smul])
    (fun t ht a ha => by
      rw [image_eq_zero_of_notMem_tsupport (fun hs => hout t ht a ha (tsupport_Lx X ψ hs)),
        zero_smul])
  simpa [ex_zero] using this
end CompanionTheory.D.Upq.Sm
