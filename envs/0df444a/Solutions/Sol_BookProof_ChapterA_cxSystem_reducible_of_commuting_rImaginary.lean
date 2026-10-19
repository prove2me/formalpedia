-- Prove2me | solution 1 for BookProof.ChapterA.cxSystem_reducible_of_commuting_rImaginary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:08:28.657189+00:00
-- url     : https://prove2.me/submissions/d652dd11-33bc-4827-be81-c25cb1b59aef

-- Generated from ChapterA1h.lean — solution of BookProof.ChapterA.cxSystem_reducible_of_commuting_rImaginary
import Mathlib
import Definitions.Def_ChapterA1h
import Theorems.Thm_BookProof_ChapterA_rImagCx_sq
import Theorems.Thm_BookProof_ChapterA_rImagCx_commutes
import Theorems.Thm_BookProof_Complexification_Cx_smul_I
import Definitions.Def_Complexification
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification
open BookProof.ChapterA.AntiUnitary

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial W] (M : System ℝ W)
    (h : HasCommutingRImaginary M) : ¬ (cxSystem M).IsIrreducible := by

  intro h_irr
  obtain ⟨J, hJ⟩ := h
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  -- The `+i` eigenspace `W₀ = ker (Jc - i)` of the complexified R-imaginary.
  set T : Cx W →L[ℂ] Cx W := rImagCx J - Complex.I • (1 : Cx W →L[ℂ] Cx W) with hT
  set W₀ : Submodule ℂ (Cx W) := LinearMap.ker T.toLinearMap with hW₀
  -- `W₀` is a subsystem: closed (kernel of a continuous map) and invariant.
  have hW₀_subsystem : (cxSystem M).IsSubsystem W₀ := by
    refine ⟨T.isClosed_ker, ?_⟩
    rintro _ ⟨m, hm, rfl⟩ v hv
    simp only [hW₀, hT, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, sub_eq_zero] at hv ⊢
    rw [rImagCx_commutes hJ hm, hv, map_smul]
  -- `W₀ ≠ ⊥`: it contains the nonzero vector `Jc (ofReal w) + i • ofReal w = ⟨J w, w⟩`.
  have hW₀_ne_bot : W₀ ≠ ⊥ := by
    set v : Cx W := rImagCx J (Cx.ofReal w) + Complex.I • Cx.ofReal w with hv
    have hv_mem : v ∈ W₀ := by
      simp only [hW₀, hT, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, map_add, map_smul, hv, rImagCx_sq hJ]
      rw [smul_sub, smul_smul, Complex.I_mul_I]
      module
    have hv_ne : v ≠ 0 := by
      have him : v.im = w := by simp [hv, rImagCx_apply, Cx.ofReal, Cx.smul_I, map_zero]
      intro hzero
      rw [hzero] at him
      exact hw him.symm
    exact fun hbot => hv_ne (by simpa [hbot] using hv_mem)
  -- `W₀ ≠ ⊤`: else `ofReal w ∈ W₀`, forcing `⟨J w, 0⟩ = ⟨0, w⟩`, so `w = 0`.
  have hW₀_ne_top : W₀ ≠ ⊤ := by
    intro htop
    have hmem : Cx.ofReal w ∈ W₀ := htop ▸ Submodule.mem_top
    simp only [hW₀, hT, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, sub_eq_zero, rImagCx_apply, Cx.ofReal,
      Cx.smul_I, map_zero] at hmem
    have := congr_arg Cx.im hmem
    simp at this
    exact hw this.symm
  exact (hW₀_subsystem |> h_irr W₀).elim hW₀_ne_bot hW₀_ne_top
