-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.isGraphCore_of_esa
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T19:50:12.495562+00:00
-- url     : https://prove2.me/submissions/f3c1247f-5c65-4e46-9cb5-b2d134439142

-- Generated from ChapterScalaronFiberFL.lean — solution of BookProof.ScalaronFiberFL.isGraphCore_of_esa
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterFarisLavineCore
import Theorems.Thm_BookProof_ScalaronFiberFL_norm_sub_I_sq
open BookProof.FarisLavine
open BookProof.QgOuterFockFL
open BookProof.QgOuterFockCoreFL

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (C : Comparison F) (C₀ : Submodule ℂ F) (hle : C₀ ≤ C.dom)
    (P : C₀ →ₗ[ℂ] F) (hext : ∀ p : C₀, C.op ⟨(p : F), hle p.2⟩ = P p)
    (hesa : EssentiallySelfAdjointOn C₀ P) : IsGraphCore C C₀ := by
  classical
  set R : Submodule ℂ F := LinearMap.range (P - Complex.I • C₀.subtype) with hR
  have hperp : Rᗮ = ⊥ := by
    refine Submodule.eq_bot_iff _ |>.mpr ?_
    intro w hw
    refine hesa.2 w ?_
    intro v
    have hmem : (P - Complex.I • C₀.subtype) v ∈ R := ⟨v, rfl⟩
    have h0 : (inner ℂ ((P - Complex.I • C₀.subtype) v) w : ℂ) = 0 := hw _ hmem
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
      inner_sub_left, inner_smul_left] at h0
    have h1 : (inner ℂ (P v) w : ℂ) = (starRingEnd ℂ) Complex.I * inner ℂ (v : F) w := by
      linear_combination h0
    rw [h1]
    simp
  have hdense : Dense (R : Set F) := by
    have htop : R.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.mpr hperp
    rw [← Submodule.dense_iff_topologicalClosure_eq_top] at htop
    exact htop
  refine ⟨hle, ?_⟩
  intro x ε hε
  set y : F := C.op x - Complex.I • (x : F) with hy
  obtain ⟨r, hrball, hrR⟩ := Metric.dense_iff.mp hdense y ε hε
  have hr : ‖r - y‖ < ε := by
    rw [← dist_eq_norm]
    simpa [Metric.mem_ball, dist_comm] using hrball
  obtain ⟨p, hp⟩ := hrR
  set q : C.dom := ⟨(p : F), hle p.2⟩ with hq
  have hval : C.op (q - x) - Complex.I • ((q - x : C.dom) : F) = r - y := by
    rw [map_sub, hy, ← hp]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
      Submodule.coe_sub, hq, hext p, smul_sub]
    abel
  have hkey := BookProof.ScalaronFiberFL.norm_sub_I_sq C.op C.sym (q - x)
  rw [hval] at hkey
  have hcoe : ((q - x : C.dom) : F) = (p : F) - (x : F) := rfl
  refine ⟨q, p.2, ?_, ?_⟩
  · have h2 : ‖((q - x : C.dom) : F)‖ < ε := by
      nlinarith [norm_nonneg ((q - x : C.dom) : F), norm_nonneg (C.op (q - x)),
        norm_nonneg (r - y), hr]
    rwa [hcoe] at h2
  · have h2 : ‖C.op (q - x)‖ < ε := by
      nlinarith [norm_nonneg ((q - x : C.dom) : F), norm_nonneg (C.op (q - x)),
        norm_nonneg (r - y), hr]
    rwa [map_sub] at h2
