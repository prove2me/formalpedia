-- Prove2me | solution 1 for BookProof.Complexification.Cx.realPart_isSubsystem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:54:46.890388+00:00
-- url     : https://prove2.me/submissions/405071be-4c92-4804-8e33-11305e90da0f

import Mathlib
import Definitions.Def_ChapterA1b
import Definitions.Def_ChapterA
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_Complexification
-- Generated from ChapterA1b.lean — theorem BookProof.Complexification.Cx.realPart_isSubsystem
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.Complexification
open BookProof.Complexification


open scoped RealInnerProductSpace
open BookProof.ChapterA


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

variable [CompleteSpace W]
open BookProof.Complexification BookProof.ChapterA in
theorem hbp_cx_cont_re {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] :
    Continuous (Cx.re : Cx W → W) :=
  (LipschitzWith.of_dist_le_mul (K := 1) (fun x y => by simpa [dist_eq_norm] using Cx.norm_re_le (x - y))).continuous

open BookProof.Complexification BookProof.ChapterA in
theorem hbp_cx_cont_im {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] :
    Continuous (Cx.im : Cx W → W) :=
  (LipschitzWith.of_dist_le_mul (K := 1) (fun x y => by simpa [dist_eq_norm] using Cx.norm_im_le (x - y))).continuous

open BookProof.Complexification BookProof.ChapterA in
theorem hbp_cx_cont_ofReal {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] :
    Continuous (Cx.ofReal : W → Cx W) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) (fun x y => ?_)).continuous
  have h : Cx.ofReal x - Cx.ofReal y = Cx.ofReal (x - y) := by ext <;> simp
  have h2 := Cx.norm_sq (Cx.ofReal (x - y))
  simp only [Cx.ofReal_re, Cx.ofReal_im, norm_zero] at h2
  rw [dist_eq_norm, dist_eq_norm, h]
  have : ‖Cx.ofReal (x - y)‖ = ‖x - y‖ := by
    have := norm_nonneg (Cx.ofReal (x - y)); have := norm_nonneg (x - y); nlinarith
  simp [this]

open BookProof.Complexification BookProof.ChapterA in
theorem hbp_cx_complexify_isSubsystem {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [CompleteSpace W] (M : System ℝ W) {Y : Submodule ℝ W}
    (hY : M.IsSubsystem Y) : (cxSystem M).IsSubsystem (Cx.complexify Y) := by
  refine ⟨?_, ?_⟩
  · have : ((Cx.complexify Y : Submodule ℂ (Cx W)) : Set (Cx W)) =
        Cx.re ⁻¹' (Y : Set W) ∩ Cx.im ⁻¹' (Y : Set W) := by
      ext x; simp [Cx.mem_complexify]
    rw [this]
    exact (hY.1.preimage hbp_cx_cont_re).inter (hY.1.preimage hbp_cx_cont_im)
  · rintro m ⟨m', hm', rfl⟩ x hx
    rw [Cx.mem_complexify] at hx ⊢
    simp only [Cx.cxMap_apply]
    exact ⟨hY.2 m' hm' _ hx.1, hY.2 m' hm' _ hx.2⟩

open BookProof.Complexification BookProof.ChapterA in
theorem hbp_cx_realPart_isSubsystem {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [CompleteSpace W] (M : System ℝ W) {X : Submodule ℂ (Cx W)}
    (hX : (cxSystem M).IsSubsystem X) : M.IsSubsystem (Cx.realPart X) := by
  refine ⟨?_, ?_⟩
  · have : ((Cx.realPart X : Submodule ℝ W) : Set W) = Cx.ofReal ⁻¹' (X : Set (Cx W)) := by
      ext w; simp [Cx.mem_realPart]
    rw [this]
    exact hX.1.preimage hbp_cx_cont_ofReal
  · intro m hm w hw
    rw [Cx.mem_realPart] at hw ⊢
    have h := hX.2 (Cx.cxMap m) ⟨m, hm, rfl⟩ _ hw
    have e : Cx.cxMap m (Cx.ofReal w) = Cx.ofReal (m w) := by ext <;> simp
    rwa [e] at h

open BookProof.Complexification BookProof.ChapterA in
theorem hbp_cx_complexify_realPart {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {X : Submodule ℂ (Cx W)} (hX : ∀ x ∈ X, Cx.cxConj x ∈ X) :
    Cx.complexify (Cx.realPart X) = X := by
  ext x
  rw [Cx.mem_complexify, Cx.mem_realPart, Cx.mem_realPart]
  constructor
  · rintro ⟨h1, h2⟩
    have e : x = Cx.ofReal x.re + Complex.I • Cx.ofReal x.im := by ext <;> simp
    rw [e]; exact X.add_mem h1 (X.smul_mem _ h2)
  · intro hx
    have hc := hX x hx
    refine ⟨?_, ?_⟩
    · have e : Cx.ofReal x.re = (1/2 : ℂ) • (x + Cx.cxConj x) := by
        ext <;> simp <;> module
      rw [e]; exact X.smul_mem _ (X.add_mem hx hc)
    · have e : Cx.ofReal x.im = (-Complex.I/2 : ℂ) • (x - Cx.cxConj x) := by
        ext <;> simp <;> module
      rw [e]; exact X.smul_mem _ (X.sub_mem hx hc)

theorem solution (M : System ℝ W) {X : Submodule ℂ (Cx W)}
    (hX : (cxSystem M).IsSubsystem X) : (M).IsSubsystem (BookProof.Complexification.Cx.realPart X) := by
  exact hbp_cx_realPart_isSubsystem M hX

