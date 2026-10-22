-- Prove2me | solution 1 for BookProof.ChapterSchurIrreducible.spectrum_subsingleton_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:26:34.614773+00:00
-- url     : https://prove2.me/submissions/37e6dfe1-7add-4ece-839c-960a34ae2543

-- Generated from ChapterSchurIrreducible.lean — solution of BookProof.ChapterSchurIrreducible.spectrum_subsingleton_of_irreducible
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Theorems.Thm_BookProof_ChapterSchurIrreducible_isClosed_rangeClosure
import Theorems.Thm_BookProof_ChapterSchurIrreducible_rangeClosure_invariant
import Theorems.Thm_BookProof_ChapterSchurIrreducible_rangeClosure_ne_bot
import Theorems.Thm_BookProof_ChapterSchurIrreducible_rangeClosure_ne_top
import Theorems.Thm_BookProof_ChapterSchurIrreducible_cfc_ne_zero_of_mem_spectrum
import Definitions.Def_ChapterA
open BookProof.ChapterSchurIrreducible



open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System
open BookProof.ChapterA
open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial V] (M : System ℂ V)
    (hirr : M.IsIrreducible) {T : V →L[ℂ] V} (hT : IsSelfAdjoint T) (hcomm : M.Commutes T)
    {a b : ℝ} (ha : a ∈ spectrum ℝ T) (hb : b ∈ spectrum ℝ T) : a = b := by

  by_contra hab
  -- Order the two spectral points.
  set p := min a b with hp_def
  set q := max a b with hq_def
  have hp : p ∈ spectrum ℝ T := by
    rcases min_cases a b with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [hp_def, h] <;> assumption
  have hq : q ∈ spectrum ℝ T := by
    rcases max_cases a b with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [hq_def, h] <;> assumption
  have hpq : p < q := lt_of_le_of_ne (min_le_max) (by
    intro h
    rcases le_total a b with hle | hle
    · rw [hp_def, hq_def, min_eq_left hle, max_eq_right hle] at h; exact hab h
    · rw [hp_def, hq_def, min_eq_right hle, max_eq_left hle] at h; exact hab h.symm)
  set mid : ℝ := (p + q) / 2 with hmid
  have hpmid : p < mid := by rw [hmid]; linarith
  have hmidq : mid < q := by rw [hmid]; linarith
  set f : ℝ → ℝ := fun x => max 0 (mid - x) with hf_def
  set g : ℝ → ℝ := fun x => max 0 (x - mid) with hg_def
  have hfc : Continuous f := continuous_const.max (continuous_const.sub continuous_id)
  have hgc : Continuous g := continuous_const.max (continuous_id.sub continuous_const)
  have hfp : f p ≠ 0 := by
    rw [hf_def]
    simp only [ne_eq, max_eq_left_iff, not_le]
    linarith
  have hgq : g q ≠ 0 := by
    rw [hg_def]
    simp only [ne_eq, max_eq_left_iff, not_le]
    linarith
  set F : V →L[ℂ] V := cfc f T with hF_def
  set G : V →L[ℂ] V := cfc g T with hG_def
  have hF : F ≠ 0 := cfc_ne_zero_of_mem_spectrum hT hfc hp hfp
  have hG : G ≠ 0 := cfc_ne_zero_of_mem_spectrum hT hgc hq hgq
  -- The two functions have disjoint support, so the operators annihilate each other.
  have hGF : G * F = 0 := by
    have hzero : (fun x : ℝ => g x * f x) = fun _ : ℝ => (0 : ℝ) := by
      funext x
      rcases le_total x mid with hx | hx
      · have : g x = 0 := by rw [hg_def]; simp only [max_eq_left_iff]; linarith
        rw [this, zero_mul]
      · have : f x = 0 := by rw [hf_def]; simp only [max_eq_left_iff]; linarith
        rw [this, mul_zero]
    have := cfc_mul g f T (hgc.continuousOn) (hfc.continuousOn)
    rw [hzero] at this
    rw [hG_def, hF_def, ← this, cfc_const (0 : ℝ) T, map_zero]
  -- The closure of the range of `F` is a closed invariant subspace.
  have hsub : M.IsSubsystem (rangeClosure F) := by
    refine ⟨isClosed_rangeClosure F, ?_⟩
    intro m hm w hw
    have hcm : Commute T m := hcomm m hm
    have : Commute (cfc f T) m := hT.commute_cfc (𝕜 := ℝ) hcm f
    exact rangeClosure_invariant (F := F) this hw
  rcases hirr _ hsub with h | h
  · exact rangeClosure_ne_bot hF h
  · exact rangeClosure_ne_top hG hGF h
