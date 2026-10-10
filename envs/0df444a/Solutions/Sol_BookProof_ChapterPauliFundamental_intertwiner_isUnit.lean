-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.intertwiner_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:30.759082+00:00
-- url     : https://prove2.me/submissions/bb301f18-c8e6-49a7-8b4e-411de09be076

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.intertwiner_isUnit
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Theorems.Thm_BookProof_ChapterPauliFundamental_G_span
import Definitions.Def_ChapterGammaCommutant
import Definitions.Def_ChapterA3
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution {S : M4} (hS0 : S ≠ 0) (hSint : ∀ μ, A μ * S = S * mgamma μ) :
    IsUnit S.det := by

  by_contra hdet
  have hdet0 : S.det = 0 := by
    by_contra h
    exact hdet (isUnit_iff_ne_zero.mpr h)
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0
  -- the kernel of `S`
  let K : Submodule ℂ (Fin 4 → ℂ) :=
    { carrier := {w | S *ᵥ w = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        rw [Matrix.mulVec_add, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at *
        rw [Matrix.mulVec_smul, ha, smul_zero] }
  have hmemK : ∀ w : Fin 4 → ℂ, w ∈ K ↔ S *ᵥ w = 0 := fun w => Iff.rfl
  have hgamma : ∀ (μ : Fin 4) (w : Fin 4 → ℂ), w ∈ K → mgamma μ *ᵥ w ∈ K := by
    intro μ w hw
    rw [hmemK] at hw ⊢
    rw [Matrix.mulVec_mulVec, ← hSint μ, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  have hgp : ∀ (l : List (Fin 4)) (w : Fin 4 → ℂ), w ∈ K → gp mgamma l *ᵥ w ∈ K := by
    intro l
    induction l with
    | nil => intro w hw; simpa [gp] using hw
    | cons a t ih =>
        intro w hw
        have hstep : gp mgamma (a :: t) *ᵥ w = mgamma a *ᵥ (gp mgamma t *ᵥ w) := by
          change (mgamma a * gp mgamma t) *ᵥ w = _
          rw [Matrix.mulVec_mulVec]
        rw [hstep]
        exact hgamma a _ (ih w hw)
  have hGK : ∀ (T : Finset (Fin 4)) (w : Fin 4 → ℂ), w ∈ K → G T *ᵥ w ∈ K :=
    fun T w hw => hgp (sel T) w hw
  -- hence the kernel is invariant under every matrix
  have hall : ∀ (X : M4) (w : Fin 4 → ℂ), w ∈ K → X *ᵥ w ∈ K := by
    intro X w hw
    have hmem : X ∈ Submodule.span ℂ (Set.range G) := by rw [G_span]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
    · rintro Y ⟨T, rfl⟩
      exact hGK T w hw
    · change (0 : M4) *ᵥ w ∈ K
      rw [Matrix.zero_mulVec]
      exact K.zero_mem
    · intro Y Z _ _ hY hZ
      change (Y + Z) *ᵥ w ∈ K
      rw [Matrix.add_mulVec]
      exact K.add_mem hY hZ
    · intro c Y _ hY
      change (c • Y) *ᵥ w ∈ K
      rw [Matrix.smul_mulVec]
      exact K.smul_mem c hY
  -- a nonzero kernel vector makes the kernel everything, so `S = 0`
  have htop : ∀ w : Fin 4 → ℂ, w ∈ K := by
    intro w
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hv0 (funext hcon)
    have hX := hall (Matrix.of fun a b => if b = i then w a / v i else 0) v hv
    have heq : (Matrix.of fun a b => if b = i then w a / v i else 0) *ᵥ v = w := by
      funext a
      rw [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single i]
      · simp only [Matrix.of_apply, if_true]
        field_simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ i) h
    rwa [heq] at hX
  have hzero : S = 0 := by
    ext a b
    have hb : S *ᵥ (fun c => if c = b then (1 : ℂ) else 0) = 0 :=
      htop (fun c => if c = b then 1 else 0)
    have hcol := congrFun hb a
    rw [Matrix.mulVec, dotProduct] at hcol
    rw [Finset.sum_eq_single b] at hcol
    · simpa using hcol
    · intro c _ hc; simp [hc]
    · intro h; exact absurd (Finset.mem_univ b) h
  exact hS0 hzero
