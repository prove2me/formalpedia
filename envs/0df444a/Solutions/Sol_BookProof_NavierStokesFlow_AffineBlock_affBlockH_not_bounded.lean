-- Prove2me | solution 1 for BookProof.NavierStokesFlow.AffineBlock.affBlockH_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:38:42.764645+00:00
-- url     : https://prove2.me/submissions/7a16877f-5a36-47b6-b8cc-4e14b354f149

import Mathlib
import Definitions.Def_ChapterNavierStokesAffineBlockEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneResolvent
-- Generated from ChapterNavierStokesAffineBlockEsa.lean — theorem BookProof.NavierStokesFlow.AffineBlock.affBlockH_not_bounded
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber.PairShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineBlock


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber BilinearEsa

variable {J : Type*}
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.AffineFiber BookProof.NavierStokesFlow.IkebeKato
  BookProof.NavierStokesFlow.HermiteFarisLavine BookProof.NavierStokesFlow.ShiftHamiltonian in
theorem h43_coord1 {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) (n : ℕ) :
    ((affH hκ hc (basisState κ c n) : L2I ℕ) : ℕ → ℂ) (n + 1)
      = Complex.I * ((shear c n : ℝ) : ℂ) := by
  have e : ((affH hκ hc (basisState κ c n) : L2I ℕ) : ℕ → ℂ) (n + 1)
      = (affData hκ hc).fst.hFun ((basisState κ c n : L2I ℕ) : ℕ → ℂ) (n + 1)
        + (affData hκ hc).snd.hFun ((basisState κ c n : L2I ℕ) : ℕ → ℂ) (n + 1) := rfl
  rw [e]
  have hX : ∀ m, ((basisState κ c n : L2I ℕ) : ℕ → ℂ) m = if m = n then 1 else 0 := by
    intro m
    show (lp.single 2 n (1 : ℂ) : L2I ℕ) m = _
    rw [lp.single_apply, Pi.single_apply]
  have h2 : (affData hκ hc).snd.hop (fun α => (((affData hκ hc).snd.amp α : ℝ) : ℂ) *
      ((basisState κ c n : L2I ℕ) : ℕ → ℂ) α) (n + 1)
      = (((affData hκ hc).snd.amp n : ℝ) : ℂ) * ((basisState κ c n : L2I ℕ) : ℕ → ℂ) n :=
    (affData hκ hc).snd.hop_shift _ n
  have h1 : (affData hκ hc).fst.hop (fun α => (((affData hκ hc).fst.amp α : ℝ) : ℂ) *
      ((basisState κ c n : L2I ℕ) : ℕ → ℂ) α) (n + 1) = 0 := by
    rcases n with _ | m
    · apply ShiftData.hop_eq_zero
      rintro ⟨α, hα⟩
      have : α + 2 = 1 := hα
      omega
    · have := (affData hκ hc).fst.hop_shift (fun α => (((affData hκ hc).fst.amp α : ℝ) : ℂ) *
        ((basisState κ c (m+1) : L2I ℕ) : ℕ → ℂ) α) m
      refine this.trans ?_
      rw [hX]; simp
  simp only [ShiftData.hFun] at *
  rw [h1, h2]
  have s1 : (affData hκ hc).shift₁ (n + 1) = n + 3 := rfl
  have s2 : (affData hκ hc).shift₂ (n + 1) = n + 2 := rfl
  have a2 : (affData hκ hc).amp₂ n = shear c n := rfl
  rw [s1, s2, a2, hX, hX, hX]
  simp

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.AffineFiber BookProof.NavierStokesFlow.IkebeKato
  BookProof.NavierStokesFlow.HermiteFarisLavine BookProof.NavierStokesFlow.ShiftHamiltonian in
theorem h43_coord2 {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) (n : ℕ) :
    ((affH hκ hc (basisState κ c n) : L2I ℕ) : ℕ → ℂ) (n + 2)
      = Complex.I * ((amp κ n : ℝ) : ℂ) := by
  have e : ((affH hκ hc (basisState κ c n) : L2I ℕ) : ℕ → ℂ) (n + 2)
      = (affData hκ hc).fst.hFun ((basisState κ c n : L2I ℕ) : ℕ → ℂ) (n + 2)
        + (affData hκ hc).snd.hFun ((basisState κ c n : L2I ℕ) : ℕ → ℂ) (n + 2) := rfl
  rw [e]
  have hX : ∀ m, ((basisState κ c n : L2I ℕ) : ℕ → ℂ) m = if m = n then 1 else 0 := by
    intro m
    show (lp.single 2 n (1 : ℂ) : L2I ℕ) m = _
    rw [lp.single_apply, Pi.single_apply]
  have h1 : (affData hκ hc).fst.hop (fun α => (((affData hκ hc).fst.amp α : ℝ) : ℂ) *
      ((basisState κ c n : L2I ℕ) : ℕ → ℂ) α) (n + 2)
      = (((affData hκ hc).fst.amp n : ℝ) : ℂ) * ((basisState κ c n : L2I ℕ) : ℕ → ℂ) n :=
    (affData hκ hc).fst.hop_shift _ n
  have h2 : (affData hκ hc).snd.hop (fun α => (((affData hκ hc).snd.amp α : ℝ) : ℂ) *
      ((basisState κ c n : L2I ℕ) : ℕ → ℂ) α) (n + 2) = 0 := by
    have := (affData hκ hc).snd.hop_shift (fun α => (((affData hκ hc).snd.amp α : ℝ) : ℂ) *
        ((basisState κ c n : L2I ℕ) : ℕ → ℂ) α) (n + 1)
    refine this.trans ?_
    rw [hX]; simp
  simp only [ShiftData.hFun] at *
  rw [h1, h2]
  rw [show (affData hκ hc).shift₁ (n + 2) = n + 4 from rfl,
    show (affData hκ hc).shift₂ (n + 2) = n + 3 from rfl,
    show (affData hκ hc).amp₁ n = amp κ n from rfl, hX, hX, hX]
  simp

theorem solution (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j)
    (hunb : ∀ C : ℝ, ∃ j, C < κ j) (C : ℝ) :
    ∃ x : lpFiniteModes (ℕ × J),
      ‖((x : lpFiniteModes (ℕ × J)) : L2I (ℕ × J))‖ = 1
        ∧ C < ‖affBlockH κ c hκ hc x‖ := by
  classical
  obtain ⟨j, hj⟩ := hunb (2 * C)
  let x : lpFiniteModes (ℕ × J) := ⟨lp.single 2 ((0 : ℕ), j) (1 : ℂ), lpSingle_mem_lpFiniteModes _ _⟩
  refine ⟨x, ?_, ?_⟩
  · show ‖(lp.single 2 ((0 : ℕ), j) (1 : ℂ) : L2I (ℕ × J))‖ = 1
    rw [lp.norm_single (by norm_num)]; simp
  · have hfun : (fun n => ((x : L2I (ℕ × J)) : ℕ × J → ℂ) (n, j))
        = ((basisState (κ j) (c j) 0 : L2I ℕ) : ℕ → ℂ) := by
      funext n
      show (lp.single 2 ((0 : ℕ), j) (1 : ℂ) : L2I (ℕ × J)) (n, j)
        = (lp.single 2 (0 : ℕ) (1 : ℂ) : L2I ℕ) n
      rw [lp.single_apply, lp.single_apply, Pi.single_apply, Pi.single_apply]
      simp
    have hc2 : ((affBlockH κ c hκ hc x : L2I (ℕ × J)) : ℕ × J → ℂ) (0 + 2, j)
        = Complex.I * ((amp (κ j) 0 : ℝ) : ℂ) := by
      rw [← h43_coord2 (hκ j) (hc j) 0]
      show (affData (hκ j) (hc j)).fst.hFun (fun n => ((x : L2I (ℕ × J)) : ℕ × J → ℂ) (n, j)) (0 + 2)
        + (affData (hκ j) (hc j)).snd.hFun (fun n => ((x : L2I (ℕ × J)) : ℕ × J → ℂ) (n, j)) (0 + 2)
        = _
      rw [hfun]
      rfl
    have hle := lp.norm_apply_le_norm (p := 2) (by norm_num)
      (affBlockH κ c hκ hc x : L2I (ℕ × J)) (0 + 2, j)
    rw [hc2] at hle
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, one_mul, Real.norm_eq_abs] at hle
    have hamp : κ j / 2 ≤ amp (κ j) 0 := by
      unfold amp
      have hs : (1:ℝ) ≤ Real.sqrt ((((0:ℕ):ℝ) + 1) * (((0:ℕ):ℝ) + 2)) := by
        apply Real.le_sqrt_of_sq_le; norm_num
      have := hκ j
      have h0 : (0:ℝ) ≤ κ j / 2 := by linarith
      calc κ j / 2 = κ j / 2 * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hs h0
    have := le_abs_self (amp (κ j) 0)
    show C < ‖(affBlockH κ c hκ hc x : L2I (ℕ × J))‖
    linarith

