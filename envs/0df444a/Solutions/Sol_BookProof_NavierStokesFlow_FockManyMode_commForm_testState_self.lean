-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockManyMode.commForm_testState_self
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T12:18:20.438727+00:00
-- url     : https://prove2.me/submissions/cfdfdc1d-0b92-4c35-b03c-61e59a13b85f

import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa

set_option autoImplicit false

open BookProof.NavierStokesFlow.HermiteFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData
open BookProof.NavierStokesFlow.FockManyMode

open scoped ENNReal

open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian

namespace P_a1ed0741

theorem summable_v {ι : Type*} (S : ShiftData ι) (x : maxDom S.sym) :
    Summable (fun β => 2 * S.sym β * S.amp β *
      ((starRingEnd ℂ) (((x : L2I ι) : ι → ℂ) β) * ((x : L2I ι) : ι → ℂ) (S.shift β)).re) := by
  have hsq := ShiftData.summable_ampSeq_sq S x
  have hN := (ShiftData.hasSum_normSq (diagMax S.sym x)).summable
  refine Summable.of_norm_bounded (hN.add (ShiftData.summable_comp_shift S hsq)) ?_
  intro β
  set X : ι → ℂ := ((x : L2I ι) : ι → ℂ)
  have hsig := ShiftData.sym_nonneg S β
  have hw := S.amp_nonneg β
  have hmono := S.amp_mono β
  have hre := Complex.abs_re_le_norm ((starRingEnd ℂ) (X β) * X (S.shift β))
  have hz : ‖(starRingEnd ℂ) (X β) * X (S.shift β)‖ = ‖X β‖ * ‖X (S.shift β)‖ := by
    rw [norm_mul, Complex.norm_conj]
  rw [hz] at hre
  have hd := ShiftData.norm_diagMax_coe S x β
  simp only [ShiftData.ampSeq]
  rw [hd, Real.norm_eq_abs]
  have ha := norm_nonneg (X β)
  have hb := norm_nonneg (X (S.shift β))
  have h1 : |2 * S.sym β * S.amp β * ((starRingEnd ℂ) (X β) * X (S.shift β)).re|
      ≤ 2 * S.sym β * S.amp β * (‖X β‖ * ‖X (S.shift β)‖) := by
    rw [abs_mul]
    have : |2 * S.sym β * S.amp β| = 2 * S.sym β * S.amp β := abs_of_nonneg (by positivity)
    rw [this]
    exact mul_le_mul_of_nonneg_left hre (by positivity)
  have h2 : S.amp β * ‖X (S.shift β)‖ ≤ S.amp (S.shift β) * ‖X (S.shift β)‖ :=
    mul_le_mul_of_nonneg_right hmono hb
  nlinarith [sq_nonneg (S.sym β * ‖X β‖ - S.amp (S.shift β) * ‖X (S.shift β)‖),
    mul_le_mul_of_nonneg_left h2 (mul_nonneg hsig ha)]

theorem main {ι : Type*} (S : ShiftData ι) (x : maxDom S.sym) :
    HasSum (fun β => 2 * S.step * (S.amp β
        * ((starRingEnd ℂ) (((x : L2I ι) : ι → ℂ) β)
            * ((x : L2I ι) : ι → ℂ) (S.shift β)).re))
      (commForm (shiftH S) (diagMax S.sym) x) := by
  set X : ι → ℂ := ((x : L2I ι) : ι → ℂ) with hXdef
  have hinner := lp.hasSum_inner (𝕜 := ℂ) (shiftH S x) (diagMax S.sym x)
  have hinner2 := lp.hasSum_inner (𝕜 := ℂ) (diagMax S.sym x) (shiftH S x)
  have hf := Complex.hasSum_re ((hinner.sub hinner2).mul_left Complex.I)
  have hC : (Complex.I * (inner ℂ (shiftH S x) (diagMax S.sym x)
      - inner ℂ (diagMax S.sym x) (shiftH S x))).re
      = commForm (shiftH S) (diagMax S.sym) x := rfl
  rw [hC] at hf
  set u' : ι → ℝ := fun α => 2 * S.sym (S.shift α) * S.amp α *
      ((starRingEnd ℂ) (X α) * X (S.shift α)).re with hu'
  set v : ι → ℝ := fun β => 2 * S.sym β * S.amp β *
      ((starRingEnd ℂ) (X β) * X (S.shift β)).re with hv
  have hvs : Summable v := summable_v S x
  have hpt : ∀ β, (Complex.I * (inner ℂ ((shiftH S x : L2I ι) β) ((diagMax S.sym x : L2I ι) β)
      - inner ℂ ((diagMax S.sym x : L2I ι) β) ((shiftH S x : L2I ι) β))).re
      = S.hop u' β - v β := by
    intro β
    have hH : ((shiftH S x : L2I ι) : ι → ℂ) β = S.hFun X β := rfl
    have hD : ((diagMax S.sym x : L2I ι) : ι → ℂ) β = (S.sym β : ℂ) * X β := rfl
    rw [hH, hD]
    by_cases hb : ∃ α, S.shift α = β
    · obtain ⟨α, rfl⟩ := hb
      simp only [ShiftData.hFun, ShiftData.hop_shift, hu', hv, RCLike.inner_apply]
      simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, map_mul, map_sub, RCLike.conj_to_real, Complex.conj_ofReal,
        Complex.conj_I, Complex.neg_re, Complex.neg_im]
      ring
    · simp only [ShiftData.hFun, ShiftData.hop_eq_zero S _ hb, hv, RCLike.inner_apply]
      simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, map_mul, map_sub, Complex.conj_ofReal,
        Complex.conj_I, Pi.zero_apply, map_zero, Complex.zero_re, Complex.zero_im, Complex.neg_re, Complex.neg_im]
      ring
  have hf' : HasSum (fun β => S.hop u' β - v β) (commForm (shiftH S) (diagMax S.sym) x) := by
    have := hf
    simp only [hpt] at this
    exact this
  have hu : HasSum (S.hop u') (commForm (shiftH S) (diagMax S.sym) x + ∑' β, v β) := by
    have := hf'.add hvs.hasSum
    simpa using this
  have hu2 : HasSum u' (commForm (shiftH S) (diagMax S.sym) x + ∑' β, v β) :=
    (ShiftData.hasSum_hop_iff S).mp hu
  have hg := hu2.sub hvs.hasSum
  rw [add_sub_cancel_right] at hg
  have hfun : (fun β => 2 * S.step * (S.amp β
        * ((starRingEnd ℂ) (X β) * X (S.shift β)).re)) = fun b => u' b - v b := by
    funext β
    simp only [hu', hv, S.sym_step]
    ring
  rw [hfun]
  exact hg

end P_a1ed0741

section P2MHelpers

variable {d : ℕ} {κ : Fin d → ℝ}

theorem p2m_a1ed0741_coord (i₀ : Fin d) (β : Occ d) :
    (((testState κ i₀ : maxDom (fockSym κ)) : L2I (Occ d)) : Occ d → ℂ) β
      = (if β = 0 then (1 : ℂ) else 0) + (if β = modeShift i₀ 0 then (1 : ℂ) else 0) := by
  show ((lp.single 2 (0 : Occ d) (1 : ℂ) + lp.single 2 (modeShift i₀ (0 : Occ d)) (1 : ℂ)
      : L2I (Occ d)) : Occ d → ℂ) β = _
  rw [lp.coeFn_add, Pi.add_apply]
  congr 1
  · by_cases h : β = 0
    · subst h; rw [lp.single_apply_self, if_pos rfl]
    · rw [lp.single_apply_ne _ _ _ h, if_neg h]
  · by_cases h : β = modeShift i₀ 0
    · subst h; rw [lp.single_apply_self, if_pos rfl]
    · rw [lp.single_apply_ne _ _ _ h, if_neg h]

theorem p2m_a1ed0741_shift_ne_zero (i₀ : Fin d) (β : Occ d) : modeShift i₀ β ≠ 0 := by
  intro h
  have := congrFun h i₀
  simp at this

end P2MHelpers

open BookProof.NavierStokesFlow.HermiteFarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData BookProof.NavierStokesFlow.FockManyMode LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian in
theorem solution {d : ℕ} {κ : Fin d → ℝ} (hκ : ∀ i, 0 ≤ κ i) (i₀ : Fin d) :
    commForm (ShiftData.shiftH (modeData hκ i₀)) (diagMax (fockSym κ)) (testState κ i₀)
      = 2 * (4 * κ i₀) * modeAmp κ i₀ 0 := by
  have h := P_a1ed0741.main (modeData hκ i₀) (testState κ i₀)
  have hfun : (fun β => 2 * (modeData hκ i₀).step * ((modeData hκ i₀).amp β
        * ((starRingEnd ℂ) (((testState κ i₀ : maxDom (fockSym κ)) : L2I (Occ d)) β)
            * ((testState κ i₀ : maxDom (fockSym κ)) : L2I (Occ d))
                ((modeData hκ i₀).shift β)).re))
      = fun β => if β = 0 then 2 * (4 * κ i₀) * modeAmp κ i₀ 0 else 0 := by
    funext β
    change 2 * (4 * κ i₀) * (modeAmp κ i₀ β
        * ((starRingEnd ℂ) (((testState κ i₀ : maxDom (fockSym κ)) : L2I (Occ d)) β)
            * ((testState κ i₀ : maxDom (fockSym κ)) : L2I (Occ d)) (modeShift i₀ β)).re) = _
    rw [p2m_a1ed0741_coord i₀ β, p2m_a1ed0741_coord i₀ (modeShift i₀ β),
      if_neg (p2m_a1ed0741_shift_ne_zero i₀ β)]
    have h0 : (0 : Occ d) ≠ modeShift i₀ 0 := (p2m_a1ed0741_shift_ne_zero i₀ 0).symm
    by_cases hb : β = 0
    · subst hb
      rw [if_pos rfl, if_pos rfl, if_neg h0, if_pos rfl]
      simp
    · have hs : modeShift i₀ β ≠ modeShift i₀ 0 := fun e => hb (modeShift_injective i₀ e)
      rw [if_neg hs, if_neg hb]
      simp [hb]
  rw [hfun] at h
  exact h.unique (hasSum_ite_eq 0 _)
