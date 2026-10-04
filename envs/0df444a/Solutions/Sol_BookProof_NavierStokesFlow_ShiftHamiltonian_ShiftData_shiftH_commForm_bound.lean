-- Prove2me | solution 1 for BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.shiftH_commForm_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T15:24:15.883601+00:00
-- url     : https://prove2.me/submissions/2379ec4a-4eff-4cd0-8eb1-1f5f33d3bb8e

import Mathlib
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa

set_option autoImplicit false

open BookProof.NavierStokesFlow.HermiteFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ShiftHamiltonian

open scoped ENNReal

open LpNat BookProof.FarisLavine IkebeKato

namespace P2MAux_f2de434b

theorem re_I_mul_sub_conj (T : ℂ) :
    (Complex.I * (T - (starRingEnd ℂ) T)).re = -2 * T.im := by
  simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

theorem abs_re_conj_mul_le (a b : ℂ) : |((starRingEnd ℂ) a * b).re| ≤ ‖a‖ * ‖b‖ := by
  refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_conj]

end P2MAux_f2de434b

open BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData BookProof.NavierStokesFlow.IkebeKato BookProof.FarisLavine in
theorem solution {ι : Type*} (S : ShiftData ι) (x : maxDom S.sym) :
    |commForm (shiftH S) (diagMax S.sym) x|
      ≤ (2 * S.step * (1 / 4 + S.K)) * quadForm (diagMax S.sym) x := by
  classical
  have hY : ∀ β, ((diagMax S.sym x : L2I ι) : ι → ℂ) β
      = (S.sym β : ℂ) * ((x : L2I ι) : ι → ℂ) β := fun β => rfl
  have hH : ∀ β, ((shiftH S x : L2I ι) : ι → ℂ) β = S.hFun ((x : L2I ι) : ι → ℂ) β :=
    fun β => rfl
  -- abbreviations
  let X : ι → ℂ := ((x : L2I ι) : ι → ℂ)
  -- the quadratic form series
  let q : ι → ℝ := fun β => S.sym β * ‖X β‖ ^ 2
  have hq : HasSum q (quadForm (diagMax S.sym) x) := by
    have h := Complex.hasSum_re (lp.hasSum_inner (x : L2I ι) (diagMax S.sym x : L2I ι))
    unfold quadForm
    convert h using 1
    funext β
    rw [RCLike.inner_apply', hY]
    simp only [q, X]
    simp [Complex.mul_re, Complex.mul_im, Complex.sq_norm, Complex.normSq_apply]
    ring
  -- the amplitude series
  let e : ι → ℝ := fun β => S.amp β * ‖X β‖ ^ 2
  have he_nonneg : ∀ β, 0 ≤ e β := fun β => mul_nonneg (S.amp_nonneg β) (sq_nonneg _)
  have he_le : ∀ β, e β ≤ (1 / 4 + S.K) * q β := by
    intro β
    have h1 := S.amp_le β
    have h2 := S.sym_ge_one β
    have h3 : S.amp β ≤ (1 / 4 + S.K) * S.sym β := by nlinarith [S.K_nonneg]
    simp only [e, q]
    have := mul_le_mul_of_nonneg_right h3 (sq_nonneg ‖X β‖)
    linarith
  have he : Summable e :=
    Summable.of_nonneg_of_le he_nonneg he_le (hq.summable.mul_left _)
  have hE : ∑' β, e β ≤ (1 / 4 + S.K) * quadForm (diagMax S.sym) x :=
    hasSum_le he_le he.hasSum (hq.mul_left _)
  have hes : Summable (fun β => e (S.shift β)) := he.comp_injective S.shift_injective
  have hEs : ∑' β, e (S.shift β) ≤ ∑' β, e β :=
    tsum_comp_le_tsum_of_inj he he_nonneg S.shift_injective
  -- the inner product series
  set T : ℂ := (inner ℂ (shiftH S x : L2I ι) (diagMax S.sym x : L2I ι) : ℂ) with hTdef
  have hc : commForm (shiftH S) (diagMax S.sym) x = -2 * T.im := by
    unfold commForm
    rw [← inner_conj_symm (diagMax S.sym x : L2I ι) (shiftH S x : L2I ι)]
    exact P2MAux_f2de434b.re_I_mul_sub_conj T
  have hT := Complex.hasSum_im (lp.hasSum_inner (shiftH S x : L2I ι) (diagMax S.sym x : L2I ι))
  -- the two hopping series
  let g : ι → ℝ := fun α =>
    S.amp α * S.sym (S.shift α) * ((starRingEnd ℂ) (X α) * X (S.shift α)).re
  let v : ι → ℝ := fun β =>
    S.amp β * S.sym β * ((starRingEnd ℂ) (X (S.shift β)) * X β).re
  have hpt : ∀ β, (inner ℂ (((shiftH S x : L2I ι) : ι → ℂ) β)
      (((diagMax S.sym x : L2I ι) : ι → ℂ) β) : ℂ).im = -(S.hop g β - v β) := by
    intro β
    rw [RCLike.inner_apply', hY, hH]
    by_cases hb : ∃ α, S.shift α = β
    · obtain ⟨α, rfl⟩ := hb
      simp only [ShiftData.hFun, hop_shift, g, v, X]
      simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    · simp only [ShiftData.hFun, hop_eq_zero S _ hb, g, v, X]
      simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
  have huv : HasSum (fun β => S.hop g β - v β) (-T.im) := by
    have heq : (fun β => S.hop g β - v β) = fun β => -(inner ℂ (((shiftH S x : L2I ι) : ι → ℂ) β)
        (((diagMax S.sym x : L2I ι) : ι → ℂ) β) : ℂ).im := by
      funext β
      rw [hpt β]
      ring
    rw [heq]
    exact hT.neg
  -- summability of v
  have hv : Summable v := by
    have hb1 : Summable (fun β => (S.ampSeq X (S.shift β)) ^ 2) :=
      summable_comp_shift S (summable_ampSeq_sq S x)
    have hb2 := (ShiftData.hasSum_normSq (diagMax S.sym x : L2I ι)).summable
    refine Summable.of_norm_bounded (hb1.add hb2) ?_
    intro β
    rw [Real.norm_eq_abs, norm_diagMax_coe S x β]
    change |v β| ≤ (S.amp (S.shift β) * ‖X (S.shift β)‖) ^ 2 + (S.sym β * ‖X β‖) ^ 2
    have hr := P2MAux_f2de434b.abs_re_conj_mul_le (X (S.shift β)) (X β)
    have ha := S.amp_nonneg β
    have ham := S.amp_mono β
    have hs := S.sym_nonneg β
    have hm := norm_nonneg (X (S.shift β))
    have hn := norm_nonneg (X β)
    have habs : |v β| = S.amp β * S.sym β *
        |((starRingEnd ℂ) (X (S.shift β)) * X β).re| := by
      simp only [v]
      rw [abs_mul, abs_of_nonneg (mul_nonneg ha hs)]
    rw [habs]
    have h1 : S.amp β * S.sym β * |((starRingEnd ℂ) (X (S.shift β)) * X β).re|
        ≤ (S.amp (S.shift β) * ‖X (S.shift β)‖) * (S.sym β * ‖X β‖) := by
      calc S.amp β * S.sym β * |((starRingEnd ℂ) (X (S.shift β)) * X β).re|
          ≤ S.amp β * S.sym β * (‖X (S.shift β)‖ * ‖X β‖) :=
            mul_le_mul_of_nonneg_left hr (mul_nonneg ha hs)
        _ = (S.amp β * ‖X (S.shift β)‖) * (S.sym β * ‖X β‖) := by ring
        _ ≤ (S.amp (S.shift β) * ‖X (S.shift β)‖) * (S.sym β * ‖X β‖) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ham hm)
              (mul_nonneg hs hn)
    nlinarith [sq_nonneg (S.amp (S.shift β) * ‖X (S.shift β)‖ - S.sym β * ‖X β‖)]
  have hu : Summable (S.hop g) := by
    have := huv.summable.add hv
    simpa using this
  have hg : HasSum g (∑' β, S.hop g β) := (hasSum_hop_iff S).mp hu.hasSum
  -- the hopping series r
  let r : ι → ℝ := fun α => S.amp α * ((starRingEnd ℂ) (X α) * X (S.shift α)).re
  have hgv : ∀ α, g α - v α = S.step * r α := by
    intro α
    simp only [g, v, r, S.sym_step α]
    have : ((starRingEnd ℂ) (X (S.shift α)) * X α).re
        = ((starRingEnd ℂ) (X α) * X (S.shift α)).re := by
      simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    rw [this]
    ring
  have hTim : HasSum (fun α => S.step * r α) (-T.im) := by
    have h1 : -T.im = ∑' β, S.hop g β - ∑' β, v β := by
      have h2 := huv.unique ((hu.hasSum).sub hv.hasSum)
      exact h2
    rw [h1]
    have heq : (fun α => S.step * r α) = fun α => g α - v α := funext fun α => (hgv α).symm
    rw [heq]
    exact hg.sub hv.hasSum
  have hr_le : ∀ α, |r α| ≤ (e α + e (S.shift α)) / 2 := by
    intro α
    have hr := P2MAux_f2de434b.abs_re_conj_mul_le (X α) (X (S.shift α))
    have ha := S.amp_nonneg α
    have ham := S.amp_mono α
    have hm := norm_nonneg (X α)
    have hn := norm_nonneg (X (S.shift α))
    simp only [r, e]
    rw [abs_mul, abs_of_nonneg ha]
    have h1 : S.amp α * |((starRingEnd ℂ) (X α) * X (S.shift α)).re|
        ≤ S.amp α * (‖X α‖ * ‖X (S.shift α)‖) := mul_le_mul_of_nonneg_left hr ha
    have h2 : S.amp α * (‖X α‖ * ‖X (S.shift α)‖)
        ≤ (S.amp α * ‖X α‖ ^ 2 + S.amp α * ‖X (S.shift α)‖ ^ 2) / 2 := by
      nlinarith [mul_nonneg ha (sq_nonneg (‖X α‖ - ‖X (S.shift α)‖))]
    have h3 : S.amp α * ‖X (S.shift α)‖ ^ 2 ≤ S.amp (S.shift α) * ‖X (S.shift α)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right ham (sq_nonneg _)
    linarith
  have hr : Summable r := by
    refine Summable.of_norm_bounded ((he.add hes).div_const 2) ?_
    intro α
    rw [Real.norm_eq_abs]
    exact hr_le α
  have hR : -T.im = S.step * ∑' α, r α := (hTim.unique (hr.hasSum.mul_left S.step))
  have hbound := (he.hasSum.add hes.hasSum).div_const 2
  have hRle : |∑' α, r α| ≤ (∑' β, e β + ∑' β, e (S.shift β)) / 2 := by
    rw [abs_le]
    constructor
    · have := hasSum_le (fun α => (neg_le_of_abs_le (hr_le α))) hbound.neg hr.hasSum
      linarith
    · exact hasSum_le (fun α => le_of_abs_le (hr_le α)) hr.hasSum hbound
  have hstep := S.step_nonneg
  rw [hc]
  have hcomm : -2 * T.im = 2 * S.step * ∑' α, r α := by linarith
  rw [hcomm, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * S.step)]
  have hfin : |∑' α, r α| ≤ (1 / 4 + S.K) * quadForm (diagMax S.sym) x := by linarith
  calc 2 * S.step * |∑' α, r α| ≤ 2 * S.step * ((1 / 4 + S.K) * quadForm (diagMax S.sym) x) :=
        mul_le_mul_of_nonneg_left hfin (by linarith)
    _ = (2 * S.step * (1 / 4 + S.K)) * quadForm (diagMax S.sym) x := by ring
