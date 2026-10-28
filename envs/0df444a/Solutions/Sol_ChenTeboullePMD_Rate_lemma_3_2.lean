-- Prove2me | solution 1 for ChenTeboullePMD.Rate.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:49:02.655727+00:00
-- url     : https://prove2.me/submissions/4c819815-ba8b-4776-b01f-2ce6740c4f8c

import Definitions.Def_ChenTeboullePMD_Rate_Setting
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Filter Topology BeckTeboulleMD.EMDA ChenTeboullePMD.Rate

private theorem three_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q) (φ : E → ℝ) (hφ : ConvexOn ℝ Q φ) (h : E → ℝ)
    (z zp : E) (hhd : DifferentiableAt ℝ h zp) (hzp : zp ∈ Q)
    (hmin : ∀ u ∈ Q, φ zp + bregman h zp z ≤ φ u + bregman h u z) :
    ∀ u ∈ Q, φ u + bregman h u z ≥ φ zp + bregman h zp z + bregman h u zp := by
  intro u hu
  let d := u - zp
  let a : ℝ → E := fun t => zp + t • d
  have had : HasDerivAt a d 0 := by
    simpa only [a, id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add zp
  have hhder : HasDerivAt (fun t => h (a t)) (fderiv ℝ h zp d) 0 := by
    have hdz : HasFDerivAt h (fderiv ℝ h zp) (a 0) := by
      simpa only [a, zero_smul, add_zero] using hhd.hasFDerivAt
    exact hdz.comp_hasDerivAt 0 had
  have hlim : Tendsto (fun t : ℝ => (h (a t) - h zp) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (fderiv ℝ h zp d)) := by
    simpa [a, smul_eq_mul, div_eq_mul_inv, mul_comm] using hhder.tendsto_slope_zero_right
  have hlimG : Tendsto
      (fun t : ℝ => φ u - φ zp + (h (a t) - h zp) / t - fderiv ℝ h z d)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (φ u - φ zp + fderiv ℝ h zp d - fderiv ℝ h z d)) :=
    (tendsto_const_nhds.add hlim).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => fderiv ℝ h z d)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (fderiv ℝ h z d)))
  have hpos : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 ≤ φ u - φ zp + (h (a t) - h zp) / t - fderiv ℝ h z d := by
    have hsmall : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t < 1 :=
      (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with t ht0 ht1
    have htpos : 0 < t := ht0
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨htpos.le, ht1.le⟩
    have hamem : a t ∈ Q := hQ.add_smul_sub_mem hzp hu ht
    have haeq : (1 - t) • zp + t • u = a t := by
      dsimp [a, d]
      rw [sub_smul, one_smul, smul_sub]
      abel
    have hc := hφ.2 hzp hu (sub_nonneg.mpr ht1.le) htpos.le (sub_add_cancel 1 t)
    rw [haeq] at hc
    simp only [smul_eq_mul] at hc
    have hm := hmin (a t) hamem
    have hl : fderiv ℝ h z (a t - z) = fderiv ℝ h z (zp - z) + t * fderiv ℝ h z d := by
      have hv : a t - z = (zp - z) + t • d := by dsimp [a]; abel
      rw [hv, map_add, map_smul, smul_eq_mul]
    unfold bregman at hm
    rw [hl] at hm
    have hpre : 0 ≤ t * (φ u - φ zp - fderiv ℝ h z d) + h (a t) - h zp := by
      nlinarith only [hm, hc]
    by_contra! hb
    have hbad := mul_neg_of_pos_of_neg htpos hb
    have halg : t * (φ u - φ zp + (h (a t) - h zp) / t - fderiv ℝ h z d) =
        t * (φ u - φ zp - fderiv ℝ h z d) + h (a t) - h zp := by
      field_simp [htpos.ne'] <;> ring
    rw [halg] at hbad
    linarith only [hpre, hbad]
  have hle : 0 ≤ φ u - φ zp + fderiv ℝ h zp d - fderiv ℝ h z d :=
    ge_of_tendsto hlimG hpos
  dsimp [d] at hle
  unfold bregman
  simp only [map_sub] at hle ⊢
  linarith only [hle]


theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Set E) (ψ : E → ℝ) (hψ : IsBregmanFunction S ψ)
    (C : Set E) (hCne : C.Nonempty) (hCconv : Convex ℝ C)
    (f : E → ℝ) (hf : ConvexOn ℝ C f)
    (hlsc : LowerSemicontinuous (extendTop C f))
    (hri : intrinsicInterior ℝ C ⊆ S)
    (lam : ℕ → ℝ) (hlam : ∀ k, 1 ≤ k → 0 < lam k)
    (x : ℕ → E) (hrun : IsPMDRun S C ψ f lam x) :
    ∀ k : ℕ, ∀ u ∈ C, u ∈ closure S →
      lam (k + 1) * (f (x (k + 1)) - f u) ≤
        bregman ψ u (x k) - bregman ψ u (x (k + 1)) -
          bregman ψ (x (k + 1)) (x k) := by
  intro k u hu huS
  let Q := C ∩ closure S
  have hQ : Convex ℝ Q := hCconv.inter hψ.strictConvexOn.1
  have hl : 0 < lam (k+1) := hlam (k+1) (Nat.succ_le_succ (Nat.zero_le k))
  have hφ : ConvexOn ℝ Q (fun v => lam (k+1) * f v) := by
    refine ⟨hQ,?_⟩
    intro a ha b hb r s hr hs hrs
    have he := mul_le_mul_of_nonneg_left (hf.2 ha.1 hb.1 hr hs hrs) hl.le
    simpa only [smul_eq_mul, mul_add, mul_assoc, mul_left_comm] using he
  have hxpQ : x (k+1) ∈ Q := ⟨(hrun.2 k).2.1, subset_closure (hrun.2 k).1⟩
  have hdiff : DifferentiableAt ℝ ψ (x (k+1)) :=
    (hψ.contDiffOn.differentiableOn (by norm_num) _ (hrun.2 k).1).differentiableAt
      (hψ.isOpen.mem_nhds (hrun.2 k).1)
  have hmin : ∀ v ∈ Q,
      lam (k+1) * f (x (k+1)) + bregman ψ (x (k+1)) (x k) ≤
        lam (k+1) * f v + bregman ψ v (x k) := by
    intro v hv
    have hm := mul_le_mul_of_nonneg_left ((hrun.2 k).2.2 v hv.1 hv.2) hl.le
    simpa only [mul_add, ← mul_assoc, mul_inv_cancel₀ hl.ne', one_mul] using hm
  have ht := three_point Q hQ (fun v => lam (k+1)*f v) hφ ψ (x k) (x (k+1))
    hdiff hxpQ hmin u ⟨hu,huS⟩
  nlinarith only [ht]

#print axioms solution
