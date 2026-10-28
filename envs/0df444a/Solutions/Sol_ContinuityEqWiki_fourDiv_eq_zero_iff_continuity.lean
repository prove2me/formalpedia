-- Prove2me | solution 1 for ContinuityEqWiki.fourDiv_eq_zero_iff_continuity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:19:30.331472+00:00
-- url     : https://prove2.me/submissions/c3ada929-51d5-4d81-ba76-2ceef0a29d6d

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

open ContinuityEqWiki

namespace LUHelpCE

theorem timeDeriv_eq (Φ : ℝ × Space → ℝ) (t : ℝ) (x : Space)
    (h : DifferentiableAt ℝ Φ (t, x)) :
    deriv (fun s => Φ (s, x)) t = fderiv ℝ Φ (t, x) ((1 : ℝ), (0 : Space)) := by
  have h1 : HasDerivAt (Φ ∘ fun s => (s, x)) (fderiv ℝ Φ (t, x) ((1 : ℝ), (0 : Space))) t :=
    h.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  exact h1.deriv

theorem spaceDeriv_eq (Φ : ℝ × Space → ℝ) (t : ℝ) (x : Space)
    (h : DifferentiableAt ℝ Φ (t, x)) (w : Space) :
    fderiv ℝ (fun y => Φ (t, y)) x w = fderiv ℝ Φ (t, x) ((0 : ℝ), w) := by
  have h3 : HasFDerivAt (fun y : Space => ((t, y) : ℝ × Space))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have h4 := h.hasFDerivAt.comp x h3
  rw [show (fun y => Φ (t, y)) = Φ ∘ (fun y : Space => ((t, y) : ℝ × Space)) from rfl, h4.fderiv]
  simp

noncomputable def ψL (c : ℝ) : Spacetime →L[ℝ] ℝ × Space :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Y => (Y 0 / c, Fin.tail Y)
      map_add' := by
        intro Y Z
        ext <;> simp [Fin.tail, add_div]
      map_smul' := by
        intro r Y
        ext <;> simp [Fin.tail, mul_div_assoc] }

theorem ψL_apply (c : ℝ) (Y : Spacetime) : ψL c Y = (Y 0 / c, Fin.tail Y) := rfl

theorem comp_eq (c : ℝ) (G : ℝ × Space → ℝ) (X : Spacetime) (hG : DifferentiableAt ℝ G (ψL c X))
    (w : Spacetime) :
    fderiv ℝ (G ∘ ψL c) X w = fderiv ℝ G (ψL c X) (ψL c w) := by
  have := (hG.hasFDerivAt.comp X (ψL c).hasFDerivAt).fderiv
  rw [this]
  rfl

theorem four (c : ℝ) (hc : 0 < c) (ρ : ℝ → Space → ℝ) (j : ℝ → Space → Space)
    (hρ : ContDiff ℝ 1 (Function.uncurry ρ)) (hj : ContDiff ℝ 1 (Function.uncurry j))
    (t : ℝ) (x : Space) :
    fourDiv (fourCurrent c ρ j) (spacetimePoint c t x) = timeDeriv ρ t x + div (j t) x := by
  have hX : ψL c (spacetimePoint c t x) = (t, x) := by
    rw [ψL_apply]
    simp [spacetimePoint, hc.ne']
  have hρd : Differentiable ℝ (Function.uncurry ρ) := hρ.differentiable one_ne_zero
  have hjd : ∀ i : Fin 3, Differentiable ℝ (fun q => Function.uncurry j q i) := fun i =>
    (contDiff_pi.1 hj i).differentiable one_ne_zero
  unfold fourDiv div
  rw [Fin.sum_univ_succ]
  congr 1
  · -- time component
    have e0 : (fun Y : Spacetime => fourCurrent c ρ j Y 0) =
        (fun q => c * Function.uncurry ρ q) ∘ ψL c := by
      funext Y
      simp [fourCurrent, ψL_apply]
    unfold partialDeriv
    rw [e0, comp_eq c _ _ (by rw [hX]; exact (hρd _).const_mul c), hX,
      fderiv_const_mul (hρd _)]
    have hw : ψL c (Pi.single 0 1) = (1 / c) • ((1 : ℝ), (0 : Space)) := by
      rw [ψL_apply]
      ext k
      · simp
      · simp [Fin.tail, Pi.single_apply, Fin.succ_ne_zero]
    rw [hw]
    unfold timeDeriv
    rw [show (fun s => ρ s x) = fun s => Function.uncurry ρ (s, x) from rfl,
      timeDeriv_eq _ t x (hρd _)]
    simp only [ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul]
    field_simp
  · apply Finset.sum_congr rfl
    intro i _
    have ei : (fun Y : Spacetime => fourCurrent c ρ j Y i.succ) =
        (fun q => Function.uncurry j q i) ∘ ψL c := by
      funext Y
      simp [fourCurrent, ψL_apply]
    unfold partialDeriv
    rw [ei, comp_eq c _ _ (by rw [hX]; exact hjd i _), hX]
    have hw : ψL c (Pi.single i.succ 1) = ((0 : ℝ), (Pi.single i 1 : Space)) := by
      rw [ψL_apply]
      ext k
      · simp [Pi.single_apply, Fin.succ_ne_zero]
      · simp [Fin.tail, Pi.single_apply]
    rw [hw, ← spaceDeriv_eq _ t x (hjd i _)]
    rfl

end LUHelpCE
theorem solution (c : ℝ) (hc : 0 < c) (ρ : ℝ → Space → ℝ)
    (j : ℝ → Space → Space)
    (hρ : ContDiff ℝ 1 (Function.uncurry ρ)) (hj : ContDiff ℝ 1 (Function.uncurry j)) :
    (∀ X : Spacetime, fourDiv (fourCurrent c ρ j) X = 0) ↔
      ∀ (t : ℝ) (x : Space), timeDeriv ρ t x + div (j t) x = 0 := by
  constructor
  · intro h t x
    rw [← LUHelpCE.four c hc ρ j hρ hj t x]
    exact h _
  · intro h X
    have hX : X = spacetimePoint c (X 0 / c) (Fin.tail X) := by
      unfold spacetimePoint
      rw [mul_div_cancel₀ _ hc.ne']
      exact (Fin.cons_self_tail X).symm
    rw [hX, LUHelpCE.four c hc ρ j hρ hj]
    exact h _ _
