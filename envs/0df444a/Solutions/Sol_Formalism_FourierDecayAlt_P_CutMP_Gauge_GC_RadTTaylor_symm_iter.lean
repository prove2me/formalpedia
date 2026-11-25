-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor.symm_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:33:13.084083+00:00
-- url     : https://prove2.me/submissions/577f39b1-e7be-4128-8f9f-1d68fd8424f9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTTaylor
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_RadTTaylor_perm_of_swaps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor
theorem _root_.solution : ∀ (n : ℕ) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (f : E → W) (U : Set E),
    IsOpen U → ContDiffOn ℝ ∞ f U → ∀ x ∈ U, ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E),
      iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by
  have hle : ∀ k : ℕ, ((k : ℕ) : WithTop ℕ∞) ≤ ∞ := fun k => by
    first
    | exact WithTop.coe_le_coe.2 le_top
    | exact_mod_cast (le_top : ((k : ℕ∞)) ≤ ⊤)
  intro n
  induction n with
  | zero =>
    intro W _ _ f U hU hf x hx σ v
    rw [Subsingleton.elim (v ∘ σ) v]
  | succ n ih =>
    intro W _ _ f U hU hf x hx
    refine perm_of_swaps (iteratedFDeriv ℝ (n + 1) f x) ?_
    intro a b hab
    rcases n with _ | m
    · exact absurd (Fin.ext (by have := a.isLt; have := b.isLt; omega)) hab
    have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hU.mem_nhds hx)
    have hmul : ∀ σ τ : Equiv.Perm (Fin (m + 1 + 1)),
        (∀ v, iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ σ) = iteratedFDeriv ℝ (m + 1 + 1) f x v) →
        (∀ v, iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ τ) = iteratedFDeriv ℝ (m + 1 + 1) f x v) →
        ∀ v, iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ ⇑(σ * τ)) = iteratedFDeriv ℝ (m + 1 + 1) f x v := by
      intro σ τ hσ hτ v
      rw [Equiv.Perm.coe_mul]
      exact (hτ (v ∘ σ)).trans (hσ v)
    have T1 : ∀ a' b' : Fin (m + 1), a' ≠ b' → ∀ v : Fin (m + 1 + 1) → E,
        iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ Equiv.swap a'.succ b'.succ) =
          iteratedFDeriv ℝ (m + 1 + 1) f x v := by
      intro a' b' _ v
      rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left]
      have h0 : (v ∘ Equiv.swap a'.succ b'.succ) 0 = v 0 := by
        simp only [Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero a').symm (Fin.succ_ne_zero b').symm]
      have ht : Fin.tail (v ∘ Equiv.swap a'.succ b'.succ) = Fin.tail v ∘ Equiv.swap a' b' := by
        funext i
        simp only [Fin.tail, Function.comp_apply]
        rw [(Fin.succ_injective _).swap_apply]
      rw [h0, ht]
      have hgd : DifferentiableAt ℝ (iteratedFDeriv ℝ (m + 1) f) x :=
        (hfx.iteratedFDeriv_right (m := 1) (i := m + 1) (by
          have := hle (1 + (m + 1)); push_cast at this ⊢; exact this)).differentiableAt one_ne_zero
      rw [← fderiv_continuousMultilinear_apply_const_apply hgd,
        ← fderiv_continuousMultilinear_apply_const_apply hgd]
      rw [Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hU.mem_nhds hx)
        (fun y hy => ih W f U hU hf y hy (Equiv.swap a' b') (Fin.tail v)))]
    have T2 : ∀ v : Fin (m + 1 + 1) → E,
        iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ Equiv.swap 0 (Fin.succ 0)) =
          iteratedFDeriv ℝ (m + 1 + 1) f x v := by
      intro v
      have hrepr : ∀ w : Fin (m + 1 + 1) → E, iteratedFDeriv ℝ (m + 1 + 1) f x w =
          fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ m f)) x (w 0) (Fin.tail w 0) (Fin.tail (Fin.tail w)) := by
        intro w
        rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.comp_fderiv]
        first
        | rfl
        | simp [continuousMultilinearCurryLeftEquiv_symm_apply]
      rw [hrepr, hrepr]
      have hg : ContDiffAt ℝ 2 (iteratedFDeriv ℝ m f) x :=
        hfx.iteratedFDeriv_right (by have := hle (2 + m); push_cast at this ⊢; exact this)
      have hs := hg.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])
      have e0 : (v ∘ Equiv.swap 0 (Fin.succ 0)) 0 = Fin.tail v 0 := by
        simp only [Function.comp_apply, Equiv.swap_apply_left, Fin.tail]
      have e1 : Fin.tail (v ∘ Equiv.swap 0 (Fin.succ 0)) 0 = v 0 := by
        simp only [Fin.tail, Function.comp_apply, Equiv.swap_apply_right]
      have e2 : Fin.tail (Fin.tail (v ∘ Equiv.swap 0 (Fin.succ 0))) = Fin.tail (Fin.tail v) := by
        funext i
        simp only [Fin.tail, Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
          (fun h => Fin.succ_ne_zero i (Fin.succ_injective _ h))]
      rw [e0, e1, e2, hs (Fin.tail v 0) (v 0)]
    have T0 : ∀ b' : Fin (m + 1), ∀ v : Fin (m + 1 + 1) → E,
        iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ Equiv.swap 0 b'.succ) =
          iteratedFDeriv ℝ (m + 1 + 1) f x v := by
      intro b'
      by_cases hb : b' = 0
      · subst hb; exact T2
      · have e := Equiv.swap_mul_swap_mul_swap (x := (0 : Fin (m + 1 + 1))) (y := Fin.succ 0)
          (z := b'.succ) (Fin.succ_ne_zero 0).symm (Fin.succ_ne_zero b').symm
        rw [Equiv.swap_comm, ← e]
        have h1 := T1 0 b' (Ne.symm hb)
        exact hmul _ _ (hmul _ _ h1 T2) h1
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => exact absurd rfl hab
      | succ b' => exact T0 b'
    | succ a' =>
      cases b using Fin.cases with
      | zero => intro v; rw [Equiv.swap_comm]; exact T0 a' v
      | succ b' => exact T1 a' b' (fun h => hab (h ▸ rfl))
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor
