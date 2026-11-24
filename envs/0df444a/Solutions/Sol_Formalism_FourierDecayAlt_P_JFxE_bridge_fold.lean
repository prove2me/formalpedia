-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.bridge_fold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:11:16.938246+00:00
-- url     : https://prove2.me/submissions/2842e2ab-70aa-4354-88d1-934492f60808

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_rep_Tm_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ev_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Rep_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ev_ck
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_rep_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
section Bridge
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
private theorem ckOn_mono_lemma_4 {m m' : ℕ∞} (h : m' ≤ m) {f : Mat k r → E} (hf : CkOn m (GV k r) f) :
    CkOn m' (GV k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hcd, heq⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hcd.of_le (WithTop.coe_le_coe.mpr h), heq⟩
private theorem rep_prod_lemma_3 {Λ : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → AA k r E} (hΛ : ∀ c d, Rep 1 (Λ c d)) :
    ∀ ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)),
      Rep ts.length ((ts.map fun t => Tm Λ t.1 t.2.1 t.2.2).prod) := by
  intro ts
  induction ts with
  | nil => exact ⟨[(1, [])], by simp, fun _ _ => by simp⟩
  | cons t ts ih =>
    rw [List.map_cons, List.prod_cons]
    exact Rep.mono (by simp only [List.length_cons]; omega) (rep_mul (rep_Tm_of hΛ _ _ _) ih)
end Bridge
section Skew
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
end Skew
section Ad
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
end Ad
end Formalism.FourierDecayAlt.P.JFxE
end
end

set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop)
    {Λ : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → AA k r E} (hΛ : ∀ c d, Rep 1 (Λ c d))
    (Op : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (hLop : HL Op)
    (hT : ∀ v c d (φ : Mat k r → E), CkOn 1 (GV k r) φ → ∀ g ∈ GV k r, ev Eop (Tm Λ v c d) φ g = Top Op v c d φ g) :
    ∀ (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (f : Mat k r → E),
      CkOn ((ts.length : ℕ) : ℕ∞) (GV k r) f → ∀ g ∈ GV k r,
        ev Eop ((ts.map fun t => Tm Λ t.1 t.2.1 t.2.2).prod) f g =
          (ts.map fun t => Top Op t.1 t.2.1 t.2.2).foldr (fun T h => T h) f g := by
  intro ts
  induction ts with
  | nil =>
    intro f _ g _
    simp [ev_one]
  | cons t ts ih =>
    intro f hf g hg
    have hP := rep_prod_lemma_3 hΛ ts
    have hf' : CkOn ((1 + ts.length : ℕ) : ℕ∞) (GV k r) f :=
      ckOn_mono_lemma_4 (ENat.coe_le_coe.mpr (by simp only [List.length_cons]; omega)) hf
    have hfs : CkOn ((ts.length : ℕ) : ℕ∞) (GV k r) f :=
      ckOn_mono_lemma_4 (ENat.coe_le_coe.mpr (by simp only [List.length_cons]; omega)) hf
    have hφ : CkOn 1 (GV k r) (ev Eop ((ts.map fun t => Tm Λ t.1 t.2.1 t.2.2).prod) f) := by
      simpa using ev_ck (Eop := Eop) hC hP 1 f hf'
    have hI := ih f hfs
    rw [List.map_cons, List.prod_cons,
      ev_mul (Eop := Eop) hC hL hA hS (rep_Tm_of hΛ _ _ _) hP f hf' g hg, hT _ _ _ _ hφ g hg]
    simp only [List.map_cons, List.foldr_cons, Formalism.QuantumDeterminants.Top]
    rw [hLop _ _ _ _ hI g hg, hI g hg]
end Formalism.FourierDecayAlt.P.JFxE
