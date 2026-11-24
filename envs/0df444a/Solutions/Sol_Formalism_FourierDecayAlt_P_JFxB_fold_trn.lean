-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.fold_trn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:14:11.072915+00:00
-- url     : https://prove2.me/submissions/613cd14d-cbf4-42da-a51d-5ca1a9d0d1d0

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_top_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_ckOn_fold
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
section Transport
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
private theorem ckOn_mono_lemma {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {m n : ℕ} (h : n ≤ m)
    {f : Mat k r → F} (hf : CkOn (m : ℕ∞) (GV k r) f) : CkOn (n : ℕ∞) (GV k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg, hc, he⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hg, hc.of_le (by exact_mod_cast h), he⟩
end Transport
section Letters
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
end Letters
end Formalism.FourierDecayAlt.P.JFxB
end
end

set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution (L : E →L[ℂ] E') {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r)
    (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E') → (Mat k r → E'))
    (Eop' : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
    (hI : ∀ c d (f : Mat k r → E), CkOn ((1 : ℕ) : ℕ∞) (GV k r) f →
      ∀ g ∈ GV k r, Eop c d (trn L a b f) g = trn L a b (Eop' c d f) g)
    (hC : ∀ c d (f f₂ : Mat k r → E'), (∀ g ∈ GV k r, f g = f₂ g) → ∀ g ∈ GV k r, Eop c d f g = Eop c d f₂ g)
    (hS' : ∀ c d (m : ℕ) (f : Mat k r → E), CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f →
      CkOn (m : ℕ∞) (GV k r) (Eop' c d f))
    (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ (f : Mat k r → E), CkOn ((ts.length : ℕ) : ℕ∞) (GV k r) f → ∀ g ∈ GV k r,
      (ts.map fun t => Top Eop t.1 t.2.1 t.2.2).foldr (fun T h => T h) (trn L a b f) g =
        trn L a b ((ts.map fun t => Top Eop' t.1 t.2.1 t.2.2).foldr (fun T h => T h) f) g := by
  induction ts with
  | nil =>
    intro f _ g _
    rfl
  | cons t ts ih =>
    intro f hf g hg
    have hfl : CkOn ((ts.length + 1 : ℕ) : ℕ∞) (GV k r) f := by simpa using hf
    have hf0 : CkOn ((ts.length : ℕ) : ℕ∞) (GV k r) f := ckOn_mono_lemma (Nat.le_succ _) hfl
    have hY : CkOn ((1 : ℕ) : ℕ∞) (GV k r)
        ((ts.map fun t => Top Eop' t.1 t.2.1 t.2.2).foldr (fun T h => T h) f) :=
      ckOn_fold Eop' hS' ts 1 f (by simpa [Nat.add_comm] using hfl)
    have hX := ih f hf0
    show Top Eop t.1 t.2.1 t.2.2
        ((ts.map fun t => Top Eop t.1 t.2.1 t.2.2).foldr (fun T h => T h) (trn L a b f)) g =
      trn L a b (Top Eop' t.1 t.2.1 t.2.2
        ((ts.map fun t => Top Eop' t.1 t.2.1 t.2.2).foldr (fun T h => T h) f)) g
    rw [top_apply, hX g hg, hC t.2.1 t.2.2 _ _ hX g hg, hI t.2.1 t.2.2 _ hY g hg]
    simp only [trn, top_apply]
    split_ifs <;> simp [map_add, map_smul]
end Formalism.FourierDecayAlt.P.JFxB
