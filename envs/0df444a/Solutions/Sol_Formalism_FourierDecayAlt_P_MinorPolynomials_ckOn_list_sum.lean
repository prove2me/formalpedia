-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_list_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:21:59.118993+00:00
-- url     : https://prove2.me/submissions/283af0e6-ad4e-4f06-9822-2055cdd7ec68

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListMapSumApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComposeDifferentialOperators
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_Bd_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
private lemma ckOn_GV_add {m : ℕ∞} {f f₂ : Mat k r → (Wq →L[ℂ] Wp)} (hf : CkOn m (GV k r) f)
    (hg : CkOn m (GV k r) f₂) : CkOn m (GV k r) (fun x => f x + f₂ x) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hf g₀ hg₀
  obtain ⟨V, g', hV, hgV, hg', hge⟩ := hg g₀ hg₀
  refine ⟨U ∩ V, fun x => f' x + g' x, hU.inter hV, ⟨hgU, hgV⟩,
    (hf'.mono Set.inter_subset_left).add (hg'.mono Set.inter_subset_right), ?_⟩
  intro x hx hxG
  simp only [hfe x hx.1 hxG, hge x hx.2 hxG]
end Formalism.FourierDecayAlt.P.MinorPolynomials
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.MinorPolynomials
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution {m : ℕ∞} {α : Type*} (L : List α) (f : α → Mat k r → (Wq →L[ℂ] Wp))
    (h : ∀ a ∈ L, CkOn m (GV k r) (f a)) : CkOn m (GV k r) (fun g => (L.map fun a => f a g).sum) := by
  induction L with
  | nil =>
    intro g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => by simp⟩
  | cons a t ih =>
    have := ckOn_GV_add (h a (by simp)) (ih fun b hb => h b (by simp [hb]))
    simpa using this
end Formalism.FourierDecayAlt.P.MinorPolynomials
