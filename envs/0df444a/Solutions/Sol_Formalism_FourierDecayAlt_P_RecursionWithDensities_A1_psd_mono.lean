-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.psd_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:34.922499+00:00
-- url     : https://prove2.me/submissions/7ff58019-6569-4156-90d2-b809a480282a

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {α : Type}
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
theorem _root_.solution {P Q : Finset α} {k : α → α → ℂ} (hQ : Q ⊆ P) (hk : PSDOn P k) : PSDOn Q k := by
  unfold TA.PSDOn at hk ⊢
  refine ⟨fun x hx y hy => hk.1 x (hQ hx) y (hQ hy), fun a => ?_⟩
  obtain ⟨b, hbQ, hb0⟩ : ∃ b : α → ℂ, (∀ x ∈ Q, b x = a x) ∧ ∀ x, x ∉ Q → b x = 0 :=
    ⟨fun x => if x ∈ Q then a x else 0, fun x hx => by simp [hx], fun x hx => by simp [hx]⟩
  have h := hk.2 b
  have e1 : ∀ x ∈ P, ∑ y ∈ P, conj (b x) * k x y * b y = ∑ y ∈ Q, conj (b x) * k x y * b y :=
    fun x _ => (Finset.sum_subset (f := fun y => conj (b x) * k x y * b y) hQ
      (fun y _ hy => by simp [hb0 y hy])).symm
  rw [Finset.sum_congr rfl e1] at h
  rw [← Finset.sum_subset (f := fun x => ∑ y ∈ Q, conj (b x) * k x y * b y) hQ
    (fun x _ hx => by simp [hb0 x hx])] at h
  have e2 : ∑ x ∈ Q, ∑ y ∈ Q, conj (b x) * k x y * b y =
      ∑ x ∈ Q, ∑ y ∈ Q, conj (a x) * k x y * a y :=
    Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by rw [hbQ x hx, hbQ y hy]
  rw [e2] at h
  exact h
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
