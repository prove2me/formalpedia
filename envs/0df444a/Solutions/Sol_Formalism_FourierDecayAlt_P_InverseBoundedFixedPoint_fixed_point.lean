-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:54.051257+00:00
-- url     : https://prove2.me/submissions/813bc5f5-5627-4476-a1f8-186140c52f86

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
theorem _root_.solution {E : Type} [TopologicalSpace E] (X : Set E) (hX : IsCompact X) (hXc : IsClosed X)
    (hne : X.Nonempty) (rel : ℕ → E → E → Prop) (hcl : ∀ n y, IsClosed {x | rel n x y})
    (h0 : ∀ x ∈ X, ∀ y ∈ X, rel 0 x y) (hrefl : ∀ n x, rel n x x)
    (hmono : ∀ n x y, rel (n + 1) x y → rel n x y)
    (htrans : ∀ n x y z, rel n x y → rel n y z → rel n x z)
    (hsymm : ∀ n x y, rel n x y → rel n y x) (hsep : ∀ x y, (∀ n, rel n x y) → x = y)
    (T : E → E) (hT : ∀ x ∈ X, T x ∈ X)
    (hc : ∀ n, ∀ x ∈ X, ∀ y ∈ X, rel n x y → rel (n + 1) (T x) (T y)) : ∃ x ∈ X, T x = x := by
  obtain ⟨x0, hx0⟩ := hne
  have hx : ∀ n, T^[n] x0 ∈ X := by
    intro n
    induction n with
    | zero => exact hx0
    | succ n ih => rw [Function.iterate_succ_apply']; exact hT _ ih
  have hstep : ∀ n, rel n (T^[n + 1] x0) (T^[n] x0) := by
    intro n
    induction n with
    | zero => exact h0 _ (hx 1) _ (hx 0)
    | succ n ih =>
      have h2 := hc n _ (hx _) _ (hx _) ih
      rwa [← Function.iterate_succ_apply' T (n + 1), ← Function.iterate_succ_apply' T n] at h2
  obtain ⟨x, hxx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => X ∩ {x | rel n x (T^[n] x0)})
    (fun n x hx => ⟨hx.1, htrans n _ _ _ (hmono n _ _ hx.2) (hstep n)⟩)
    (fun n => ⟨_, hx n, hrefl n _⟩)
    (hX.of_isClosed_subset (hXc.inter (hcl 0 _)) Set.inter_subset_left)
    (fun n => hXc.inter (hcl n _))
  have hxx' := Set.mem_iInter.1 hxx
  refine ⟨x, (hxx' 0).1, hsep _ _ fun n => hmono n _ _ ?_⟩
  have h1 := hc n _ (hxx' n).1 _ (hx n) (hxx' n).2
  rw [← Function.iterate_succ_apply' T n] at h1
  exact htrans _ _ _ _ h1 (hsymm _ _ _ (hxx' (n + 1)).2)
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
