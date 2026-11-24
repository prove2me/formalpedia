-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.exch_list_rev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:17.067503+00:00
-- url     : https://prove2.me/submissions/cd72f095-7f53-4f09-9319-81b2e3b79d8c

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {R ι : Type} [Monoid R]
namespace Formalism.FourierDecayAlt.P.Wd8
theorem _root_.solution (X : R) (f g : ι → R) (L : List ι)
    (h1 : ∀ σ ∈ L, f σ * X * g σ = g σ * X * f σ)
    (h2 : L.Pairwise fun σ τ => Commute (f τ) (g σ) ∧ Commute (f σ) (g τ)) :
    (L.reverse.map f).prod * X * (L.map g).prod = (L.map g).prod * X * (L.reverse.map f).prod := by
  induction L with
  | nil => simp
  | cons σ L ih =>
    have hp := List.pairwise_cons.mp h2
    have hF : Commute (L.reverse.map f).prod (g σ) :=
      Commute.list_prod_left _ _ (by
        intro t ht
        obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
        exact (hp.1 τ (List.mem_reverse.mp hτ)).1)
    have hG : Commute (f σ) (L.map g).prod :=
      Commute.list_prod_right _ _ (by
        intro t ht
        obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
        exact (hp.1 τ hτ).2)
    have ih' := ih (fun τ hτ => h1 τ (List.mem_cons.mpr (Or.inr hτ))) hp.2
    have e1 := h1 σ (List.mem_cons.mpr (Or.inl rfl))
    have key : (L.reverse.map f).prod * f σ * X * (g σ * (L.map g).prod)
        = g σ * (L.map g).prod * X * ((L.reverse.map f).prod * f σ) := by
      calc (L.reverse.map f).prod * f σ * X * (g σ * (L.map g).prod)
          = (L.reverse.map f).prod * (f σ * X * g σ) * (L.map g).prod := by simp only [mul_assoc]
        _ = (L.reverse.map f).prod * (g σ * X * f σ) * (L.map g).prod := by rw [e1]
        _ = (L.reverse.map f).prod * g σ * X * f σ * (L.map g).prod := by simp only [mul_assoc]
        _ = g σ * (L.reverse.map f).prod * X * f σ * (L.map g).prod := by rw [hF.eq]
        _ = g σ * (L.reverse.map f).prod * X * (f σ * (L.map g).prod) := by simp only [mul_assoc]
        _ = g σ * (L.reverse.map f).prod * X * ((L.map g).prod * f σ) := by rw [hG.eq]
        _ = g σ * ((L.reverse.map f).prod * X * (L.map g).prod) * f σ := by simp only [mul_assoc]
        _ = g σ * ((L.map g).prod * X * (L.reverse.map f).prod) * f σ := by rw [ih']
        _ = g σ * (L.map g).prod * X * ((L.reverse.map f).prod * f σ) := by simp only [mul_assoc]
    simpa [List.reverse_cons, mul_assoc] using key
end Formalism.FourierDecayAlt.P.Wd8
