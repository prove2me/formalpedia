-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x2.gramRealiseCut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:44.187806+00:00
-- url     : https://prove2.me/submissions/f38faec3-f648-4605-a8b9-4ab4f9c15889

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PosSemidefEntryBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x2_exists_factor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x2
namespace Formalism.FourierDecayAlt.P.A6x2
theorem _root_.solution : GramRealiseCut := by
  intro X F G Gc h1 h2
  classical
  obtain ⟨S1, hS1⟩ := exists_factor F Gc h1
  obtain ⟨S2, hS2⟩ := exists_factor F _ h2
  let e : (F ⊕ F) ≃ Fin (Fintype.card (F ⊕ F)) := Fintype.equivFin _
  let u : X → EuclideanSpace ℂ (Fin (Fintype.card (F ⊕ F))) := fun x =>
    WithLp.toLp 2 (fun i => if hx : x ∈ F then
      Sum.elim (fun j => S1 j ⟨x, hx⟩) (fun j => S2 j ⟨x, hx⟩) (e.symm i) else 0)
  let d : Fin (Fintype.card (F ⊕ F)) → ℂ := fun i => if (e.symm i).isLeft then 1 else 0
  let T : EuclideanSpace ℂ (Fin (Fintype.card (F ⊕ F))) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin (Fintype.card (F ⊕ F))) :=
    { toFun := fun v => WithLp.toLp 2 (fun i => d i * v i)
      map_add' := by
        intro v w; ext i; simp [mul_add]
      map_smul' := by
        intro c v; ext i; simp; ring }
  refine ⟨_, u, T, ?_, ?_, ?_⟩
  · intro v
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    show ‖d i * v i‖ ^ 2 ≤ ‖v i‖ ^ 2
    by_cases hi : (e.symm i).isLeft
    · simp [d, hi]
    · simp [d, hi]
  · intro x hx y hy
    rw [PiLp.inner_apply, ← e.sum_comp, Fintype.sum_sum_type]
    have h3 := hS1 ⟨x, hx⟩ ⟨y, hy⟩
    have h4 := hS2 ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Finset.univ_eq_attach] at h3 h4
    simp only [u, hx, hy, dite_true, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
      RCLike.inner_apply, Finset.univ_eq_attach]
    rw [← h3, ← h4]
    ring
  · intro x hx y hy
    rw [PiLp.inner_apply, ← e.sum_comp, Fintype.sum_sum_type]
    have h3 := hS1 ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Finset.univ_eq_attach] at h3
    simp [u, T, d, hx, hy]
    exact h3.symm
end Formalism.FourierDecayAlt.P.A6x2
