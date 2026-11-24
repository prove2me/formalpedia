-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.GramDeterminantPositive.exists_ortho_family
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:07.354732+00:00
-- url     : https://prove2.me/submissions/3055cf32-2507-42d4-abc5-76a8e283502b

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandG
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_GramDeterminantPositive_exists_ortho_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.GramDeterminantPositive
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLattices.Ext.L3.GramDeterminantPositive
theorem _root_.solution [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) :
    ∀ k : ℕ, k ≤ finrank K V →
      ∃ v : Fin k → V, (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧ ∀ i, v i ≠ 0 := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨v, ho, hne⟩ := ih (by omega)
    obtain ⟨x, hx0, hx⟩ := exists_ortho_ne_zero h v (by omega)
    refine ⟨Fin.snoc v x, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · intro hij; exact absurd rfl hij
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact hs.isRefl _ _ (hx j)
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact hx i
      · intro hij
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact ho i j (fun e => hij (by rw [e]))
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [Fin.snoc_last]; exact hx0
      · rw [Fin.snoc_castSucc]; exact hne i
end Formalism.HermitianLattices.Ext.L3.GramDeterminantPositive
