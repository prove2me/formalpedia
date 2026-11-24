-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.irreducible_of_galois_conditions
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:12.944439+00:00
-- url     : https://prove2.me/submissions/a4766e43-265d-4889-bf44-864e0b092d82

import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableOf
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_IrredOf
import Theorems.Thm_Formalism_GaloisIrreducibility_isSubSum_of_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Finset
namespace Formalism.GaloisIrreducibility
theorem _root_.solution : IrredOf := by
  intro hA K V P ι _ _ _ _ _ τ F q O I hFτ hO hroots hsub W hWτ hWF
  classical
  have hs1 : ∀ v, IsSubSum ((I v).val.map fun i => (O v i).card) (Module.finrank K W) := by
    intro v
    obtain ⟨J, hJ, hJeq⟩ := hA K V ι (τ v) (F v) (q v) (O v) (I v) (hFτ v) (hO v) (hroots v) ⊥ W
      bot_le (by simp) (by simp) (hWτ v) (hWF v)
    rw [finrank_bot, Nat.sub_zero] at hJeq
    rw [hJeq]
    exact isSubSum_of_subset _ _ _ hJ
  have hs2 : ∀ v, IsSubSum ((I v).val.map fun i => (O v i).card)
      (Module.finrank K V - Module.finrank K W) := by
    intro v
    obtain ⟨J, hJ, hJeq⟩ := hA K V ι (τ v) (F v) (q v) (O v) (I v) (hFτ v) (hO v) (hroots v) W ⊤
      le_top (hWτ v) (hWF v) (by simp) (by simp)
    rw [finrank_top] at hJeq
    rw [hJeq]
    exact isSubSum_of_subset _ _ _ hJ
  by_contra hne
  push_neg at hne
  obtain ⟨h0, h1⟩ := hne
  have hd0 : 0 < Module.finrank K W :=
    Nat.pos_of_ne_zero fun h => h0 (Submodule.finrank_eq_zero.mp h)
  have hdN : Module.finrank K W < Module.finrank K V :=
    Submodule.finrank_lt h1
  obtain ⟨v, hv⟩ := hsub (min (Module.finrank K W) (Module.finrank K V - Module.finrank K W))
    (by omega) (by omega)
  apply hv
  rcases min_choice (Module.finrank K W) (Module.finrank K V - Module.finrank K W) with h | h
  · rw [h]
    exact hs1 v
  · rw [h]
    exact hs2 v
end Formalism.GaloisIrreducibility
