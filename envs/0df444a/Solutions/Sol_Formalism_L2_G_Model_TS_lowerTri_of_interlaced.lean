-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.lowerTri_of_interlaced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:00:51.220231+00:00
-- url     : https://prove2.me/submissions/99350ae1-8201-449d-81a1-ead05623686d

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCassemLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_LowerTriangularOverField
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
open scoped MonomialOrder
namespace Formalism.L2.G.Model.TS
theorem _root_.solution {r n : ℕ} {m : Fin r × Fin n →₀ ℕ} (h : Interlaced m) : LowerTri m := by
  suffices key : ∀ (k : ℕ) (s : Fin n), s.val = k → ∀ a : Fin r, a.val < s.val → m (a, s) = 0 from
    fun a s has => key s.val s rfl a has
  intro k
  induction k with
  | zero =>
    intro s hs a ha
    omega
  | succ k ih =>
    intro s hs a ha
    have hk : k < n := by have := s.isLt; omega
    have h1 := h ⟨k, hk⟩ s (by simpa using hs) a
    have h2 : (∑ b : Fin r with b < a, m (b, (⟨k, hk⟩ : Fin n))) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hba : b < a := (Finset.mem_filter.mp hb).2
      have hba' : b.val < a.val := hba
      exact ih ⟨k, hk⟩ rfl b (by show b.val < k; omega)
    rw [h2, zero_add] at h1
    have h3 : m (a, s) ≤ ∑ b : Fin r with b ≤ a, m (b, s) :=
      Finset.single_le_sum (f := fun b => m (b, s)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ a, le_rfl⟩)
    omega
end Formalism.L2.G.Model.TS
