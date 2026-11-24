-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.quotientLengthExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:28:55.851694+00:00
-- url     : https://prove2.me/submissions/e09c8ad7-2ae7-4684-a6f1-bf13924c1a38

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_LengthBaseChangeLocal
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_LengthBaseChangeAlt_ext_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module TensorProduct
open BQuot
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : QuotientLengthExt := by
  intro O K K₁ V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ n c N hN th hspan X e be hX hth a a' ha ha'
    hdet
  have h := LengthBaseChangeAlt.ext_core ϖ hϖ n c N hN th hspan X e be hX hth a a' ha hdet
  have hva : IsDiscreteValuationRing.addVal O a ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact ha
  have hva' : IsDiscreteValuationRing.addVal O a' ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact ha'
  have hd : 0 < finrank K K₁ := finrank_pos
  intro Tj
  change _ * ql X ((X ⊓ N.restrictScalars O) ⊔ Tj) + _ ≤ _ at h
  show ∃ m : ℕ, ql X ((X ⊓ N.restrictScalars O) ⊔ Tj) = m ∧ _
  generalize ql X ((X ⊓ N.restrictScalars O) ⊔ Tj) = q at h ⊢
  generalize IsDiscreteValuationRing.addVal O a = va at h hva ⊢
  generalize IsDiscreteValuationRing.addVal O a' = va' at h hva' ⊢
  generalize finrank K K₁ = d at h hd ⊢
  lift va to ℕ using hva
  lift va' to ℕ using hva'
  have hq : q ≠ ⊤ := by
    intro hq
    rw [hq, ENat.mul_top (by exact_mod_cast hd.ne'), top_add, top_le_iff] at h
    exact ENat.natCast_ne_top _ (by exact_mod_cast h)
  lift q to ℕ using hq
  refine ⟨q, rfl, ?_⟩
  have h' : d * q + va' ≤ va + d * n * be := by exact_mod_cast h
  simp only [ENat.toNat_natCast]
  have h'' : ((d * q + va' : ℕ) : ℤ) ≤ ((va + d * n * be : ℕ) : ℤ) := Int.ofNat_le.2 h'
  push_cast at h''
  linarith
end Formalism.LatticeBaseChangeAlt
