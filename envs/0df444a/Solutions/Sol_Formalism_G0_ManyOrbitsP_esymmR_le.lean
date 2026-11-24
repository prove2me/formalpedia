-- Prove2me | solution 1 for Formalism.G0.ManyOrbitsP.esymmR_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:08.574411+00:00
-- url     : https://prove2.me/submissions/ad48fd9b-d985-4865-a64b-3f66db834bb0

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
import Theorems.Thm_Formalism_G0_ManyOrbitsP_fact_esymm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.ManyOrbitsP
namespace Formalism.G0.ManyOrbitsP
theorem _root_.solution {V : ℕ} (κ : Fin V → ℝ) (hκ : ∀ v, 0 ≤ κ v) (m : ℝ) (hm : 0 ≤ m) (k : ℕ) :
    m ^ k * esymmR κ k ≤ (m * ∑ v, κ v) ^ k / k.factorial := by
  unfold esymmR
  have hnn : ∀ x ∈ Finset.univ.val.map κ, 0 ≤ x := by
    intro x hx
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hx
    exact hκ v
  have hE := fact_esymm_le (Finset.univ.val.map κ) hnn k
  rw [Finset.esymm_map_val] at hE
  have hsum : (Finset.univ.val.map κ).sum = ∑ v, κ v := rfl
  rw [hsum] at hE
  have hk : (0 : ℝ) < k.factorial := by positivity
  have hmk : 0 ≤ m ^ k := pow_nonneg hm k
  rw [le_div_iff₀ hk, mul_pow]
  have h2 := mul_le_mul_of_nonneg_left hE hmk
  calc m ^ k * (∑ B ∈ Finset.powersetCard k Finset.univ, ∏ v ∈ B, κ v) * (k.factorial : ℝ)
      = m ^ k * ((k.factorial : ℝ) * ∑ B ∈ Finset.powersetCard k Finset.univ, ∏ v ∈ B, κ v) := by ring
    _ ≤ m ^ k * (∑ v, κ v) ^ k := h2
end Formalism.G0.ManyOrbitsP
