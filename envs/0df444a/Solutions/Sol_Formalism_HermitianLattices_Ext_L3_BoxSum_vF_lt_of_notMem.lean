-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.vF_lt_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:57:05.98628+00:00
-- url     : https://prove2.me/submissions/d1a2314d-65b5-4a01-ae5a-24ed6d537393

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumPeriodic
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_BoxInterEqEmpty
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeBotOfIsMaximal
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Filter Topology
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {n : 𝓞 F} {e : ℕ} (h : n ∉ 𝔭 ^ e) : vF 𝔭 n < e := by
  unfold vF
  have hne : ({e' : ℕ | n ∈ 𝔭 ^ e'} : Set ℕ).Nonempty := ⟨0, by simp⟩
  have hlt : ∀ k ∈ ({e' : ℕ | n ∈ 𝔭 ^ e'} : Set ℕ), k < e := by
    intro k hk
    by_contra hke
    push_neg at hke
    exact h (Ideal.pow_le_pow_right hke hk)
  have hbdd : BddAbove ({e' : ℕ | n ∈ 𝔭 ^ e'} : Set ℕ) := ⟨e, fun k hk => (hlt k hk).le⟩
  exact hlt _ (Nat.sSup_mem hne hbdd)
end Formalism.HermitianLattices.Ext.L3.BoxSum
