-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanC.vF_lt_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:47:54.766282+00:00
-- url     : https://prove2.me/submissions/9a315fef-fb8d-405d-94b6-eabd0f9fac15

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
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
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.MeanC
namespace Formalism.HermitianLattices.Ext.L3.MeanC
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {n : 𝓞 F} {j : ℕ} (h : n ∉ 𝔭 ^ j) : vF 𝔭 n < j := by
  have hb : BddAbove {e : ℕ | n ∈ 𝔭 ^ e} := ⟨j, fun e he => by
    by_contra hlt
    push_neg at hlt
    exact h (Ideal.pow_le_pow_right hlt.le he)⟩
  have hne : ({e : ℕ | n ∈ 𝔭 ^ e}).Nonempty := ⟨0, by simp⟩
  have hm : n ∈ 𝔭 ^ sSup {e : ℕ | n ∈ 𝔭 ^ e} := Nat.sSup_mem hne hb
  unfold vF
  by_contra hle
  push_neg at hle
  exact h (Ideal.pow_le_pow_right hle hm)
end Formalism.HermitianLattices.Ext.L3.MeanC
