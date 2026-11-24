-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantNormShapes.ent_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:28:37.53359+00:00
-- url     : https://prove2.me/submissions/f1ff4c7d-7f0b-41ca-a158-bf48804c311d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_EntOfMapEqZero
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
open NumberField Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {c : Type} [Fintype c] [DecidableEq c]
variable [Fact (IsFixF K F)]
namespace Formalism.L2.SG.Pf.discriminantNormShapes
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {k : ℕ} (hk : 1 ≤ k)
    {A : Matrix c c (𝓞 K)}
    (hA : ∀ i j, Ideal.Quotient.mk (extP K 𝔭 ^ k) (A i j) ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) :
    Ent (extP K 𝔭) A := fun i j => by
  obtain ⟨x, hx, hxe⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (hA i j)
  have h1 : A i j - x ∈ extP K 𝔭 ^ k := by
    rw [← Ideal.Quotient.eq]; exact hxe.symm
  have h2 : extP K 𝔭 ^ k ≤ extP K 𝔭 := by
    calc extP K 𝔭 ^ k ≤ extP K 𝔭 ^ 1 := Ideal.pow_le_pow_right hk
      _ = extP K 𝔭 := pow_one _
  have := (extP K 𝔭).add_mem (h2 h1) hx
  simpa using this
end Formalism.L2.SG.Pf.discriminantNormShapes
