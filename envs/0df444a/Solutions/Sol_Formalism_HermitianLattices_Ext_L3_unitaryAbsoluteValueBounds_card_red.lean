-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.card_red
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:55.15665+00:00
-- url     : https://prove2.me/submissions/6b31d146-4788-4001-a712-44c3ce500aea

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityField
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CntIOneOfNotMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_card_preimage
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_card_AQ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_finite_AQ


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
open NormLifting
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (j M : ℕ) (T : (Fin M → AQ K 𝔭 j) → Prop) :
    Nat.card {y : Fin M → AQ K 𝔭 (j + 1) //
        T fun i => Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ j)) (y i)} =
      Ideal.absNorm 𝔭 ^ (2 * M) * Nat.card {y // T y} := by
  have := finite_AQ (K := K) h𝔭 (j + 1)
  have := finite_AQ (K := K) h𝔭 j
  have hle : extP K 𝔭 ^ (j + 1) ≤ extP K 𝔭 ^ j := Ideal.pow_le_pow_right (Nat.le_succ j)
  let f : (Fin M → AQ K 𝔭 (j + 1)) →+ (Fin M → AQ K 𝔭 j) :=
    AddMonoidHom.compLeft (Ideal.Quotient.factor hle).toAddMonoidHom (Fin M)
  have hf : Function.Surjective f := by
    intro b
    choose a ha using fun i => Ideal.Quotient.factor_surjective hle (b i)
    exact ⟨a, funext ha⟩
  have hq : 0 < Ideal.absNorm 𝔭 :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 (idealPowerSpanBounds.ne_bot h𝔭))
  have hker : Nat.card f.ker = Ideal.absNorm 𝔭 ^ (2 * M) := by
    have h0 := HermitianSublattices.card_preimage f hf (fun _ => True)
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)),
      Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)), Nat.card_fun, Nat.card_fun,
      Nat.card_fin, card_AQ hK hF, card_AQ hK hF] at h0
    apply Nat.eq_of_mul_eq_mul_right (pow_pos (pow_pos hq (2 * j)) M)
    rw [← h0, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [← hker]
  exact HermitianSublattices.card_preimage f hf T
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
